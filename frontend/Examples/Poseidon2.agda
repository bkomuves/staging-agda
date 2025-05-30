
module Examples.Poseidon2 where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Fin renaming ( zero to fzero ; suc to fsuc ) 
open import Data.Vec

open import Relation.Binary.PropositionalEquality

open import Meta.Object

open import Algebra.BigInt using ( BigInt )
open import Algebra.Limbs

open import Algebra.Prime
open import Algebra.FieldLib
open import Algebra.Montgomery.Instance

open import Examples.Poseidon2.RoundConst

--------------------------------------------------------------------------------

private 

  f0 : Fin 3
  f0 = fzero

  f1 : Fin 3
  f1 = fsuc fzero

  f2 : Fin 3
  f2 = fsuc (fsuc fzero)

--------------------------------------------------------------------------------

theFieldPrime : Prime
theFieldPrime = mkPrime (bigFieldPrime (ScalarField BN254))

State : Ty -> Ty
State ty = Vect 3 ty

variable
  s t : Ty

private 

  withState : Tm (State s) -> (Tm s -> Tm s -> Tm s -> Gen (Tm t)) -> Gen (Tm t)
  withState triple action = do
    var <- gen triple
    action
      (proj f0 var)
      (proj f1 var)
      (proj f2 var)
    
  mkState : Tm t -> Tm t -> Tm t -> Tm (State t)
  mkState x y z = mkVect (x ∷ y ∷ z ∷ [])
  
Output : Ty
Output = State (BigInt 4)

--------------------------------------------------------------------------------

record PoseidonAPI : Set where
  field
    Big       : Ty
    Mont      : Ty
    PermState : Ty -> Ty
    ingress   : Tm (State Big ) -> Tm (State Mont)
    egress    : Tm (State Mont) -> Tm (State Big ) 
    perm      : Tm (State Mont) -> Tm (State Mont)
    digest    : Tm (State Mont) -> Tm Big

--------------------------------------------------------------------------------

withPoseidon'
  :  {ty : Ty} -> MontgomeryAPI theFieldPrime
  -> ((api : PoseidonAPI) -> (PoseidonAPI.Big api ≡ BigInt 4) -> Tm ty)
  -> Tm ty
withPoseidon' {ty} montAPI kont = runGen final where

  open MontgomeryAPI montAPI

  PermFun : Set
  PermFun = Tm (State Mont ⇒ State Mont)

  SBoxFun : Set
  SBoxFun = Tm (Mont ⇒ Mont)

  Big4 : Ty
  Big4 = BigInt 4
  
  {-# NON_COVERING #-}
  eq4 : #limbs ≡ 4
  eq4 with #limbs
  eq4 | 4 = refl
  
  final : Gen (Tm ty)
  final = do
  
    let ingressFun : Tm (State Big4 ⇒ State Mont)
        ingressFun = Lam \inp -> runGen do
          withState inp \x y z -> return (mkState
            (importMont eq4 x)
            (importMont eq4 y)
            (importMont eq4 z))

    let egressFun : Tm (State Mont ⇒ State Big4)
        egressFun = Lam \inp -> runGen do
          withState inp \x y z -> return (mkState
            (exportMont eq4 x)
            (exportMont eq4 y)
            (exportMont eq4 z))

    let digestFun : Tm (State Mont ⇒ Big4)
        digestFun = Lam \inp -> runGen do
          withState inp \x y z -> return (exportMont eq4 x)

    ingressVar <- gen ingressFun
    egressVar  <- gen egressFun
    digestVar  <- gen digestFun

    -- the function x ↦ x⁵
    let sboxTm : Tm Mont -> Tm Mont
        sboxTm input = runGen do
          x1 <- gen input
          x2 <- gen (sqr x1)
          x4 <- gen (sqr x2)
          x5 <- gen (mul x1 x4)
          return x5

    sboxFun <- gen (Log "sboxλ" (Lam sboxTm))
    let sbox x = App (Log "sbox" sboxFun) x
 
    let add3 : Tm Mont -> Tm Mont -> Tm Mont -> Tm Mont
        add3 x y z = add (add x y) z

    let triple : Tm Mont -> Tm Mont
        triple x = add (dbl x) x

    let linearLayer : Tm (State Mont) -> Gen (Tm (State Mont))
        linearLayer state = withState state \x y z -> do
          s <- gen (add3 x y z)
          return (mkState (add s x) (add s y) (add s z))

    let internalRound : Tm (State Mont) -> ℕ -> Gen (Tm (State Mont))
        internalRound state rc = withState state \x y z -> do
          let c = montFromℕ rc
          x' <- gen (sbox (add x c))
          s  <- gen (add3 x' y z)
          z2 <- gen (dbl z)
          return (mkState (add s x') (add s y) (add s z2))

    let externalRound : Tm (State Mont) -> Vec ℕ 3 -> Gen (Tm (State Mont))
        externalRound state rcs = withState state \x y z -> do
          let cx = montFromℕ (lookup rcs f0)
          let cy = montFromℕ (lookup rcs f1)
          let cz = montFromℕ (lookup rcs f2)
          x' <- gen (sbox (add x cx))
          y' <- gen (sbox (add y cy))
          z' <- gen (sbox (add z cz))
          s  <- gen (add3 x' y' z')
          return (mkState (add s x') (add s y') (add s z'))

    let permTm : Tm (State Mont) -> Tm (State Mont)
        permTm input = runGen do
          tmp  <- linearLayer input
          tmp′ <- vecFoldM externalRound tmp  (Data.Vec.map (lookup initialRoundConstsℕ ) (allFin  4))
          tmp″ <- vecFoldM internalRound tmp′ (Data.Vec.map (lookup internalRoundConstsℕ) (allFin 56))
          tmp‴ <- vecFoldM externalRound tmp″ (Data.Vec.map (lookup finalRoundConstsℕ   ) (allFin  4))
          return tmp‴

    permVar <- gen (Lam permTm)

    let api : PoseidonAPI
        api = record
          { Big       = BigInt 4
          ; Mont      = Mont
          ; PermState = State
          ; ingress   = App (Log "ingress" ingressVar)
          ; egress    = App (Log "egress"  egressVar )
          ; perm      = App (Log "perm"    permVar   )
          ; digest    = App (Log "digest"  digestVar )
          }

    return (kont api refl)

----------------------------------------

withPoseidon :  {ty : Ty} -> ((api : PoseidonAPI) -> (PoseidonAPI.Big api ≡ BigInt 4) -> Tm ty) -> Tm ty
withPoseidon kont = withMontgomery theFieldPrime \montAPI -> withPoseidon' montAPI kont

--------------------------------------------------------------------------------

myApplication' : (api : PoseidonAPI) -> (PoseidonAPI.Big api ≡ BigInt 4) -> Tm Output 
myApplication' api refl = program where

  open PoseidonAPI api
  
  iniState : Tm (State (BigInt 4))
  iniState = mkState (bigIntFromℕ {4} 0) (bigIntFromℕ {4} 1) (bigIntFromℕ {4} 2)

  iniState′ : Tm (State Mont)
  iniState′ = ingress iniState

{-
  {-# NON_COVERING #-}
  eq4 : #limbs ≡ 4
  eq4 with #limbs
  eq4 | 4 = refl
  
  extractResult : Tm (State Mont) -> Tm Output
  extractResult triple = mkVect
    ( exportMont eq4 (proj f0 triple)
    ∷ exportMont eq4 (proj f1 triple)
    ∷ exportMont eq4 (proj f2 triple)
    ∷ [])
-}

  program = runGen do
    let res = perm iniState′
    return (egress res)

myApplication : Tm Output
myApplication = withPoseidon myApplication'

--------------------------------------------------------------------------------
