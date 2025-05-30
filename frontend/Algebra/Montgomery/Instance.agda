
{-

As the unrolled functions starts to get big, we don't want to inline them all the time.
Instead, we want to make them functions using Let and just call those at the use sites.

This module helps by giving you an API to conveniently do just that.

-}

module Algebra.Montgomery.Instance where

--------------------------------------------------------------------------------

open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Meta.Object

open import Algebra.BigInt using ( BigInt )
open import Algebra.Limbs
open import Algebra.Prime

--------------------------------------------------------------------------------

record MontgomeryAPI (p : Prime) : Set where
  field
    #limbs : ℕ
    Big    : Ty
    Mont   : Ty
    montFromℕ     : ℕ -> Tm Mont 
    unsafeFromBig : Tm Big  -> Tm Mont
    toBig         : Tm Mont -> Tm Big 
    importMont    : {l : ℕ} -> #limbs ≡ l -> Tm (BigInt l) -> Tm Mont
    exportMont    : {l : ℕ} -> #limbs ≡ l -> Tm Mont -> Tm (BigInt l)
    neg    : Tm Mont -> Tm Mont
    dbl    : Tm Mont -> Tm Mont
    add    : Tm Mont -> Tm Mont -> Tm Mont
    sub    : Tm Mont -> Tm Mont -> Tm Mont
    sqr    : Tm Mont -> Tm Mont
    mul    : Tm Mont -> Tm Mont -> Tm Mont

--------------------------------------------------------------------------------

import Algebra.Montgomery.Impl 

withMontgomery : {ty : Ty} -> (prime : Prime) -> (MontgomeryAPI prime -> Tm ty) -> Tm ty
withMontgomery prime kont = final where

  open module MontP = Algebra.Montgomery.Impl prime

  montFromℕ' : ℕ -> Tm MontP.Mont
  montFromℕ' n = MontP.unsafeFromBigInt (bigIntFromℕ n)

  toBigFun         = Lam MontP.toBigInt
  unsafeFromBigFun = Lam MontP.unsafeFromBigInt

  negFun : Tm (Mont ⇒ Mont)
  dblFun : Tm (Mont ⇒ Mont)
  addFun : Tm (Mont ⇒ Mont ⇒ Mont)
  subFun : Tm (Mont ⇒ Mont ⇒ Mont)
  sqrFun : Tm (Mont ⇒ Mont)
  mulFun : Tm (Mont ⇒ Mont ⇒ Mont)

  negFun  = Lam  MontP.neg    
  dblFun  = Lam  MontP.double
  addFun  = Lam2 MontP.add
  subFun  = Lam2 MontP.sub
  sqrFun  = Lam  MontP.square
  mulFun  = Lam2 MontP.mul

  exportBig : {l : ℕ} -> MontP.#limbs ≡ l -> Tm Big -> Tm (BigInt l)
  exportBig refl tm = tm

  importBig : {l : ℕ} -> MontP.#limbs ≡ l -> Tm (BigInt l) -> Tm Big 
  importBig refl tm = tm

  final = 
    Let (Log "toBigλ"   toBigFun        ) \toBigVar         ->
    Let (Log "fromBigλ" unsafeFromBigFun) \unsafeFromBigVar ->
    Let (Log "negλ" negFun)        \negVar ->
    Let (Log "dblλ" dblFun)        \dblVar ->
    Let (Log "addλ" addFun)        \addVar ->
    Let (Log "subλ" subFun)        \subVar ->
    Let (Log "sqrλ" sqrFun)        \sqrVar ->
    Let (Log "mulλ" mulFun)        \mulVar ->
      let api = record
            { #limbs = MontP.#limbs
            ; Big    = MontP.Big
            ; Mont   = MontP.Mont
            ; montFromℕ     = montFromℕ'
            ; toBig         = App toBigVar
            ; unsafeFromBig = App unsafeFromBigVar
            ; importMont    = \eq tm -> App (Log "fromBig" unsafeFromBigVar) (importBig eq tm)
            ; exportMont    = \eq tm -> exportBig eq (App (Log "toBig" toBigVar) tm)
            ; neg    = App  (Log "neg" negVar)
            ; dbl    = App  (Log "dbl" dblVar)
            ; add    = App2 (Log "add" addVar)
            ; sub    = App2 (Log "sub" subVar)
            ; sqr    = App  (Log "sqr" sqrVar)
            ; mul    = App2 (Log "mul" mulVar)
            }
      in kont api

--------------------------------------------------------------------------------
