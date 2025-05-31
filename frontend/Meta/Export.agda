{-# OPTIONS --type-in-type #-}

module Meta.Export where

--------------------------------------------------------------------------------

open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat  using ( ℕ ; zero ; suc  )
open import Data.Fin  using ( Fin ; fromℕ ; opposite ; cast ; toℕ )
open import Data.Vec  using ( Vec ; _∷_ ; [] ; lookup )
open import Data.List using ( List ; _∷_ ; [] )
open import Data.Product using ( _×_ ; _,_ )
open import Data.String using ( String ; _++_ )
open import Data.Word64
open import Data.Maybe

open import Meta.Ty
open import Meta.Ctx
open import Meta.PrimOp
open import Meta.HList
open import Meta.Show

import Meta.Val     as TVal
import Meta.STLC    as STLC
import Meta.HOAS    as HOAS
import Meta.Convert as Conv

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n   : ℕ
  ctx : Ctx n

{-
-- well-typed lambda calculus
data LC : Ctx n -> (ty : Ty) -> Set where
  Lam : LC (s ∷ ctx) t -> LC ctx (s ⇒ t)
  Let : LC ctx s -> LC (s ∷ ctx) t -> LC ctx t
  App : LC ctx (s ⇒ t) -> LC ctx s -> LC ctx t
  Fix : LC ctx ((s ⇒ s) ⇒ (s ⇒ s)) -> LC ctx (s ⇒ s)
  Pri : PrimOp (LC ctx) t -> LC ctx t
  Lit : Val t -> LC ctx t
  Var : (j : Fin n) -> LC {n} ctx (lkpCtx ctx j)
-}

--------------------------------------------------------------------------------

data RVal : Set where
  Tt      :                   RVal
  BitV    : Bool           -> RVal
  U64V    : Word64         -> RVal
  NatV    : ℕ              -> RVal
  StructV : List RVal      -> RVal
  WrapV   : String -> RVal -> RVal

valForget : TVal.Val t -> RVal
valForget = go where

  {-# NON_COVERING #-}
  go : {ty : Ty} -> TVal.Val ty -> RVal
  goList : {ts : Vec Ty n} -> HList TVal.Val ts -> List RVal

  go TVal.Tt           = Tt
  go (TVal.BitV b)     = BitV b
  go (TVal.U64V u)     = U64V u
  go (TVal.NatV n)     = NatV n
  go (TVal.StructV xs) = StructV (goList xs)
  go (TVal.WrapV {t} {nam} v)  = WrapV nam (go v)
  -- go (TVal.Fun fun)   = {!!}
  -- go (TVal.ArrayV xs)  = {!!}

  goList Nil = []
  goList (Cons x xs) = go x ∷ goList xs

{-# TERMINATING #-}
showRValPrec : ℕ -> RVal -> String
showRValPrec = go where

  go : ℕ -> RVal -> String
  go d Tt          = "Tt"
  go d (BitV b)     = showParen (d >ᵇ appPrec) ("BitV " ++ showBoolHs b)
  go d (U64V w    ) = showParen (d >ᵇ appPrec) ("U64V " ++ showWord64 w)
  go d (NatV n    ) = showParen (d >ᵇ appPrec) ("NatV " ++ showNat    n)
  go d (StructV xs) = showParen (d >ᵇ appPrec) ("StructV " ++ showList (go 0) xs)
  go d (WrapV n v)  = showParen (d >ᵇ appPrec) ("WrapV " ++ showString n ++ " " ++ go appPrec₊₁ v)
  
showRVal : RVal -> String
showRVal = showRValPrec 0

--------------------------------------------------------------------------------

data Raw : Set where
  Lam : Ty -> Raw -> Raw
  Let : Ty -> Raw -> Raw -> Raw
  App : Raw -> Raw -> Raw
  Fix : Raw -> Raw
  Pri : RawPrim -> List Raw -> Raw
  Lit : RVal -> Raw
  Var : (j : ℕ) -> Raw
  Log : String -> Raw -> Raw
  
{-# TERMINATING #-}
convertToRaw : STLC.LC ctx t -> Raw
convertToRaw = go where

  go : {n : ℕ} -> {ctx : Ctx n} -> {ty : Ty} -> STLC.LC ctx ty -> Raw
  go (STLC.Lam           {s} body    )   = Lam s (go body)
  go (STLC.Let {n} {ctx} {s} rhs body)   = Let s (go rhs) (go body)
  go (STLC.App               fun arg )   = App (go fun) (go arg)
  go (STLC.Var               j   _   )   = Var (Data.Fin.toℕ j)
  go (STLC.Lit               val     )   = Lit (valForget val)
  go (STLC.Pri               pri     )   = let raw , list = primOpForget go pri in Pri raw list
  go (STLC.Fix               rec     )   = Fix (go rec)
  go (STLC.Log               nam body)   = Log nam (go body)
  
--------------------------------------------------------------------------------

{-# TERMINATING #-}
showRawPrec : ℕ -> Raw -> String
showRawPrec = go where

  go : ℕ -> Raw -> String
  go d (Lam ty body    ) = showParen (d >ᵇ appPrec) ("Lam " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ body)
  go d (Let ty rhs body) = showParen (d >ᵇ appPrec) ("Let " ++ showTyPrec appPrec₊₁ ty ++ " " ++ go appPrec₊₁ rhs ++ " " ++ go appPrec₊₁ body)
  go d (App fun arg)     = showParen (d >ᵇ appPrec) ("App " ++ go appPrec₊₁ fun ++ " " ++ go appPrec₊₁ arg)
  go d (Lit val)         = showParen (d >ᵇ appPrec) ("Lit " ++ showRValPrec appPrec₊₁ val)
  go d (Var j)           = showParen (d >ᵇ appPrec) ("Var " ++ showNat j)
  go d (Pri raw args)    = showParen (d >ᵇ appPrec) ("Pri " ++ showRawPrimPrec appPrec₊₁ raw ++ " " ++ showList (go 0) args)
  go d (Fix rec)         = showParen (d >ᵇ appPrec) ("Fix " ++ go appPrec₊₁ rec)
  go d (Log name body)   = showParen (d >ᵇ appPrec) ("Log " ++ showString name ++ " " ++ go appPrec₊₁ body)

showRaw : Raw -> String
showRaw = showRawPrec 0 

--------------------------------------------------------------------------------

exportToStringMaybe : {ty : Ty} -> HOAS.Tm ty -> Maybe String
exportToStringMaybe tm = do
  lc <- Conv.convert tm
  let raw = convertToRaw lc
  just (showRaw raw)

{-# NON_COVERING #-}
exportToString : {ty : Ty} -> HOAS.Tm ty -> String
exportToString tm with exportToStringMaybe tm
exportToString _ | (just str) = str

--------------------------------------------------------------------------------
