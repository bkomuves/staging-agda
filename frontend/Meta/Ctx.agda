
{-# OPTIONS --type-in-type #-}
module Meta.Ctx where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Vec
open import Data.String using ( String ; _++_ )
open import Data.Fin using ( Fin ; zero ; suc ;  opposite ; inject₁ )
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Meta.Ty

--------------------------------------------------------------------------------

private variable
  n : ℕ

Ctx : ℕ -> Set
Ctx n = Vec Ty n

-- note: we use de Bruijn *levels* for indexing,
-- so we have to use `Fin.opposite` for lookup up!
--
lkpCtx : Ctx n -> Fin n -> Ty
lkpCtx ctx j = Data.Vec.lookup ctx (Data.Fin.opposite j)

lkpCtx₁ : (s : Ty) -> Ctx n -> Fin n -> Ty
lkpCtx₁ s ctx j = lkpCtx (s ∷ ctx) (inject₁ j)

--------------------------------------------------------------------------------

lookup-sub₂ : (ctx : Ctx n) -> {j₁ j₂ : Fin n} -> (j₁ ≡ j₂) -> lookup ctx j₁ ≡ lookup ctx j₂
lookup-sub₂ ctx refl = refl

--------------------------------------------------------------------------------

natToFin : (n : ℕ) -> (k : ℕ) -> Maybe (Fin n)
natToFin zero     _        = nothing
natToFin (suc n₁) zero     = just zero
natToFin (suc n₁) (suc k₁) with natToFin n₁ k₁
natToFin _        _        | nothing  = nothing
natToFin _        _        | just f₁  = just (suc f₁)

{-
lkpCtxNat : {n : ℕ} -> Ctx n -> (k : ℕ) -> Maybe Ty
lkpCtxNat {n} ctx k with natToFin n k
lkpCtxNat {n} ctx k | nothing = nothing
lkpCtxNat {n} ctx k | just f  = just (lkpCtx ctx f)
-}

data InCtx {n : ℕ} (ctx : Ctx n) : Set where
  MkInCtx : (j : Fin n) -> (ty : Ty) -> lkpCtx ctx j ≡ ty -> InCtx ctx

lkpInCtx : (ctx : Ctx n) -> Fin n -> InCtx ctx
lkpInCtx ctx j = MkInCtx j (lkpCtx ctx j) refl

lkpCtxNatWithProof  : {n : ℕ} -> (ctx : Ctx n) -> (k : ℕ) -> Maybe (InCtx ctx)
lkpCtxNatWithProof {n} ctx k with natToFin n k
lkpCtxNatWithProof {n} ctx k | nothing = nothing
lkpCtxNatWithProof {n} ctx k | just f  = just (lkpInCtx ctx f)

--------------------------------------------------------------------------------

{-
fact-lookup-suc : {A : Set} -> {n : ℕ} -> {x : A} -> {xs : Vec A n} -> (j : Fin n) -> Data.Vec.lookup (x ∷ xs) (suc j) ≡ Data.Vec.lookup xs j
fact-lookup-suc j = refl

thm-opposite-inject₁ : {n : ℕ} -> (j : Fin n) -> opposite (inject₁ j) ≡ Data.Fin.suc (opposite j)
thm-opposite-inject₁ {n} zero    = refl
thm-opposite-inject₁ {n} (suc j) = let eq = thm-opposite-inject₁ j in cong inject₁ eq

thm-lkp-extended-ctx : {n : ℕ} -> {ctx : Ctx n} -> (s : Ty) -> (j : Fin n) -> lkpCtx ctx j ≡ lkpCtx (s ∷ ctx) (inject₁ j)
thm-lkp-extended-ctx {n} {ctx} s j = sym (trans eq₂ fact) where

  fact : Data.Vec.lookup (s ∷ ctx) (suc (opposite j)) ≡ Data.Vec.lookup ctx (opposite j) 
  fact = fact-lookup-suc {Ty} {n} {s} {ctx} (opposite j)

  eq₁ : opposite (inject₁ j) ≡ suc (opposite j)
  eq₁ = thm-opposite-inject₁ j

  eq₂ : Data.Vec.lookup (s ∷ ctx) (opposite (inject₁ j)) ≡ Data.Vec.lookup (s ∷ ctx) (suc (opposite j))
  eq₂ = cong (Data.Vec.lookup (s ∷ ctx)) eq₁
-}

--------------------------------------------------------------------------------

 
