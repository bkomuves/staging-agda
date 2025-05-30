
{-# OPTIONS --type-in-type #-}
module Meta.Val where

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool
open import Data.Word64
open import Data.String
open import Data.List
open import Data.Vec

open import Meta.Ty 
open import Meta.HList

--------------------------------------------------------------------------------

private variable
  s t : Ty
  n m : ℕ
  ts  : Vec Ty m
  nam : String

{-# NO_POSITIVITY_CHECK #-}
data Val : Ty -> Set where
  Tt      :                     Val Unit
  BitV    : Bool             -> Val Bit
  U64V    : Word64           -> Val U64
  NatV    : ℕ                -> Val Nat
  StructV : HList Val ts     -> Val (Struct ts)
  WrapV   : Val t            -> Val (Named nam t)
  FunV    : (Val s -> Val t) -> Val (s ⇒ t)
  -- ArrayV  : Vec (Val t) n    -> Val (Array n t)

--------------------------------------------------------------------------------

valApp : Val (s ⇒ t) -> Val s -> Val t
valApp (FunV f) x = f x

valVec : Vec (Val t) n -> Val (Meta.Ty.Vect n t)
valVec v = StructV (vecToHList Val v) 

--------------------------------------------------------------------------------
