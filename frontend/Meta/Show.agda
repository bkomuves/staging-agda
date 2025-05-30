
module Meta.Show where

--------------------------------------------------------------------------------

open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Vec  using ( Vec  ; [] ; _∷_ )
open import Data.List using ( List ; [] ; _∷_ )
open import Data.Bool

open import Data.Word64
open import Data.Word64.Show

--------------------------------------------------------------------------------

showParen : Bool -> String -> String
showParen false s = s
showParen true  s = "(" ++ s ++ ")"

quoteString : String -> String
quoteString s = q ++ s ++ q where
  q : String
  q = Data.String.fromChar '\"'

infix 4 _>ᵇ_
_>ᵇ_ : (m n : ℕ) → Bool
_>ᵇ_ x y = _<ᵇ_ y x

appPrec : ℕ
appPrec = 10

appPrec₊₁ : ℕ
appPrec₊₁ = suc appPrec

--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Nat.Show
open import Data.Nat.Show as ℕ
open import Data.Digit using ( toNatDigits )
open import Data.Char as Char
open import Function.Base using ( _$_ ; _∘′_ )

toHexDigitChar : ℕ → Char
toHexDigitChar n = if n <ᵇ 10
  then Char.fromℕ (n      + Char.toℕ '0')
  else Char.fromℕ (n ∸ 10 + Char.toℕ 'a')

toHexadecimalChars : ℕ → List Char
toHexadecimalChars = Data.List.map toHexDigitChar ∘′ toNatDigits 16

myShowHexa : Word64 -> String
myShowHexa w 
  = "0x" ++_
  $ padLeft '0' 16
  $ Data.String.fromList  
  $ toHexadecimalChars (Data.Word64.toℕ w)

exh : String
exh = myShowHexa (Data.Word64.fromℕ 0xdeadcafe12345)

--------------------------------------------------------------------------------

showBool : Bool -> String
showBool true  = "true"
showBool false = "false"

showBoolHs : Bool -> String
showBoolHs true  = "True"
showBoolHs false = "False"

showNat : ℕ -> String
showNat n = Data.Nat.Show.show n

-- WARNING: no escaping support
showString : String -> String
showString = quoteString

showWord64 : Word64 -> String
showWord64 = myShowHexa

showVec : {A : Set} -> (A -> String) -> {n : ℕ} -> Vec A n -> String
showVec {A} f [] = "[]"
showVec {A} f ys = "[ " ++ go ys where
  go : {n : ℕ} -> Vec A n -> String
  go []       = " ]"
  go (x ∷ []) = f x ++ " ]"
  go (x ∷ xs) = f x ++ ", " ++ go xs

showList : {A : Set} -> (A -> String) -> List A -> String
showList {A} f [] = "[]"
showList {A} f ys = "[ " ++ go ys where
  go : List A -> String
  go []       = " ]"
  go (x ∷ []) = f x ++ " ]"
  go (x ∷ xs) = f x ++ ", " ++ go xs

--------------------------------------------------------------------------------

{-
ex : String
ex = showVec showNat (1 ∷ 2 ∷ 3 ∷ 40000000001111111122222222 ∷ [])
-}
