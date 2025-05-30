
module Examples.Simple where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Meta.Object
open import Algebra.FieldLib
open import Algebra.Limbs
open import Algebra.Prime

--------------------------------------------------------------------------------

-- *** BIGINT ***

open import Algebra.BigInt using ( BigInt )

halfP+1 : Tm (BigInt 4)
halfP+1 = bigIntFromℕ 10944121435919637611123202872628637544274182200208017171849102093287904247809

big1 : Tm (BigInt 4)
big1 = bigIntFromℕ 12535032671501493392438659292886563663979619812816639413586309554197071221275

big2 : Tm (BigInt 4)
big2 = bigIntFromℕ 20670156704232560809430694243501641649572216251781105022963497476851362916519

big3 : Tm (BigInt 4)
big3 = bigIntFromℕ 10734482926936635597888852654981536388697257091861152194513442686302125663795

small1 : Tm (BigInt 2)
small1 = bigIntFromℕ 298219370995091515800384725779828479220

small2 : Tm (BigInt 2)
small2 = bigIntFromℕ 45210828018843085130265813626022701902

verySmall : Tm (BigInt 1)
verySmall = bigIntFromℕ 45210828018843

exBig0 : Tm (BigInt _)
exBig0 = snd (Algebra.BigInt.add big1 big2)

exBig1 : Tm Bit
exBig1 = Algebra.BigInt.isGE big2 big1 

exSmall2 : Tm Bit
exSmall2 = Algebra.BigInt.isGE small1 small2 

--------------------------------------------------------------------------------
-- *** FIELD PRIME ***

thePrime-ℕ : ℕ
thePrime-ℕ = bigFieldPrime (ScalarField BN254)

thePrime : Prime
thePrime = mkPrime thePrime-ℕ

--------------------------------------------------------------------------------
-- *** MODULAR ***

import Algebra.Modular as Modular

open module ModuloP = Modular thePrime 

mod1 : Tm Mod
mod1 = wrap big1

mod2 : Tm Mod
mod2 = wrap big2

mod3 : Tm Mod
mod3 = wrap big3

exMod1 : Tm Mod
exMod1 = ModuloP.add mod1 mod2

exMod2 : Tm Mod
exMod2 = ModuloP.sub mod1 mod2

--------------------------------------------------------------------------------
-- *** MONTGOMERY ***

import Algebra.Montgomery.Impl as Montgomery

open module MontP = Montgomery thePrime

mont1 : Tm Mont
mont1 = wrap big1

mont2 : Tm Mont
mont2 = wrap big2

mont3 : Tm Mont
mont3 = wrap big3

exMont1 : Tm Mont
exMont1 = MontP.mul mont1 mont2

exMont2 : Tm (BigInt 4)
exMont2 = runGen do
  x <- gen (MontP.unsafeFromBigInt big1)
  y <- gen (MontP.unsafeFromBigInt big2)
  z <- gen (MontP.unsafeFromBigInt big3)
  tmp₁ <- gen (MontP.mul x y)
  tmp₂ <- gen (MontP.add tmp₁ z)
  tmp₃ <- gen (MontP.toBigInt tmp₂)
  Meta.Object.return tmp₃
   
--------------------------------------------------------------------------------
-- *** NAT and RECURSION ***

open NatLib

import Examples.Tests as Tests

natEx1 : Tm Nat
natEx1 = Tests.natFixPow 7 (kstNat 2)

natEx2 : Tm Nat
natEx2 = Tests.natDynPowNaive (kstNat 8) (kstNat 2) 

lamEx0 : Tm Nat
lamEx0 = App Tests.squarePlus7 (kstNat 10)

lamEx1 : Tm (Pair Nat Nat)
lamEx1 = Tests.lamTest2

lamEx2a : Tm Nat
lamEx2a = Tests.lamTest3

lamEx2 : Tm (Pair Nat Nat)
lamEx2 = Tests.lambdaLiftTest

mixedLam1 : Tm (Pair U64 Nat)
mixedLam1 = Tests.mixedTest1

--------------------------------------------------------------------------------
