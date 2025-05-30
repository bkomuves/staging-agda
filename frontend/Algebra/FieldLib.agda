
module Algebra.FieldLib where

---------------------------------------------------------------------------------

open import Data.Nat

---------------------------------------------------------------------------------

data Curve : Set where
  BN254     : Curve
  BLS12-381 : Curve

data SmallField : Set where
  Goldilocks : SmallField
  Mersenne31 : SmallField
  BabyBear   : SmallField
  
data BigField : Set where
  ScalarField : Curve -> BigField
  BaseField   : Curve -> BigField

---------------------------------------------------------------------------------

smallFieldPrime : SmallField -> ℕ
smallFieldPrime Goldilocks = 0xffffffff00000001     -- 2^64 - 2^32 + 1
smallFieldPrime BabyBear   = 0x78000001             -- 2^31 - 2^27 + 1
smallFieldPrime Mersenne31 = 0x7fffffff             -- 2^31 - 1

---------------------------------------------------------------------------------

bigFieldPrime : BigField -> ℕ
bigFieldPrime (BaseField   BN254    ) = 21888242871839275222246405745257275088696311157297823662689037894645226208583
bigFieldPrime (ScalarField BN254    ) = 21888242871839275222246405745257275088548364400416034343698204186575808495617
bigFieldPrime (BaseField   BLS12-381) = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
bigFieldPrime (ScalarField BLS12-381) = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

---------------------------------------------------------------------------------
