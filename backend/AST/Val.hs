
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving, PatternSynonyms #-}
module AST.Val where

--------------------------------------------------------------------------------

import Data.Word
import Text.Read

import Data.Sequence ( Seq , empty )

import Control.Monad.Identity

import AST.Ty

--------------------------------------------------------------------------------

 -- used only for the evaluator
data Function m
  = MkFun (Val' m -> m (Val' m))

instance Eq   (Function m) where (==)     = error "Function/Eq"
instance Show (Function m) where show     = error "Function/Show"
instance Read (Function m) where readPrec = error "Function/Read"

runFunction :: Function Identity -> Val -> Val
runFunction (MkFun f) x = runIdentity (f x)

--------------------------------------------------------------------------------

data Val' m where
  TtV     ::                     Val' m
  BitV    :: Bool             -> Val' m
  U64V    :: Word64           -> Val' m
  NatV    :: Integer          -> Val' m
  StructV :: [Val' m]         -> Val' m
  WrapV   :: String -> Val' m -> Val' m
  FunV    :: Function m       -> Val' m      -- ^ used only for the evaluator

type Val = Val' Identity

castVal :: Val' m1 -> Val' m2
castVal = go where
  go :: Val' m1 -> Val' m2
  go value = case value of
    TtV        -> TtV     
    BitV    b  -> BitV b    
    U64V    x  -> U64V x   
    NatV    n  -> NatV n   
    StructV xs -> StructV (map go xs) 
    WrapV n y  -> WrapV n (go y)
    FunV {}    -> error "castVal: FunV"

pattern PairV x y = StructV [x,y]

deriving instance Eq   (Val' m)
deriving instance Show (Val' m)
deriving instance Read (Val' m)

isAtomicValue :: Val' m -> Bool
isAtomicValue value = case value of
  TtV         -> True
  BitV {}     -> True
  U64V {}     -> True
  NatV {}     -> True
  StructV _   -> False
  WrapV   _ x -> isAtomicValue x
  FunV {}     -> error "isAtomicValue: called on function"

mbAtomicValue :: Val' m -> Maybe (Val' m)
mbAtomicValue value = if isAtomicValue value 
  then Just value
  else Nothing
  
--------------------------------------------------------------------------------

type Env' m = Seq (Val' m)

type Env = Env' Identity

emptyEnv :: Env' m 
emptyEnv = Data.Sequence.empty

--------------------------------------------------------------------------------

valTy :: Val' m -> Ty
valTy val = case val of
  TtV         -> Unit
  BitV _      -> Bit
  U64V _      -> U64
  NatV _      -> Nat
  StructV xs  -> Struct (map valTy xs)
  WrapV   n x -> Named n (valTy x)
  FunV {}     -> error "valTy: FunV"

--------------------------------------------------------------------------------
