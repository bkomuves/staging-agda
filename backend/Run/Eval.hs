
{-# LANGUAGE PatternSynonyms #-}
module Run.Eval where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )
import qualified Data.Foldable as F

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import CodeGen.Lifting
import CodeGen.ANF

import Run.Semantics

import Aux.Misc

--------------------------------------------------------------------------------

type Env = Seq Val

emptyEnv :: Env
emptyEnv = Seq.empty

eval :: Raw -> Val
eval = evalInEnv Seq.empty emptyEnv

pattern Fun f = FunV (MkFun f)

evalInEnv :: Seq (FunDef Raw) -> Env -> Raw -> Val
evalInEnv topEnv = go where

  go ::  Env -> Raw -> Val
  go env term = case term of
    Lam _ty body      -> Fun (\x -> go (env |> x) body)
    Let _ty rhs body  -> go (env |> go env rhs) body
    App fun arg       -> case (go env fun) of
                           Fun f -> f (go env arg)
                           _     -> error "evalInEnv: application to a non-lambda"
    Fix fun           -> case (go env fun) of
                           Fun f -> evalFix f
                           _     -> error "evalInEnv: fixpoint of a non-lambda"
    Pri op args       -> let ys = map (go env) args in evalPrimOp (MkPrim op ys)
    Lit val           -> val
    Var j             -> Seq.index env j
    Top k             -> go Seq.empty $ funDefToLam (Seq.index topEnv k)
    Log _ body        -> go env body

evalFix :: (Val -> Val) -> Val
evalFix f = f (evalFix f) 
-- evalFix _ = error "evalFix: not yet implemented"

runProgram :: Program Raw -> Val
runProgram (MkProgram tops main) = evalInEnv tops Seq.empty main

--------------------------------------------------------------------------------

{-

data Atom 
  = VarA !Level        -- ^ local variable (de Bruijn levels)
  | TopA !TopLev       -- ^ top-level variable
  | KstA !Val          -- ^ literal constant
  --  | ExtA !Int          -- ^ external input
  deriving (Eq,Show)

-- expressions
data ExpA
  = AtmE !Atom
  | AppE !TopLev  [Atom]
  | PriE !RawPrim [Atom] 
  | IftE !Atom !ANFE !ANFE
  deriving (Eq,Show)
 
data ANF hole = MkANF 
  { _lets :: !(Seq (Typed ExpA))
  , _in   :: !hole
  }
  deriving (Eq,Show)

type ANFE = ANF (Typed ExpA)

 { _funIdx  :: Int         -- ^ top level index
  , _funName :: String
  , _funType :: FunTy
  , _funBody :: a 
  }
-}

evalAnfInEnv :: Seq (FunDef ANFE) -> Env -> ANFE -> Val
evalAnfInEnv topEnv = goANF where

  goAtom :: Env -> Atom -> Val
  goAtom locEnv atom = case atom of
    VarA j -> Seq.index locEnv j
    TopA k -> error "evalANF: trying to evaluate top-level lambda"
    KstA v -> v

  goTyExp ::  Env -> Typed ExpA -> Val
  goTyExp env (MkTyped ty expr) = goExp env expr

  goApp :: Env -> FunDef ANFE -> [Val] -> Val
  goApp env (MkFunDef _idx _name funTy body _fix) args = 
    goANF (Seq.fromList args) body
    
  goExp :: Env -> ExpA -> Val
  goExp env expr = case expr of
    AtmE atom            -> goAtom env atom
    AppE topIdx args     -> goApp env (Seq.index topEnv topIdx) (map (goAtom env) args)
    PriE op args         -> evalPrimOp (MkPrim op $ map (goAtom env) args)
    IftE cond tbr fbr    -> goIfte env (goAtom env cond) tbr fbr

  goIfte :: Env -> Val -> ANFE -> ANFE -> Val
  goIfte env cond tbr fbr = case cond of 
    BitV True  -> goANF env tbr
    BitV False -> goANF env fbr
    _          -> error "evalANF: IFTE: condition is not a boolean"
    
  goANF :: Env -> ANFE -> Val
  goANF env0 (MkANF lets expr) = worker env0 (F.toList lets) where
    worker env []     = goTyExp env expr
    worker env (u:us) = let v = goTyExp env u 
                        in  worker (env |> v) us

runANFProgram :: Program ANFE -> Val
runANFProgram (MkProgram tops main) = evalAnfInEnv tops Seq.empty main

--------------------------------------------------------------------------------

data Prim a 
  = MkPrim RawPrim [a]
  deriving (Eq,Show)

evalPrimOp :: Prim Val -> Val
evalPrimOp primArgs = case primArgs of

  MkPrim (MkRawPrim prim   ) args          -> evalNormalPrim (prim, args)
  MkPrim (RawProj   j      ) [StructV xs]  -> xs !! j
  MkPrim (RawWrap   name   ) [x]           -> WrapV name x
  MkPrim (RawInput  name ty) []            -> error "evalPrimOp: input"
  MkPrim (RawOutput name   ) [x]           -> error "evalPrimOp: output"

  _ -> error "evalPrimOp: invalid combination"

--------------------------------------------------------------------------------

-- just sugar for nicer patterns below
pattern name :@@ args = (name, args)

evalNormalPrim :: (String , [Val]) -> Val
evalNormalPrim primArgs = 

  case primArgs of

    "AddU64"        :@@ [ U64V x , U64V y ]             -> U64V (x + y)
    "SubU64"        :@@ [ U64V x , U64V y ]             -> U64V (x - y)
    "AddCarryU64"   :@@ [ BitV cin , U64V x , U64V y ]  -> pairBitU64 (addCarry64 cin x y)
    "SubCarryU64"   :@@ [ BitV cin , U64V x , U64V y ]  -> pairBitU64 (subCarry64 cin x y)
    "MulTruncU64"   :@@ [ U64V x , U64V y ]             -> U64V (x * y)
    "MulExtU64"     :@@ [            U64V x , U64V y ]  -> pairU64U64 (mulExtU64   x y)
    "MulAddU64"     :@@ [ U64V a   , U64V x , U64V y ]  -> pairU64U64 (mulAddU64 a x y)
    "BitComplement" :@@ [ U64V x ]                      -> U64V (complement x)
    "BitOr"         :@@ [ U64V x , U64V y ]             -> U64V (x .|. y)
    "BitAnd"        :@@ [ U64V x , U64V y ]             -> U64V (x .&. y)
    "BitXor"        :@@ [ U64V x , U64V y ]             -> U64V (x `xor` y)
    "RotLeftU64"    :@@ [ BitV cin , U64V x ]           -> pairBitU64 (rotLeftU64  cin x)    
    "RotRightU64"   :@@ [ BitV cin , U64V x ]           -> pairBitU64 (rotRightU64 cin x)
    "EqU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primEqU64 x y) 
    "LtU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primLtU64 x y)  
    "LeU64"         :@@ [ U64V x   , U64V y ]           -> BitV (primLeU64 x y) 
    "CastBitU64"    :@@ [ BitV b ]                      -> U64V (primCastBitU64 b)
    "Not"           :@@ [ BitV b ]                      -> BitV (not b)
    "And"           :@@ [ BitV a , BitV b ]             -> BitV (a && b)
    "Or"            :@@ [ BitV a , BitV b ]             -> BitV (a || b)
    "IFTE"          :@@ [ BitV b , x , y ]              -> if b then x else y
    "MkStruct"      :@@ xs                              -> StructV xs
    "Unwrap"        :@@ [ WrapV _ x ]                   -> x
    "Zero"          :@@ []                              -> NatV 0
    "Succ"          :@@ [ NatV n ]                      -> NatV (n + 1)
    "IsZero"        :@@ [ NatV n ]                      -> BitV (n == 0)
    "NatAdd"        :@@ [ NatV x , NatV y ]             -> NatV (x + y)
    "NatMul"        :@@ [ NatV x , NatV y ]             -> NatV (x * y)
    "NatSubTrunc"   :@@ [ NatV x , NatV y ]             -> NatV (max 0 (x - y))

    _ -> error $ "evalNormalPrim: either unimplement or invalid: `" ++ show (fst primArgs) ++ "`"

  where 

    pairBitU64 :: (Bit, Word64) -> Val
    pairBitU64 (bit,word) = PairV (BitV bit) (U64V word)

    pairU64U64 :: (Word64, Word64) -> Val
    pairU64U64 (w1,w2) = PairV (U64V w1) (U64V w2)

--------------------------------------------------------------------------------
