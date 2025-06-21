
{-# LANGUAGE PatternSynonyms #-}
module Run.Eval.Monadic where

--------------------------------------------------------------------------------

import Data.Word
import Data.Bits

import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.State.Strict

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import CodeGen.Lifting
import CodeGen.ANF

import Run.Input
import Run.Prim

import Aux.Misc

--------------------------------------------------------------------------------

runWithInputs :: (a -> EvalM b) -> Inputs -> a -> (Outputs, b)
runWithInputs action inputs x = 
  case runState (action x) iniState of
    (result, outState) -> (_outputs outState , result)
  where
    iniState = emptyEvalState { _inputs = inputs }

evalWithInputs :: Inputs -> Raw -> (Outputs, ValM)
evalWithInputs = runWithInputs evalM

evalM :: Raw -> EvalM ValM
evalM = evalInEnvM Seq.empty emptyEnv

--------------------------------------------------------------------------------

pattern Fun f = FunV (MkFun f)

evalInEnvM :: Seq (FunDef Raw) -> EnvM -> Raw -> EvalM ValM
evalInEnvM topEnv = go where

  go ::  EnvM -> Raw -> EvalM ValM
  go env term = case term of

    Lam _ty body -> return $ Fun (\x -> go (env |> x) body)

    Let _ty rhs body -> do
      rhs' <- go env rhs
      go (env |> rhs') body

    App fun arg -> do
      fun' <- go env fun
      case fun' of
        Fun f -> f =<< (go env arg)
        _     -> error "evalInEnvM: application to a non-lambda"

    Fix fun -> do
      fun' <- go env fun
      case fun' of
        Fun f -> evalFixM f
        _     -> error "evalInEnvM: fixpoint of a non-lambda"

    Pri op args  -> do
      ys <- mapM (go env) args 
      evalPrimOpMonadic (MkPrim op ys)

    Lit val -> return (castVal val)

    Var j -> return (Seq.index env j)

    Top k -> go Seq.empty $ funDefToLam (Seq.index topEnv k)

    Log _ body -> go env body

evalFixM :: (ValM -> EvalM ValM) -> EvalM ValM
evalFixM f = f =<< (evalFixM f) 

runProgramM :: Program Raw -> EvalM ValM
runProgramM (MkProgram tops main) = evalInEnvM tops Seq.empty main

runProgramWithInputs :: Inputs -> Program Raw -> (Outputs, ValM)
runProgramWithInputs = runWithInputs runProgramM

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

evalAnfInEnvM :: Seq (FunDef ANFE) -> EnvM -> ANFE -> EvalM ValM
evalAnfInEnvM topEnv = goANF where

  goAtom :: EnvM -> Atom -> EvalM ValM
  goAtom locEnv atom = case atom of
    VarA j -> return $ Seq.index locEnv j
    KstA v -> return $ castVal v
    TopA k -> error "evalANF: trying to evaluate top-level lambda"

  goTyExp ::  EnvM -> Typed ExpA -> EvalM ValM
  goTyExp env (MkTyped ty expr) = goExp env expr

  goApp :: EnvM -> FunDef ANFE -> [ValM] -> EvalM ValM
  goApp env (MkFunDef _idx _name funTy body _fix) args = 
    goANF (Seq.fromList args) body
    
  goExp :: EnvM -> ExpA -> EvalM ValM
  goExp env expr = case expr of

    AtmE atom -> goAtom env atom

    AppE topIdx args     -> do
      args' <- mapM (goAtom env) args
      goApp env (Seq.index topEnv topIdx) args'

    PriE op args         -> do
      args' <- mapM (goAtom env) args
      evalPrimOpMonadic (MkPrim op args')

    IftE cond tbr fbr    -> do
      cond' <- goAtom env cond
      goIfte env cond' tbr fbr

  goIfte :: EnvM -> ValM -> ANFE -> ANFE -> EvalM ValM
  goIfte env cond tbr fbr = case cond of 
    BitV True  -> goANF env tbr
    BitV False -> goANF env fbr
    _          -> error "evalANF: IFTE: condition is not a boolean"
    
  goANF :: EnvM -> ANFE -> EvalM ValM
  goANF env0 (MkANF lets expr) = worker env0 (F.toList lets) where
    worker env []     = goTyExp env expr
    worker env (u:us) = do
      v <- goTyExp env u 
      worker (env |> v) us

runANFProgramM :: Program ANFE -> EvalM ValM
runANFProgramM (MkProgram tops main) = evalAnfInEnvM tops Seq.empty main

runANFProgramWithInputs :: Inputs -> Program ANFE -> (Outputs, ValM)
runANFProgramWithInputs = runWithInputs runANFProgramM

--------------------------------------------------------------------------------

