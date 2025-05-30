
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving, PatternSynonyms #-}

module AST.Term
  ( AST 
  , Raw(..) 
  , appList , lamList
  , shiftVars , mapVars -- , shiftVars'
  , module AST.Ty
  , module AST.Val
  , module AST.PrimOp
  , TyEnv , inferTy , inferTy_
  )
  where

--------------------------------------------------------------------------------

import Data.Sequence ( Seq , (|>) )
import qualified Data.Sequence as Seq

import AST.Ty
import AST.Val
import AST.PrimOp

import Aux.Misc

--------------------------------------------------------------------------------

type Level  = Int
type TopLev = Int

type AST = Raw

data Raw where
  Lam :: Ty -> Raw -> Raw
  Let :: Ty -> Raw -> Raw -> Raw
  App :: Raw -> Raw -> Raw
  Fix :: Raw -> Raw
  Pri :: RawPrim -> [Raw] -> Raw
  Lit :: Val -> Raw
  Var :: Level  -> Raw
  Top :: TopLev -> Raw               -- ^ top level variable. This is only used for lambda lifting
  Log :: String -> Raw -> Raw        -- ^ give name to things for debugging etc

pattern NamedVar name j    = Log name (Var j)
pattern NamedTop name k    = Log name (Top k)
pattern NamedLam name ty f = Log name (Lam ty f)

deriving instance Eq   Raw
deriving instance Show Raw
deriving instance Read Raw

appList :: Raw -> [Raw] -> Raw
appList = go where
  go fun []     = fun
  go fun (x:xs) = go (App fun x) xs

lamList :: [Ty] -> Raw -> Raw
lamList = go where
  go []     body = body
  go (t:ts) body = Lam t (go ts body)

--------------------------------------------------------------------------------

shiftVars :: (Level -> Level) -> Raw -> Raw
shiftVars f = shiftVars' (\_ j -> f j)

-- | @f = \level var -> var'@
shiftVars' :: (Level -> Level -> Level) -> Raw -> Raw
shiftVars' f = go 0 where
  go :: Level -> Raw -> Raw
  go level term = case term of

    Var j -> Var (f level j)
    Top k -> Top k
    Lit v -> Lit v

    App fun args -> App (go level fun) (go level args)
    Pri op  args -> Pri op (map (go level) args)
    Fix rec      -> Fix (go level rec)

    Let t rhs body -> Let t (go level rhs) (go (level+1) body)
    Lam t body     -> Lam t (go (level+1) body)

    Log t body     -> Log t (go level body)

mapVars :: (Level -> Raw) -> Raw -> Raw
mapVars f = go 0 where
  go :: Level -> Raw -> Raw
  go level term = case term of

    Var j -> f j
    Top k -> Top k
    Lit v -> Lit v

    App fun args -> App (go level fun) (go level args)
    Pri op  args -> Pri op (map (go level) args)
    Fix rec      -> Fix (go level rec)

    Let t rhs body -> Let t (go level rhs) (go (level+1) body)
    Lam t body     -> Lam t (go (level+1) body)

    Log t body     -> Log t (go level body)

--------------------------------------------------------------------------------

type TyEnv = Seq Ty

inferTy_ :: Raw -> Ty
inferTy_ = inferTy Seq.empty Seq.empty

inferTy :: TyEnv -> TyEnv -> Raw -> Ty
inferTy topEnv = go where

  go :: TyEnv -> Raw -> Ty
  go localEnv term = case term of

    Var j -> case Seq.lookup j localEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTy: local variable " ++ show j ++ " not found in local context"
    
    Top k -> case Seq.lookup k topEnv of 
      Just ty -> ty 
      Nothing -> error $ "inferTy: top level variable " ++ show k ++ " not found in top level context"

    Lam t body     -> Arrow t (go (localEnv |> t) body)
    Let t rhs body -> if go localEnv rhs == t 
      then go (localEnv |> t) body
      else error "inferTy: inconsistent let binding type"

    App fun arg -> case go localEnv fun of
      Arrow s t   -> if go localEnv arg == s 
        then t
        else error "inferTy: incompatible function application"
      _ -> error "inferTy: application to a non-lambda"

    Fix rec -> case go localEnv rec of
      Arrow s t -> if s == t 
        then s
        else error "inferTy: invalid fixpoint"
      what -> error $ "inferTy: fixpoint applied to non-lambda: " ++ show what

    Pri op args -> primOpTy op (map (go localEnv) args)

    Lit val -> valTy val

    Log _ body -> go localEnv body

--------------------------------------------------------------------------------
