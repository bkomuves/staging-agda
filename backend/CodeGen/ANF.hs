
-- conversion to Administrative Normal Form

{-# LANGUAGE PatternSynonyms #-}
module CodeGen.ANF where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict

import qualified Data.Foldable as F
import qualified Data.Sequence as Seq    ; import Data.Sequence ( Seq , (|>) , (<|) , (><) )
import qualified Data.IntMap   as IntMap ; import Data.IntMap   ( IntMap )

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import CodeGen.Lifting ( FunDef(..) , Program(..) , printProgramWith )

import Aux.Misc

--------------------------------------------------------------------------------

type Context = Seq Ty

pattern IFTE b x y = Pri (MkRawPrim "IFTE") [b,x,y]

--------------------------------------------------------------------------------

type Level  = Int
type TopLev = Int

data Atom 
  = VarA !Level        -- ^ local variable (de Bruijn levels)
  | TopA !TopLev       -- ^ top-level variable
  | KstA !Val          -- ^ literal constant
  --  | ExtA !Int          -- ^ external input
  deriving (Eq,Show)

--------------------------------------------------------------------------------

isAtom :: Raw -> Maybe Atom
isAtom (Var   j) = Just (VarA j)
isAtom (Top   k) = Just (TopA k)
isAtom (Lit   x) = Just (KstA x)
isAtom (Log _ r) = isAtom r
isAtom _         = Nothing

-- multi-application
data Application a 
  = MkApp a [a]
  deriving (Eq,Show)

isApplication :: Raw -> Maybe (Application Raw)
isApplication (Log _ body) = isApplication body
isApplication what = 
  case go what of
    (_,[]) -> Nothing
    (f,as) -> Just (MkApp f $ reverse as)
  where
    go (App f x) = case go f of (g,xs) -> (g,x:xs) 
    go (Log _ r) = go r
    go t         = (t,[])

--------------------------------------------------------------------------------

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

typeOfANFE :: ANFE -> Ty
typeOfANFE = typeOf . _in

--------------------------------------------------------------------------------

showExpA :: ExpA -> String
showExpA = show

showAnfLet :: Level -> Typed ExpA -> String
showAnfLet level (MkTyped ty expr) = 
  "\nlet x" ++ show level ++ " : " ++ show ty ++ " := \n  " ++ showExpA expr

showANF' :: Show a => Level -> ANF a -> String
showANF' level (MkANF lets main) = concat strs ++ "\nin " ++ show main where
  strs :: [String]
  strs = map (uncurry showAnfLet) (zip [level..] $ F.toList lets)

showANFE :: ANFE -> String
showANFE = showANF' 0 

printANF' :: Show a => Level -> ANF a -> IO ()
printANF' level anf = do
  putStrLn (showANF' level anf)

printANF :: ANFE -> IO ()
printANF = printANF' 0

printANFProgram :: Program ANFE -> IO ()
printANFProgram = printProgramWith showANFE

--------------------------------------------------------------------------------

type LevelMap = IntMap Level
type TopCtx   = Context

data Local = MkLocal
  { _oldLevel :: !Level
  , _newLevel :: !Level
  , _localCtx :: !Context
  , _levelMap :: !LevelMap
  }
  deriving (Eq,Show)

type M a = StateT Local (Reader TopCtx) a

-- totally resets the state after running
withCompleteReset :: M a -> M a
withCompleteReset action = do
  old <- get
  y   <- action
  put old
  return y

-- resets the state after running, except for `newLevel`
withPartialReset :: M a -> M a
withPartialReset  action = do
  old <- get
  y   <- action
  new <- get
  let old' = old { _newLevel = _newLevel new }
  put old' 
  return y

typeOfLocalVar :: Level -> M Ty
typeOfLocalVar j = do
  local <- get
  case Seq.lookup j (_localCtx local) of
    Just ty -> return ty
    Nothing -> error "typeOfLocalVar: index not found in local context"

typeOfTopVar :: TopLev -> M Ty
typeOfTopVar k = do
  topctx <- lift ask
  case Seq.lookup k topctx of
    Just ty -> return ty
    Nothing -> error "typeOfTopVar: index not found in global context"

lookupNewLevel :: Level -> M Level
lookupNewLevel oldj = do
  local <- get
  case IntMap.lookup oldj (_levelMap local) of
    Just newj -> return newj
    Nothing   -> error "lookupNewLevel: index not found in the level translation map"

incNewLevel :: M Level
incNewLevel = do
  MkLocal ol nl ctx mp <- get
  let nl' = nl + 1
  put (MkLocal ol nl' ctx mp)
  return nl

--------------------------------------------------------------------------------

funDefToANF :: TopCtx -> FunDef Raw -> FunDef ANFE
funDefToANF topCtx fundef@(MkFunDef idx name funTy body) = MkFunDef idx name funTy body' where
  argCtx = Seq.fromList (_argTys funTy)
  body'  = toANF' topCtx argCtx body

programToANF' :: TopCtx -> Program Raw -> Program ANFE
programToANF' topCtx (MkProgram tops main) = MkProgram tops' main' where
  tops' = fmap (funDefToANF topCtx) tops
  main' = toANF topCtx main

programToANF :: Program Raw -> Program ANFE
programToANF prog@(MkProgram tops _main) = programToANF' topctx prog where
  topctx = fmap (fromFunTy . _funType) tops

--------------------------------------------------------------------------------

toANF :: TopCtx -> Raw -> ANF (Typed ExpA)
toANF topCtx rawterm = toANF' topCtx Seq.empty rawterm

toANF' :: TopCtx -> Context -> Raw -> ANF (Typed ExpA)
toANF' topCtx localCtx term = runReader (evalStateT (workerANF term) iniLocal) topCtx where
  arity  = Seq.length localCtx
  transl = IntMap.fromList [ (i,i) | i<-[0..arity-1] ]
  iniLocal :: Local
  iniLocal = MkLocal arity arity localCtx transl

workerAtom :: Raw -> M (ANF (Typed Atom))
workerAtom term = do
  MkANF lets1 (MkTyped ty exp1) <- workerANF term
  case exp1 of
    AtmE atom -> return $ MkANF lets1 (MkTyped ty atom)
    _         -> do j' <- incNewLevel
                    let atom = VarA j'
                    return $ MkANF (lets1 |> (MkTyped ty exp1)) (MkTyped ty atom)

workerAtomList :: [Raw] -> M (ANF [Typed Atom])
workerAtomList [] = return $ MkANF Seq.empty []
workerAtomList (this:rest) = do
  MkANF lets1 atom1 <- workerAtom     this
  MkANF lets2 atoms <- workerAtomList rest
  return $ MkANF (lets1 >< lets2) (atom1 : atoms)

workerANF :: Raw -> M (ANF (Typed ExpA))
workerANF raw = withPartialReset $ unsafeWorkerANF raw

unsafeWorkerANF :: Raw -> M (ANF (Typed ExpA))
unsafeWorkerANF term = case term of

  Lit y -> return $ MkANF Seq.empty (MkTyped (valTy y) (AtmE $ KstA y)) 

  Var j -> do
    ty <- typeOfLocalVar j
    j' <- lookupNewLevel j
    return $ MkANF Seq.empty (MkTyped ty (AtmE $ VarA j'))

  Top k -> do
    ty <- typeOfTopVar k
    return $ MkANF Seq.empty (MkTyped ty (AtmE $ TopA k)) 

  Log _name body -> workerANF body

  Let ty rhs body -> do
    MkANF lets1 (MkTyped ty1 exp1) <- workerANF rhs
    unless (ty == ty1) $ error "workerANF: Let bound type is inconsistent"
    MkLocal oldLevel newLevel ctx levelMap <- get
    let oldLevel' = oldLevel + 1
        newLevel' = newLevel + 1
        ctx'      = ctx |> ty
        levelMap' = IntMap.insert oldLevel newLevel levelMap
        local'    = MkLocal oldLevel' newLevel' ctx' levelMap'
    put local'
    MkANF lets2 tyExp2 <- workerANF body
    return $ MkANF ((lets1 |> (MkTyped ty1 exp1)) >< lets2) tyExp2

  App {} -> case isApplication term of
    Nothing -> error "workerANF: this should never happen"
    Just (MkApp fun args) -> do 
      MkANF lets1 (MkTyped funTy funAtom) <- workerAtom fun
      MkANF lets2 atoms <- workerAtomList args
      let top1 = case funAtom of
            TopA k -> k
            _      -> error "workerANF: application to something non-toplevel"
      let (argTys, argAtoms) = unzipTy atoms 
      case tyApp funTy argTys of
        Nothing    -> error "workerANF: invalid application"
        Just retTy -> case retTy of
          Arrow {}   -> let info = unlines
                              [ "top-level fun #" ++ show top1
                              , "with type :: " ++ show funTy
                              , "with arguments = " ++ show atoms
                              ]
                        in  error $ "workerANF: application resulting in a function type\n" ++ info
          _          -> return $ MkANF (lets1 >< lets2) (MkTyped retTy (AppE top1 argAtoms))

  IFTE cond trueBr falseBr -> do
    MkANF lets1 (MkTyped condTy cond1) <- workerAtom cond
    unless (condTy == Bit) $ error "workerANF: condition in `if` is expected to have type `Bit`" 
    trueBranch1  <- withCompleteReset $ workerANF trueBr
    falseBranch1 <- withCompleteReset $ workerANF falseBr
    let trueTy  = typeOfANFE trueBranch1
    let falseTy = typeOfANFE falseBranch1
    unless (trueTy == falseTy) $ error "workerANF: incompatible types of true and false branche"
    let ifte = IftE cond1 trueBranch1 falseBranch1
    return $ MkANF lets1 (MkTyped trueTy ifte)

  Pri op args -> do
    MkANF lets1 typedAtoms <- workerAtomList args
    let (tys, atoms) = unzipTy typedAtoms
    let retTy = primOpTy op tys
    return $ MkANF lets1 (MkTyped retTy (PriE op atoms))

--------------------------------------------------------------------------------
