
-- lambda lifting

module CodeGen.Lifting where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.State.Strict

import Data.Maybe

import qualified Data.Set      as Set ; import Data.Set      ( Set )
import qualified Data.Map      as Map ; import Data.Map      ( Map )
import qualified Data.Sequence as Seq ; import Data.Sequence ( Seq , (|>) , (><) )
import qualified Data.Foldable as F

import AST.Ty
import AST.Val
import AST.PrimOp
import AST.Term

import Aux.Misc

--------------------------------------------------------------------------------

-- multi-lambda
data Lambda a = 
  MkLambda [Ty] a
  deriving (Eq,Show)

isLambda :: Raw -> Maybe (Lambda Raw)
isLambda (Log _ body) = isLambda body
isLambda what =
  case go what of
    ([],_   ) -> Nothing
    (ts,body) -> Just (MkLambda ts body)
  where
    go (Lam t body) = case go body of (ts,y) -> (t:ts,y) 
    go y            = ([],y)

--------------------------------------------------------------------------------

data FunDef a = MkFunDef 
  { _funIdx  :: Int         -- ^ top level index
  , _funName :: String
  , _funType :: FunTy
  , _funBody :: a 
  }
  deriving (Eq,Show,Functor)

funDefToLam :: FunDef Raw -> Raw
funDefToLam (MkFunDef _ _ (MkFunTy args _) body) = go args where
  go []     = body
  go (t:ts) = Lam t (go ts)

data Program a = MkProgram
  { _topLevel :: Seq (FunDef a)
  , _prgMain  :: a
  }
  deriving (Eq,Show)

printFunDefWith :: (a -> String) -> FunDef a -> IO ()
printFunDefWith userShow (MkFunDef idx name (MkFunTy argsTy retTy) body) = do
  putStrLn $ "\n" ++ show idx ++ ": def " ++ show name
  putStrLn $ " :: " ++ show argsTy ++ " -> " ++ show retTy
  putStrLn $ " = "
  putStrLn (userShow body)

printFunDef :: Show a => FunDef a -> IO ()
printFunDef = printFunDefWith show 

printProgramWith :: (a -> String) -> Program a -> IO ()
printProgramWith userShow (MkProgram tops main) = do
  mapM_ (printFunDefWith userShow) (F.toList tops)
  putStrLn ""
  putStrLn (userShow main)

printProgram :: Show a => Program a -> IO ()
printProgram = printProgramWith show

--------------------------------------------------------------------------------

type Level  = Int
type TopLev = Int

-- | Compute the set of variables referring "outside" of the giving level
outsideVariables :: Level -> Raw -> Set Level
outsideVariables level0 input = execState (go input) Set.empty where
  go term = case term of

    Var j -> do
      when (j < level0) $ modify (Set.insert j)
      return ()

    Lam t body     -> go body
    Let t rhs body -> go rhs >> go body
    App fun arg    -> go fun >> go arg
    Fix rec        -> go rec
    Pri op args    -> mapM_ go args
    Lit val        -> return ()
    Log name body  -> go body

--------------------------------------------------------------------------------

{-
data Raw where
  Lam :: Ty -> Raw -> Raw
  Let :: Ty -> Raw -> Raw -> Raw
  App :: Raw -> Raw -> Raw
  Fix :: Raw -> Raw
  Pri :: RawPrim -> [Raw] -> Raw
  Lit :: Val -> Raw
  Var :: Int -> Raw
-}

-- we have to deal with functions in the context differently
data CtxEntry 
  = VarEntry  !Ty !Level    -- there could be a chain of variables referring to a top-level at the end
  | TopEntry  !Ty !TopLev   -- reference to a top-level function
  | SomeEntry !Ty           -- something else
  deriving (Eq,Show)

entryTy :: CtxEntry -> Ty
entryTy entry = case entry of
  VarEntry  ty _ -> ty
  TopEntry  ty _ -> ty
  SomeEntry ty   -> ty

data FreeVar
  = FTop !TopLev
  | FVar !Level
  deriving (Eq,Show)

classifyFreeVar :: Context -> Level -> FreeVar
classifyFreeVar ctx level = case isTopLevel_ ctx level of
  Nothing -> FVar level
  Just k  -> FTop k

isTopLevel :: Context -> Level -> Maybe (Typed TopLev)
isTopLevel ctx = worker where
  worker !j = case Seq.lookup j ctx of
    Nothing    -> error $ "isTopLevel: index out of range: " ++ show j
    Just entry -> case entry of
      VarEntry  _  i -> worker i
      TopEntry  ty k -> Just (MkTyped ty k)
      SomeEntry _    -> Nothing

isTopLevel_ :: Context -> Level -> Maybe TopLev
isTopLevel_ ctx j = fmap forgetTy (isTopLevel ctx j)

type Context = Seq CtxEntry

emptyCtx :: Context
emptyCtx = Seq.empty

data S = MkS
  { _topCtx  :: !(Seq Ty)
  , _funs    :: !(Seq (FunDef Raw))
  , _counter :: !Int
  }
  deriving (Eq,Show)

iniS :: S
iniS = MkS Seq.empty Seq.empty 0

type M a = State S a

getTopCtx :: M (Seq Ty)
getTopCtx = _topCtx <$> get

addLams :: [Ty] -> Raw -> Raw
addLams tys body = go tys where
  arity = length tys
  go []     = shiftVars (+arity) body
  go (t:ts) = Lam t (go ts)

addApps :: Raw -> [Raw] -> Raw
addApps = go where
  go fun []     = fun
  go fun (a:as) = go (App fun a) as

lambdaLifting :: Raw -> Program Raw
lambdaLifting raw =

  flip evalState iniS $ do
    main  <- go 0 emptyCtx raw
    state <- get
    return $ MkProgram (_funs state) main
 
  where    

    goFun :: Maybe String -> Level -> Context -> Raw -> M Raw
    goFun !mbName !level !ctx !term = case term of
      Lam {} -> case isLambda term of
        Just lambda@(MkLambda origArgTys body) -> do
          let origArity = length origArgTys
          let freeSet0  = outsideVariables level body
          let freeSet   = Set.filter (isNothing . isTopLevel ctx) freeSet0  :: Set Level
          let freeArity = Set.size   freeSet                :: Int
          let freeIdxs  = Set.toList freeSet                :: [Level]
          let mapping   = Map.fromList (zip freeIdxs [0..]) :: Map Level Int
          let ctxLookup j = case Seq.lookup j ctx of
                Nothing -> error $ "lambdaLifting/ctxLookup: index out of range: " ++ show j
                Just e  -> e
          let freeTys   = map ctxLookup freeIdxs            :: [CtxEntry]
          let shiftfun j = if j >= level
                then Var (j - level + freeArity)
                else case classifyFreeVar ctx j of
                  FTop k  -> Top k
                  FVar _  -> case Map.lookup j mapping of
                    Just i  -> Var i
                    Nothing -> error $ "level " ++ show j ++ " not found in the free variables"
          let body'' = mapVars shiftfun body
          let fullArgTys = (freeTys ++ map SomeEntry origArgTys) :: [CtxEntry]
          let fullArity  = freeArity + origArity   :: Int
          let localCtx   = Seq.fromList fullArgTys :: Context
          topCtx <- getTopCtx
          let retTy = inferTy topCtx (fmap entryTy localCtx) body''
          body''' <- go fullArity localCtx body''
          MkS topctx funs cnt <- get
          let this = MkFunDef 
                { _funIdx  = cnt
                , _funName = case mbName of { Just n -> n ++ show cnt ; Nothing -> "_fun" ++ show cnt }
                , _funType = MkFunTy (map entryTy fullArgTys) retTy
                , _funBody = body'''
                }
              thisTy = fromFunTy (_funType this)
          put $ MkS (topctx |> thisTy) (funs |> this) (cnt+1)
          return (addApps (Top cnt) (map Var freeIdxs))
        _ -> error "lambdaLifting/goFun: fatal: this should not happen"
      _ -> error "lambdaLifting/goFun: expecting a Lambda"

    go :: Level -> Context -> Raw -> M Raw
    go !level !ctx !term = case term of

      Lam ty _                  -> goFun Nothing     level ctx term
      Log name inner@(Lam ty _) -> goFun (Just name) level ctx inner

      Var j -> case isTopLevel ctx j of
                 Nothing            -> return (Var j)
                 Just (MkTyped _ k) -> return (Top k)

      Top k -> return (Top k)
      Lit y -> return (Lit y)

      Pri op args -> do
        args' <- mapM (go level ctx) args
        return (Pri op args')

      App fun arg -> do
        fun' <- go level ctx fun
        arg' <- go level ctx arg
        return (App fun' arg')

      Let t rhs body -> do
        rhs'  <- go level ctx  rhs
        let entry = case rhs' of
              Top k -> TopEntry  t k
              _     -> SomeEntry t
        body' <- go (level+1) (ctx |> entry) body
        return (Let t rhs' body')

      Fix rec -> Fix <$> go level ctx rec

      Log name body -> Log name <$> go level ctx body

--------------------------------------------------------------------------------

