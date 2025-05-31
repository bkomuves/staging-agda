
-- | C names for types and struct / typdefs definitions

{-# LANGUAGE RecordWildCards #-}
module CodeGen.C.Types where

--------------------------------------------------------------------------------

import Control.Monad.State.Strict

import qualified Data.Map as Map ; import Data.Map ( Map )

import AST.Ty
import Aux.Lens

--------------------------------------------------------------------------------

type CType  = String
type CDecl  = String
type TyMap  = Map Ty CType

data TyLenses s = MkTyLenses 
  { tyMapLens  :: Lens s TyMap         -- ^ mapping from AST types to C type names
  , tyDefsLens :: Lens s [CDecl]       -- ^ list of C type declarations (opposite order)
  , tySCntLens :: Lens s Int           -- ^ fresh name counter for structs
  } 

freshStructName :: Monad m => Lens s Int -> StateT s m String
freshStructName lens = do
  old <- get
  let name = "S" ++ show (getter lens old)
  let new = modifier lens (+1) old
  put new
  return name

insertTyDecl :: Monad m => Lens s [CDecl] -> CDecl -> StateT s m ()
insertTyDecl lens cdecl = do
  modifyVia lens (cdecl:)

insertTyName :: Monad m => Lens s TyMap -> Ty -> CType -> StateT s m ()
insertTyName lens ty ctype = do
  modifyVia lens (Map.insert ty ctype)

--------------------------------------------------------------------------------

builtInTypes :: Map Ty String
builtInTypes = Map.fromList
  [ (Unit             , "Unit"       ) -- "void"
  , (Bit              , "Bit"        ) -- "bool"
  , (U64              , "U64"        ) -- "uint64_t"
  , (Nat              , "Nat"        ) -- "unsigned int"
  , (Struct [Bit,U64] , "PairBitU64" )
  , (Struct [U64,U64] , "PairU64U64" )
  ]

isBuiltInType :: Ty -> Bool
isBuiltInType ty = Map.member ty builtInTypes

getTyName :: forall s m. Monad m => TyLenses s -> Ty -> StateT s m CType
getTyName MkTyLenses{..} = worker where

  worker :: Ty -> StateT s m CType
  worker ty = do
    table <- getter tyMapLens <$> get
    case Map.lookup ty table of
      Just name -> return name
      Nothing   -> case ty of

{-
        Unit        -> return "Unit" -- "void"
        Bit         -> return "Bit"  -- "bool"
        U64         -> return "U64"  -- "uint64_t"
        Nat         -> return "Nat"  -- "unsigned int"
-}

        Struct flds -> do
          sname   <- ("struct " ++) <$> freshStructName tySCntLens
          cfields <- mapM worker flds
          let decl = unlines $ 
                [ sname ++ " {" ] ++
                [ "  " ++ cty ++ " " ++ fld ++ ";" | (i,cty) <- zip [0..] cfields , let fld = "_field" ++ show i ] ++
                [ "};" ]
          insertTyDecl tyDefsLens decl
          insertTyName tyMapLens ty sname 
          return sname

        Named name base  -> do
          cbase <- worker base
          let decl = "typedef " ++ cbase ++ " " ++ name ++ ";"
          insertTyDecl tyDefsLens decl
          insertTyName tyMapLens ty name 
          return name

        -- Array base  -> do
        --   cbase <- worker base
        --   return ("*" ++ cbase)
 
        Arrow _ _ -> do
          error $ "getTyName: don't call `getTyName` with a function type: \n" ++ show ty 

        _ -> error $ "getTyName: unhandled type:\n  `" ++ show ty ++ "`"

--------------------------------------------------------------------------------
