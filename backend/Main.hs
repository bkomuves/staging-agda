
module Main where

--------------------------------------------------------------------------------

import Control.Monad

import Text.Read
import Text.Show.Pretty

import AST.Term
import AST.Random
import Run.Eval

import CodeGen.Lifting
import CodeGen.ANF

import Big.Marshal

--------------------------------------------------------------------------------

-- main = main_Poseidon
-- main = main_MontP
-- main = main_LetFun
-- main = main_Lift
-- main = main_Lam
-- main = main_ModP 
-- main = main_Nat

main = main_Poseidon

main_Lam = do
  runCommon "examples/ex_mixed.ast" $ \_ -> return ()

main_Lift = do
  runCommon "examples/ex_lift1.ast" $ \_ -> return ()

main_Nat = do
  runCommon "examples/ex_nat.ast" $ \_ -> return ()

main_LetFun = do
  runCommon "examples/ex_letfun1.ast" $ \_ -> return ()

main_ModP = do
  runCommon "examples/ex.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
      putStrLn $ "expected : " ++ show xplusy
  where
    r = mod (2^256) p
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    x = 12535032671501493392438659292886563663979619812816639413586309554197071221275
    y = 20670156704232560809430694243501641649572216251781105022963497476851362916519
    z = 10734482926936635597888852654981536388697257091861152194513442686302125663795
    xplusy = mod (x+y) p
    expected = xplusy

main_MontP = do
  runCommon' False "examples/ex_mont2.ast" $ \res -> case res of
    bigint -> do
      printBigIntVal bigint

main_Poseidon = do
  runCommon' False "examples/ex_posei3.ast" $ \res -> case res of
    StructV [bigx, bigy, bigz] -> do
      printBigIntVal bigx
      printBigIntVal bigy
      printBigIntVal bigz

{-
  runCommon "examples/ex_mont.ast" $ \res -> case res of
    WrapV _ bigint -> do
      printBigIntVal bigint
-}


----------------------------------------

runCommon :: FilePath -> (Val -> IO a) -> IO a
runCommon = runCommon' True

runCommon' :: Bool -> FilePath -> (Val -> IO a) -> IO a
runCommon' printAstFlag fname kont = do
  text <- readFile fname
  let mbAST = readMaybe text :: Maybe AST
  case mbAST of
    Nothing  -> error $ "cannot parse AST from `" ++ fname ++ "`"
    Just ast -> do

      when printAstFlag $ do
        putStrLn "---------------------------"
        print ast

      let res = eval ast
      putStrLn $ "\neval result = " ++ show res

      let program = lambdaLifting ast
      let anf     = programToANF  program
      -- let csource = anfToCSource  anf 

      when printAstFlag $ do
        putStrLn "---------------------------"
        putStrLn $ "lambda-lifted program:"
        printProgram program

      when printAstFlag $ do
        putStrLn "---------------------------"
        putStrLn $ "ANF converted program:"
        printANFProgram anf

{-
      when printAstFlag $ do
        putStrLn "---------------------------"
        putStrLn $ "C source code:"
        printANFProgram csource
-}

      putStrLn "---------------------------"
      putStrLn $ "program type = " ++ show (inferTy_ ast)

      putStrLn $ "\nresult of the original term     = " ++ show res
      putStrLn $ "\nresult of lambda lifted program = " ++ show (runProgram program)
      putStrLn $ "\nresult of ANF converted program = " ++ show (runANFProgram anf)
      putStrLn " "
      kont res

--------------------------------------------------------------------------------
-- DEBUGGING

exRaw0 :: Raw
exRaw0 = 
  -- Lit (U64V 101) 
  -- (Pri (MkRawPrim "AddU64") [ Lit (U64V 101) , Lit (U64V 102) ])
  Let U64 (Lit (U64V 101)) (Var 0)

exRaw1 :: Raw
exRaw1 = Let U64 
  (Pri (MkRawPrim "AddU64") [ Lit (U64V 101) , Lit (U64V 102) ])
  (Pri (MkRawPrim "MulTruncU64") [ Var 0 , Var 0 ])

exRaw2 :: Raw
exRaw2 = Let U64 (Lit (U64V 666)) (Pri (MkRawPrim "MulTruncU64") [Var 0,App (App (Lam U64 (Lam U64 (Var 2))) (Lit (U64V 11999))) (Lit (U64V 25715))])

exRaw3 :: Raw
exRaw3 = Let U64 (Lit (U64V 666)) (Pri (MkRawPrim "AddU64") [Let U64 (Var 0) (Lit (U64V 30236)),Let U64 (Lit (U64V 25007)) (Var 1)])

exRaw4 :: Raw
exRaw4 = Let U64 (Lit (U64V 666)) (Let U64 (Let U64 (Var 0) (Lit (U64V 49887))) (Let U64 (Lit (U64V 22063)) (Var 2)))

debugAnfConversion :: Size -> IO ()
debugAnfConversion target = do
  term <- randomTermU64 target
  debugAnfConversion' term

debugAnfConversion' :: Raw -> IO ()
debugAnfConversion' term = do
  if (inferTy_ term /= U64) 
    then error "debugAnfConversion: type inference doesn't match expectations"
    else do
      let prg  = lambdaLifting term
      let anf  = programToANF prg

      putStrLn "---------------------------"
      putStrLn $ "raw program:"
      print term
      putStrLn "---------------------------"
      putStrLn $ "lambda-lifted program:"
      printProgram prg
      putStrLn "---------------------------"
      putStrLn $ "ANF converted program:"
      printANFProgram anf

      let res1 = eval term
      let res2 = runProgram prg
      let res3 = runANFProgram anf
      putStrLn $ "result of original      = " ++ show res1
      putStrLn $ "result of lambda-lifted = " ++ show res2
      putStrLn $ "result of anf converted = " ++ show res3

findAnfCounterExample :: Size -> IO Raw
findAnfCounterExample target = do
  term <- randomTermU64 target
  let prg  = lambdaLifting term
  let anf  = programToANF prg
  let res2 = runProgram prg
  let res3 = runANFProgram anf
  if (res2 /= res3) 
    then return term
    else findAnfCounterExample target

--------------------------------------------------------------------------------

testLambdaLifting1 :: Size -> IO Bool
testLambdaLifting1 target = do
  term <- randomTermU64 target
  if (inferTy_ term /= U64) 
    then error "testLambdaLifting1: type inference doesn't match expectations"
    else do
      let prg  = lambdaLifting term
      let res1 = eval term
      let res2 = runProgram prg
      return (res1 == res2)
  
testAnfConversion1 :: Size -> IO Bool
testAnfConversion1 target = do
  term <- randomTermU64 target
  if (inferTy_ term /= U64) 
    then error "testAnfConversion1: type inference doesn't match expectations"
    else do
      let prg  = lambdaLifting term
      let anf  = programToANF prg
      let res1 = eval term
      let res2 = runProgram prg
      let res3 = runANFProgram anf
      return (res2 == res3)

testLambdaLiftingN :: Int -> Size -> IO Bool
testLambdaLiftingN n target = and <$> replicateM n (testLambdaLifting1 target)
  
testAnfConversionN :: Int -> Size -> IO Bool
testAnfConversionN n target = and <$> replicateM n (testAnfConversion1 target)

--------------------------------------------------------------------------------


