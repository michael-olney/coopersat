module Main where

import Data.Integer.CooperSAT
import Data.Integer.CooperSAT.Syntax
import Control.Monad
import RefSolver
import qualified Data.Set as S
import System.Random

import Test.HUnit
import System.Exit

randBExpIO :: IO BExp
randBExpIO = do
    gen <- newStdGen
    return (randBExp gen 5)

sample :: IO Bool
sample = do
    e <- randBExpIO
    let them = refSat e
    let us = cooperSat e
    return (us == them)

intDiv :: Int -> Int -> Float
intDiv a b = (fromIntegral a) / (fromIntegral b)

samples :: Int -> IO Bool
samples n = aux n True
    where
    aux n False     = return False
    aux 0 True      = return True
    aux n True      = sample >>= aux (n - 1)

refSolver = TestCase (samples 10000 >>= assertBool "ref solver mismatch")

tests = TestList [
    TestLabel "refSolver" refSolver
    ]

main :: IO ()
main = do
    r <- runTestTT $ tests
    if failures r > 0 then System.Exit.exitFailure else return ()

