module Data.Integer.CooperSAT.Syntax (
    AExp(..), BExp(..), subst, randBExp,
    fvBExp
    ) where

import qualified Data.Set as S
import qualified Data.Map as M
import System.Random

data AExp =
    Lit Integer
    | Var Int
    | Add AExp AExp
    | Mul Integer AExp
    deriving (Eq, Ord, Read, Show)

data BExp =
    Conj BExp BExp
    | Disj BExp BExp
    | Not BExp
    | Less AExp AExp
    | Divs Integer AExp
    deriving (Eq, Ord, Read, Show)

fvAExp :: AExp -> S.Set Int
fvAExp (Lit _)      = S.empty
fvAExp (Var v)      = S.singleton v
fvAExp (Add e0 e1)  = S.union (fvAExp e0) (fvAExp e1)
fvAExp (Mul _ e)    = fvAExp e

fvBExp :: BExp -> S.Set Int
fvBExp (Conj e0 e1) = S.union (fvBExp e0) (fvBExp e1)
fvBExp (Disj e0 e1) = S.union (fvBExp e0) (fvBExp e1)
fvBExp (Not e)      = fvBExp e
fvBExp (Divs v e)   = fvAExp e
fvBExp (Less e0 e1) = S.union (fvAExp e0) (fvAExp e1)

closed :: BExp -> Bool
closed e = (fvBExp e) == S.empty

type Subst = M.Map Int AExp

substA :: AExp -> Subst -> AExp
substA e@(Lit _) s                  = e
substA e@(Var v) s  | M.member v s  = s M.! v
                    | otherwise     = e
substA (Add e0 e1) s                =
    Add (substA e0 s) (substA e1 s)
substA (Mul v e) s                  =
    Mul v (substA e s)

subst :: BExp -> Subst -> BExp
subst (Conj e0 e1) s = Conj (subst e0 s) (subst e1 s)
subst (Disj e0 e1) s = Disj (subst e0 s) (subst e1 s)
subst (Not e) s      = Not (subst e s)
subst (Less e0 e1) s = Less (substA e0 s) (substA e1 s)
subst (Divs c e) s   = Divs c (substA e s)

nextMod :: StdGen -> Int -> Int
nextMod gen m = case (next gen) of (x, _) -> x `mod` m

randTerm :: StdGen -> AExp
randTerm gen = case (nextMod gen 2) of
    0 -> Lit . toInteger $ nextMod gen 100
    1 -> Var (nextMod gen 6)

randAExp :: StdGen -> Int -> AExp
randAExp gen 0 = randTerm gen
randAExp gen n = case (nextMod gen0 3) of
    0 -> randTerm gen1
    1 -> randTerm gen1
    2 -> Add (randAExp gen1 (n - 1)) (randAExp gen2 (n - 1))
    where
    (gen', gen0) = split gen
    (gen2, gen1) = split gen'

randBExp :: StdGen -> Int -> BExp
randBExp gen 0 = Less (randAExp gen 0) (randAExp gen 1)
randBExp gen n = case (nextMod gen0 4) of
    0 -> Conj (randBExp gen1 (n - 1)) (randBExp gen2 (n -1))
    1 -> Disj (randBExp gen1 (n - 1)) (randBExp gen2 (n - 1))
    2 -> Not (randBExp gen1 (n - 1))
    3 -> Less (randAExp gen1 (n - 1)) (randAExp gen2 (n - 1))
    where
    (gen', gen0) = split gen
    (gen2, gen1) = split gen'

