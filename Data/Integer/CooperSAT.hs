{-|
Solver for QFLIA based on Cooper's algorithm, described
in this paper:

    Theorem Proving in Arithmetic without Multipication
    by D. C. Cooper
-}

module Data.Integer.CooperSAT (
    cooperSat,
    module Data.Integer.CooperSAT.Syntax,
    module Data.Integer.CooperSAT.Sem
    ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Integer.CooperSAT.Normalise
import Data.Integer.CooperSAT.Syntax
import Data.Integer.CooperSAT.Sem

data TMKey = Const | Va Int
    deriving (Eq, Ord, Read, Show)

type TermMap = M.Map TMKey Integer

terms' :: AExp -> [AExp]
terms' e@(Lit _)         = [e]
terms' e@(Var _)         = [e]
terms' e@(Mul _ (Var _)) = [e]
terms' (Add e0 e1)       = (terms' e0) ++ (terms' e1)
terms' (Mul _ _)         = error "terms': found Mul"

dist :: Integer -> AExp -> AExp
dist v (Lit x)      = Lit (v*x)
dist v e@(Var _)    = Mul v (expand e)
dist v (Add e0 e1)  = Add (dist v e0) (dist v e1)
dist v (Mul x e)    = Mul (x*v) e

expand :: AExp -> AExp
expand e@(Lit _)    = e
expand e@(Var _)    = e
expand (Add e0 e1)  = Add (expand e0) (expand e1)
expand (Mul v e)    = dist v e

terms :: AExp -> [AExp]
terms = terms' . expand

addMaybe :: Integer -> Maybe Integer -> Maybe Integer
addMaybe v Nothing  = Just v
addMaybe v (Just n) = Just (n + v)

addKey :: TMKey -> Integer -> TermMap -> TermMap
addKey k v = M.alter (addMaybe v) k

toTMAux :: TermMap -> [AExp] -> TermMap
toTMAux tm []               = tm
toTMAux tm ((Lit v):es)     =
    toTMAux (addKey Const v tm) es
toTMAux tm ((Var v):es)     =
    toTMAux (addKey (Va v) 1 tm) es
toTMAux tm ((Mul x (Var v)):es)     =
    toTMAux (addKey (Va v) x tm) es

tmVCount :: TermMap -> Int -> Integer
tmVCount tm v = M.findWithDefault 0 (Va v) tm

tmIso :: Int -> TermMap -> (TermMap, TermMap)
tmIso v tm = (
    M.delete (Va v) tm,
    M.singleton (Va v) (tmVCount tm v)
    )

tmNeg :: TermMap -> TermMap
tmNeg = M.fromList . aux . M.toList
    where   aux = map (\(k, x) -> (k, -x))

tmMul :: Integer -> TermMap -> TermMap
tmMul m tm = M.map (* m) tm

tmAdd :: TermMap -> TermMap -> TermMap
tmAdd tm0 tm1 = foldr aux tm0 (M.toList tm1)
    where aux (k, v) = addKey k v

tmSetExV :: TermMap -> Int -> Integer -> TermMap
tmSetExV tm v x | count /= 0    = M.insert (Va v) x tm
                | otherwise     = tm
    where count = tmVCount tm v

toTM :: AExp -> TermMap
toTM = (toTMAux M.empty) . terms

tmFromEnt :: (TMKey, Integer) -> AExp
tmFromEnt (Const, x)    = Lit x
tmFromEnt (Va v, x)     = Mul x (Var v)

simpA' :: AExp -> AExp
simpA' (Add (Lit 0) e)   = simpA' e
simpA' (Add e (Lit 0))   = simpA' e
simpA' (Add (Lit x) (Lit y)) = Lit (x + y)
simpA' (Add e0 e1)       = Add (simpA' e0) (simpA' e1)
simpA' (Mul x (Lit y))   = Lit (x*y)
simpA' (Mul 1 e)         = simpA' e
simpA' (Mul 0 e)         = Lit 0
simpA' (Mul v e)         = Mul v (simpA' e)
simpA' e                 = e

simpA :: AExp -> AExp
simpA e = (case e' == e of
    True    -> e
    False   -> simpA e')
    where e' = simpA' e

simpB' :: BExp -> BExp
simpB' (Not (Not e))= simpB' e
simpB' (Not e)      = Not (simpB' e)
simpB' (Divs c e1)  = Divs c (simpA' e1)
simpB' (Conj (Less (Lit 0) (Lit 1)) e1) = simpB' e1
simpB' (Conj e0 (Less (Lit 0) (Lit 1))) = simpB' e0
simpB' (Conj (Less (Lit 1) (Lit 0)) e1) = false
simpB' (Conj e0 (Less (Lit 1) (Lit 0))) = false
simpB' (Disj (Less (Lit 0) (Lit 1)) e1) = true
simpB' (Disj e0 (Less (Lit 0) (Lit 1))) = true
simpB' (Disj (Less (Lit 1) (Lit 0)) e1) = simpB' e1
simpB' (Disj e0 (Less (Lit 1) (Lit 0))) = simpB' e0
simpB' (Conj e0 e1) = Conj (simpB' e0) (simpB' e1)
simpB' (Disj e0 e1) = Disj (simpB' e0) (simpB' e1)
simpB' (Less (Lit x) (Lit y))
    | x < y     = true
    | otherwise = false
simpB' (Less e0 e1) = Less (simpA' e0) (simpA' e1)

simpB :: BExp -> BExp
simpB e = (case e' == e of
    True    -> e
    False   -> simpB e')
    where e' = simpB' e

fromTM :: TermMap -> AExp
fromTM tm   | length ts == 0    = Lit 0
            | otherwise         = foldl1 Add ts
    where ts = (map tmFromEnt) . M.toList $ tm

normA :: AExp -> AExp
normA = fromTM . toTM

collect :: BExp -> BExp
collect (Less e0 e1)   = Less (normA e0) (normA e1)
collect (Not (Less e0 e1)) =
    Less (normA e1) (normA (Add e0 (Lit 1)))
collect (Divs v e)     = Divs v (normA e)
collect (Not (Divs v e)) = Not (Divs v (normA e))
collect (Not e)        = error "misplaced not"
collect (Conj e0 e1)   = Conj (collect e0) (collect e1)
collect (Disj e0 e1)   = Disj (collect e0) (collect e1)

trich :: (Eq b, Ord b) => b -> b -> a -> a -> a -> a
trich x y l e g | x < y     = l
                | x == y    = e
                | x > y     = g

normIneq :: Int -> BExp -> BExp
normIneq v (Less e0 e1) = (trich (tmVCount tm v) 0
        (Less e0L e1L)
        (Less e0M e1M)
        (Less e0R e1R)
    )
    where
            tm = tmAdd (toTM e0) (tmNeg (toTM e1))
            (tmL, vtmL) = tmIso v tm
            e0L = fromTM tmL
            e1L = fromTM . tmNeg $ vtmL
            e0M = fromTM $ tm
            e1M = Lit 0
            (tmR, vtmR) = tmIso v tm
            e0R = fromTM vtmR
            e1R = fromTM . tmNeg $ tmR
normIneq _ e = error "called normIneq on wrong rel"

normDivs :: Int -> BExp -> BExp
normDivs v (Divs c e) = Divs c (fromTM tm')
    where
            tm = toTM e
            tm' = case tmVCount tm v < 0 of
                True    -> tmNeg tm
                False   -> tm

normDivs _ e = error "called normDivs on wrong rel"

normL2 :: Int -> BExp -> BExp
normL2 v e@(Less _ _)   = normIneq v e
normL2 v e@(Divs _ _)   = normDivs v e
normL2 v (Conj e0 e1)   =
    Conj (normL2 v e0) (normL2 v e1)
normL2 v (Disj e0 e1)   =
    Disj (normL2 v e0) (normL2 v e1)

norm :: Int -> BExp -> BExp
norm v = simpB . (normL2 v) . simpB . collect . nnf

lcmList :: [Integer] -> Integer
lcmList [] = 1
lcmList [x] = x
lcmList (x:xs) = lcm x (lcmList xs)

coeffsA :: Int -> AExp -> [Integer]
coeffsA v (Lit _)               = []
coeffsA v (Add e0 e1)           =
                    (coeffsA v e0) ++ (coeffsA v e1)
coeffsA v (Var v0)  | v == v0   = [1]
                    | v /= v0   = []
coeffsA v (Mul x (Var v0))
                    | v == v0   = [x]
                    | v /= v0   = []
coeffsA v (Mul x _)             =
                    error "coeffsA: bad Mul"

coeffsB :: Int -> BExp -> [Integer]
coeffsB v (Less e0 e1)  =
    (coeffsA v e0) ++ (coeffsA v e1)
coeffsB v (Divs _ e)    = coeffsA v e
coeffsB v (Not e)       = coeffsB v e
coeffsB v (Conj e0 e1)  =
    (coeffsB v e0) ++ (coeffsB v e1)
coeffsB v (Disj e0 e1)  =
    (coeffsB v e0) ++ (coeffsB v e1)

coeff :: Int -> BExp -> Integer
coeff v (Less e0 e1) =
    (tmVCount (toTM e0) v) + (tmVCount (toTM e1) v)
coeff v (Divs c e) = tmVCount (toTM e) v
coeff _ _ = error "coeff: bad exp"

co1Ineq :: Int -> Integer -> BExp -> BExp
co1Ineq v l e@(Less e0 e1)
        | d == 0    = e
        | otherwise = Less (fromTMS tm0) (fromTMS tm1)
    where   tm0 = tmSetExV (tmMul m (toTM e0)) v 1
            tm1 = tmSetExV (tmMul m (toTM e1)) v 1
            d = coeff v e
            m = l `div` d
            fromTMS = simpA . fromTM
co1Ineq v l _ = error "co1Ineq: bad exp"

co1Divs :: Int -> Integer -> BExp -> BExp
co1Divs v l e@(Divs c e0)
        | d == 0    = e
        | otherwise = Divs (c*m) (fromTM tm)
    where   tm = tmSetExV (tmMul m (toTM e0)) v 1
            d = coeff v e
            m = l `div` d
co1Divs v l _ = error "co1Divs: bad exp"

co1Aux :: Int -> Integer -> BExp -> BExp
co1Aux v l (Not e) = Not (co1Aux v l e)
co1Aux v l e@(Less _ _) = co1Ineq v l e
co1Aux v l e@(Divs _ _) = co1Divs v l e
co1Aux v l (Conj e0 e1) =
    Conj (co1Aux v l e0) (co1Aux v l e1)
co1Aux v l (Disj e0 e1) =
    Disj (co1Aux v l e0) (co1Aux v l e1)

co1 :: Int -> Integer -> BExp -> BExp
co1 v l e = Conj (co1Aux v l e) (Divs l (Var v))

divisors :: Int -> BExp -> [Integer]
divisors v (Less e0 e1)  = []
divisors v (Divs c e)
    | tmVCount (toTM e) v == 1  = [c]
    | tmVCount (toTM e) v == 0  = []
    | otherwise                 = error "divisors"
divisors v (Not e)       = divisors v e
divisors v (Conj e0 e1)  =
    (divisors v e0) ++ (divisors v e1)
divisors v (Disj e0 e1)  =
    (divisors v e0) ++ (divisors v e1)

elimV1 :: Int -> BExp -> BExp
elimV1 v e = case length cs /= 0 of
    True    -> co1 v (lcmList cs) e'
    False   -> e'
    where   e' = norm v e
            cs = coeffsB v e'

type AB = S.Set AExp

isXRight :: Int -> BExp -> Bool
isXRight v (Less e0 (Var v')) = v == v'
isXRight _ _ = False

isXLeft :: Int -> BExp -> Bool
isXLeft v (Less (Var v') e1) = v == v'
isXLeft _ _ = False

aSet :: Int -> BExp -> AB
aSet v (Not e)      = aSet v e
aSet v (Conj e0 e1) = S.union (aSet v e0) (aSet v e1)
aSet v (Disj e0 e1) = S.union (aSet v e0) (aSet v e1)
aSet v e@(Less e0 e1)
        | isXLeft v e   = S.singleton e1
        | otherwise     = S.empty
aSet v _            = S.empty

bSet :: Int -> BExp -> AB
bSet v (Not e)      = bSet v e
bSet v (Conj e0 e1) = S.union (bSet v e0) (bSet v e1)
bSet v (Disj e0 e1) = S.union (bSet v e0) (bSet v e1)
bSet v e@(Less e0 e1)
        | isXRight v e  = S.singleton e0
        | otherwise     = S.empty
bSet v _            = S.empty

true :: BExp
true = Less (Lit 0) (Lit 1)

false :: BExp
false = Less (Lit 1) (Lit 0)

pNeg :: Int -> BExp -> BExp
pNeg v (Not e)          = Not (pNeg v e)
pNeg v (Conj e0 e1)     = Conj (pNeg v e0) (pNeg v e1)
pNeg v (Disj e0 e1)     = Disj (pNeg v e0) (pNeg v e1)
pNeg v e@(Divs _ _)     = e
pNeg v e@(Less e0 e1)   | isXLeft v e   = true
                        | isXRight v e  = false
                        | otherwise     = e

pPos :: Int -> BExp -> BExp
pPos v (Not e)          = Not (pPos v e)
pPos v (Conj e0 e1)     = Conj (pPos v e0) (pPos v e1)
pPos v (Disj e0 e1)     = Disj (pPos v e0) (pPos v e1)
pPos v e@(Divs _ _)     = e
pPos v e@(Less e0 e1)   | isXLeft v e   = false
                        | isXRight v e  = true
                        | otherwise     = e

disjList :: [AExp] -> Int -> BExp -> BExp
disjList [] _ _     = false
disjList (x:xs) v e =
    (Disj   (subst e (M.fromList [(v, x)]))
            (disjList xs v e))

cross :: [a] -> [b] -> [(a, b)]
cross [] _      = []
cross (x:xs) ys = (aux x ys) ++ (cross xs ys)
    where   aux x []        = []
            aux x (y:ys)    = (x, y):(aux x ys)


elimVA :: Int -> BExp -> AB -> [Integer] -> BExp
elimVA v e as js = (Disj
    (disjList (map Lit js) v (pPos v e))
    (disjList (map mkAdd (cross js (S.toList as))) v e)
    )
    where mkAdd (x, y) = Add (Lit (-x)) y

elimVB :: Int -> BExp -> AB -> [Integer] -> BExp
elimVB v e bs js = (Disj
    (disjList (map Lit js) v (pNeg v e))
    (disjList (map mkAdd (cross js (S.toList bs))) v e)
    )
    where mkAdd (x, y) = Add (Lit x) y

elimV2 :: Int -> BExp -> BExp
elimV2 v e = 
    (case S.size as < S.size bs of
        True    -> elimVA v e as [1..delta]
        False   -> elimVB v e bs [1..delta])
    where
            delta = lcmList (divisors v e)
            as = aSet v e
            bs = bSet v e

elimV :: Int -> BExp -> BExp
elimV v = simpB . (elimV2 v) . (elimV1 v) . (norm v)

elimVAll :: BExp -> BExp
elimVAll e = (foldr elimV e) . S.toList . fvBExp $ e

-- | Return True if formula is satisfiable, False if not.
cooperSat :: BExp -> Bool
cooperSat = eval . elimVAll . simpB
