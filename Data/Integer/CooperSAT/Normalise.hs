module Data.Integer.CooperSAT.Normalise (nnf) where

import Data.Integer.CooperSAT.Syntax

-- | Convert formula to Negation Normal Form (NNF)
nnf :: BExp -> BExp
nnf e@(Less _ _) = e
nnf e@(Divs _ _) = e
nnf (Not (Conj e0 e1)) =
    Disj (nnf (Not e0)) (nnf (Not e1))
nnf (Not (Disj e0 e1)) =
    Conj (nnf (Not e0)) (nnf (Not e1))
nnf (Not (Not e)) = nnf e
nnf (Conj e0 e1) = Conj (nnf e0) (nnf e1)
nnf (Disj e0 e1) = Disj (nnf e0) (nnf e1)
nnf (Not e) = Not (nnf e)

assert :: String -> Bool -> IO ()
assert _ True = return ()
assert s False = putStr ("fail: " ++ s ++ "\n")

