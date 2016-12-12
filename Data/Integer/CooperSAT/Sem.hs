module Data.Integer.CooperSAT.Sem where

import Data.Integer.CooperSAT.Syntax

evalA :: AExp -> Integer
evalA (Lit x)       = x
evalA (Var _)       = error "eval'd unclosed expression"
evalA (Add e0 e1)   = (evalA e0) + (evalA e1)
evalA (Mul c e)     = c*(evalA e)

eval :: BExp -> Bool
eval (Conj e0 e1)   = (eval e0) && (eval e1)
eval (Disj e0 e1)   = (eval e0) || (eval e1)
eval (Not e)        = not (eval e)
eval (Less e0 e1)   = (evalA e0) < (evalA e1)
eval (Divs v e)     = ((evalA e) `mod` v) == 0

