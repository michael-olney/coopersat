module RefSolver (refSat) where

import Data.Integer.CooperSAT.Syntax
import Data.Integer.SAT (
    Prop((:||), (:&&), (:<), (:==)),
    Expr((:+), (:*)),
    checkSat
    )
import qualified Data.Integer.SAT as RefSAT

aToRef :: AExp -> RefSAT.Expr
aToRef (Lit k)      = RefSAT.K $ k
aToRef (Var n)      = RefSAT.Var . RefSAT.toName $ n
aToRef (Add x y)    = (aToRef x) :+ (aToRef y)
aToRef (Mul k x)    = k :* (aToRef x)

bToRef :: BExp -> RefSAT.Prop
bToRef (Conj x y)   = (bToRef x) :&& (bToRef y)
bToRef (Disj x y)   = (bToRef x) :|| (bToRef y)
bToRef (Not x)      = RefSAT.Not . bToRef $ x
bToRef (Less x y)   = (aToRef x) :< (aToRef y)
bToRef (Divs k x)   = (RefSAT.Div (aToRef x) k) :== (RefSAT.K 0)

ifNothing Nothing   = False
ifNothing _         = True

refSat :: BExp -> Bool
refSat = ifNothing . checkSat . (flip RefSAT.assert $ RefSAT.noProps) . bToRef

