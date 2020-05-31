module Examples where

import Prelude hiding (head, tail, length, either)

import Fun
import SECD1

-- Compile/run in one step
eval = (run . compileMain)

-- Application with two arguments
app2 f e1 e2 = App (App f e1) e2
app3 f e1 e2 e3 = App (App (App f e1) e2) e3

-------------------------------------------------
--- Constants ----------------------------------------
-------------------------------------------------

zero  = Const 0
one   = Const 1
two   = Const 2
three = Const 3
four  = Const 4
five  = Const 5

plusOne = (Lambda "x" ((Const 1) :+ (Var "x")))

minusOne = (Lambda "x" ((Const 1) :- (Var "x")))

-------------------------------------------------
--- Pairs ---------------------------------------
-------------------------------------------------7

-- some constants
pair1  = Pair one two
pair2  = Pair (two :+ one) (two)
triple = Pair zero (Pair one two)

-- (a,b) + (c,d) = (a+c, b+d)
pairSum = (Lambda "x" 
            (Lambda "y" 
                (Pair ((Fst (Var "x")) :+ (Fst (Var "y"))) (Snd (Var "x") :+ (Snd (Var "y"))) )))

testPairSum = (eval $ Fst $ app2 pairSum pair1 pair2) == I 4
           && (eval $ Snd $ app2 pairSum pair1 pair2) == I 4

-- test pairs inside variables
varPair  = (Let "x" (Pair one two) ((Var "x")))

testVarPair = (eval $ (Const 3) :+ (Fst varPair)) == I 4

-- test functions inside pairs
fooPair = (Pair (Lambda "x" ((Var "x") :+ one))
                (Lambda "y" ((Var "y") :- one)))

testFooPair = (eval $ App (Fst fooPair) one) == I 2
           && (eval $ App (Snd fooPair) one) == I 0

-------------------------------------------------
--- Variants ------------------------------------
-------------------------------------------------

left  x = Cons "Left" (Const x)
right x = Cons "Right" (Const x)

testCase = eval $ Case (left 5) [ ("Left",  "x", zero)
                                , ("Right", "y", one) ]

either = (Lambda "f" 
            (Lambda "g" 
                (Lambda "u" (Case (Var "u") [ ("Left",  "x", App (Var "f") (Var "x"))
                                            , ("Right", "y", App (Var "g") (Var "y")) ]))))

testEither = (eval $ app3 either minusOne plusOne (right 1)) == I 2

-------------------------------------------------
--- Lists ---------------------------------------
-------------------------------------------------

nil = Cons "nil" zero

cons = (Lambda "x"
            (Lambda "y" 
                (Cons "list" (Pair (Var "x") (Var "y")))))

empty = (Lambda "x" (Case (Var "x") [ ("nil",  "y", one)
                                    , ("list", "y", zero)]))

head = (Lambda "x" (Case (Var "x") [ ("list", "y", Fst (Var "y")) ]))

tail = (Lambda "x" (Case (Var "x") [ ("list", "y", Snd (Var "y")) ]))

testEmpty = (eval $ App empty nil) == I 1
         && (eval $ App empty $ singleton five) == I 0
         && (eval $ App empty threeL) == I 0

-- List with a single element
singleton x = app2 cons x nil
 
testSingleton = (eval $ App head (singleton five)) == I 5
             && (eval $ (App empty . App tail) (singleton five)) == I 1

-- Length of a list
length = Fix (Lambda "f" 
                (Lambda "x" 
                    (Case (Var "x") [ ("nil", "y", zero)
                                    , ("list", "z", (one :+ (App (Var "f") (App tail (Var "x")))))])))

testLength = (eval $ App length nil) == I 0
          && (eval $ App length oneL) == I 1
          && (eval $ App length threeL) == I 3 


-- Lists of increasing size
oneL   = singleton one
twoL   = app2 cons two   oneL
threeL = app2 cons three twoL
fourL  = app2 cons four  threeL
fiveL  = app2 cons five  fourL

-------------------------------------------------
--- Record --------------------------------------
-------------------------------------------------

recXY = Rec [("x", two), ("y", three)]

testSel = (eval $ Sel recXY "x") == I 2
       && (eval $ Sel recXY "y") == I 3

recNested = Rec [("xy", recXY), ("z", five)]

testNested = (eval $ Sel (Sel recNested "xy") "x") == I 2
          && (eval $ Sel (Sel recNested "xy") "y") == I 3

funcMap = Rec [("plusOne", plusOne), ("minusOne", minusOne)]

testFuncMap = (eval $ App (Sel funcMap "plusOne") one) == I 2
           && (eval $ App (Sel funcMap "minusOne") one) == I 0