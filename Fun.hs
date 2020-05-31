{--------------------------------------
  Fun: a minimal functional language
  -------------------------------------

  Fun is a minimal functional language designed to experiment with
  language interpreters and compilers. This module defines the 
  abstract syntax of the language:
   - the only primitive data are integers with primitives +, - and * 
   - if-zero-then-else conditional;
   - single argument lambdas; currying can be used for 
     multiple arguments;
   - single let-definitions; multiple definitions must be 
     translated to nested lets;
   - single recursive function definitions (for simplicity).

  Pedro Vasconcelos, 2008--2012
-}
module Fun where
import Data.List (union, delete)

-- abstract syntax for language terms
data Term = Var Ident               -- variables
          | Lambda Ident Term       -- abstraction
          | App Term Term           -- application
          | Const Int               -- constants 
          | Term :+ Term            -- arithmetic operators
          | Term :- Term
          | Term :* Term
          | IfZero Term Term Term   -- conditional
          | Let Ident Term Term     -- local definition
          | Fix Term                -- fixed-point operator

          | Pair Term Term          -- Pairs
          | Fst Term                -- Left of a pair
          | Snd Term                -- Right of a pair
          
          | Cons Ident Term
          | Case Term [(Ident, Ident, Term)]

          | Rec [(Ident, Term)]
          | Sel Term Ident

          | Unit

            deriving (Eq, Show)

-- indentifiers are just strings
type Ident = String

-- some syntactical definitions
-- list of identifiers with free occurrences in a term
fv :: Term -> [Ident]
fv (Var x)      = [x]
fv (Lambda x e) = delete x (fv e)
fv (App e1 e2)  =  (fv e1) `union` (fv e2)
fv (Const _)    = []
fv (e1 :+ e2)   = fv e1 `union` fv e2
fv (e1 :* e2)   = fv e1 `union` fv e2
fv (e1 :- e2)   = fv e1 `union` fv e2
fv (IfZero e1 e2 e3) = fv e1 `union` fv e2 `union` fv e3
fv (Let x e1 e2) = fv e1 `union` delete x (fv e2)
fv (Fix e)       = fv e
fv (Pair e1 e2)  = (fv e1) `union` (fv e2)
fv (Fst e)       = fv e
fv (Snd e)       = fv e
fv (Cons _ e)    = fv e
fv (Case e m)    = foldl union (fv e) [ fv e' ++ [x] | (_,x,e') <- m ]

-- end of file -------------------------------------------------

