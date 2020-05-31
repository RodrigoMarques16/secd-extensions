{- -----------------------------------
   Fun: a minimal functional language
   -----------------------------------
   A compiler and interpreter for a SECD-like virtual machine.
   
   Pedro Vasconcelos, 2008--2011.
 -}
module SECD1 where
import           Fun
import           Data.List (elemIndex)
import           Data.Map (Map)
import qualified Data.Map as Map

-----------------------------------------------------------------
-- SECD machine definitions
-----------------------------------------------------------------

-- pseudo instructions 
data Instr = HALT                 -- finished
           | LDC Int              -- load constant
           | LD Int               -- load variable
           | ADD                  -- addition
           | SUB                  -- subtraction
           | MUL                  -- multiplication
           | SEL [Instr] [Instr]  -- select zero/non-zero
           | JOIN                 -- close branch
           | LDF [Instr]          -- load a closure
           | LDRF [Instr]         -- load a recursive closure
           | AP                   -- apply
           | RTN                  -- return 

           | PAIR                 -- pair
           | FST 
           | SND
           
           | CONS String
           | MATCH [(String, Code)]
           
           | REC [(String, Code)]
           | PRJ String
        --    | UNIT

             deriving Show

-- a code block (list of instructions)
type Code = [Instr]

-- closure: pairs of code, environment
type Closure = (Code, Env)

-- closure addresses
type Addr = Int

data StoreValue = SClo  Closure
                | SPair Value Value
                | SCons String Value
                | SRec  [(String, Value)]
                deriving(Show)

-- store for closures
type Store = Map Addr StoreValue

-- get the next available address
nextAddr :: Store -> Addr
nextAddr store = 1 + Map.size store

-- a value of the SECD machine is either
-- a primitive integer or the address of a closure
data Value = I Int
           | A Addr
           | P Int Int
             deriving (Eq,Show)

-- the SECD machine components
type Stack = [Value]

type Env   = [Value]

type Dump  = [(Stack,Env,Code)]

-- the SECD machine configuration
type Conf  = (Stack, Env, Code, Dump, Store)


-- execute a single SECD instruction
execute :: Conf -> Conf

execute (stack, env, (LDC  n):code, dump, store) 
    = (I n:stack, env, code, dump, store)

execute (I v2:I v1:stack, env, ADD:code, dump, store)
    = (I (v1+v2):stack, env, code, dump, store)

execute (I v2:I v1:stack, env, SUB:code, dump, store)
    = (I (v1-v2):stack, env, code, dump, store)

execute (I v2:I v1:stack, env, MUL:code, dump, store)
    = (I (v1*v2):stack, env, code, dump, store)

execute (stack, env, LD i:code, dump, store)
    = let v = env!!i
      in (v:stack, env, code, dump, store)

execute (stack, env, LDF code':code, dump, store)
    = let addr = nextAddr store
          store'= Map.insert addr (SClo (code',env)) store
      in (A addr:stack, env, code, dump, store')

execute (stack, env, LDRF code':code, dump, store)
    = let addr= nextAddr store
          store'=Map.insert addr (SClo (code', A addr:env)) store
      in (A addr:stack, env, code, dump, store')

execute (arg:A addr:stack, env, AP:code, dump, store)
    = let (code', env') = case Map.lookup addr store of
                    Just (SClo (c,e)) -> (c,e)
                    Just _ -> error "applying to non-function"
      in ([], arg:env', code', (stack,env,code):dump, store)

execute (v:stack, env, RTN:code, (stack',env',code'):dump, store)
    = (v:stack', env', code', dump, store)


execute (I n:stack, env, (SEL code1 code2):code, dump,store)
    | n==0      = (stack, env, code1, ([],[],code):dump, store)
    | otherwise = (stack, env, code2, ([],[],code):dump, store)

execute (stack, env, JOIN:code, (_,_,code'):dump, store)
    = (stack, env, code', dump, store)

execute (stack, env, HALT:code, dump, store)
    = (stack, env, [], dump, store)


-------------------------------------------------
--- Pairs ---------------------------------------
-------------------------------------------------

execute (v2:v1:stack, env, PAIR:code, dump, store) 
    = let addr   = nextAddr store
          store' = Map.insert addr (SPair v1 v2) store
      in (A addr:stack, env, code, dump, store')


execute (A addr:stack, env, FST:code, dump, store)
    = let Just (SPair v _) = Map.lookup addr store
      in (v:stack, env, code, dump, store)

execute (A addr:stack, env, SND:code, dump, store) 
    = let Just (SPair _ v) = Map.lookup addr store
      in (v:stack, env, code, dump, store)

-------------------------------------------------
--- Variants / Pattern Matching -----------------
-------------------------------------------------

execute (v:stack, env, CONS l:code, dump, store)
    = let addr   = nextAddr store
          store' = Map.insert addr (SCons l v) store
      in (A addr:stack, env, code, dump, store')

execute (A addr:stack, env, MATCH alts:code, dump, store)
    = let (l,v) = case  Map.lookup addr store of
            Just (SCons l v) -> (l,v)
            _ -> error """Cons expected"
      in case match l alts of 
          Just c -> (stack, v:env, c ++ [JOIN], ([],[],code):dump, store)
          _ -> error "Case not found"

-------------------------------------------------
--- Records -------------------------------------
-------------------------------------------------

-- messy.
-- first we allocate the record
-- then we evaluate each member, in isolation,
-- but gather the resulting heaps and values
-- finally we merge the heaps
-- this mess fixed missing pointers in nested structures

execute (stack, env, REC decls:code, dump, store)
    = let addr          = nextAddr store
          store'        = Map.insert addr (SRec decls') store  
          (decls',heap) = evalRecord decls (stack, env, dump, store')
          store''       = foldl Map.union store' heap
      in (A addr:stack, env, code, dump, store'')
        where evalRecord [] _ = ([],[])
              evalRecord ((name, c):rest) (s,e,d,h)
                = let (v:_,_,_,_,h') = execute (s,e,c,d,h)
                      (decls, heap)  = evalRecord rest (s,e,d,h')
                  in (((name,v):decls), h':heap)
            
                -- = map (\(l, c) -> let (v:_,_,_,_,_) = execute (s,e,c,d,h) in (l, v)) body

execute (A addr:stack, env, PRJ name:code, dump, store)
    = case Map.lookup addr store of
        Just (SRec decls) -> case lookup name decls of
            Just v  -> (v:stack, env, code, dump, store)
            Nothing -> error "field not found"
        _ -> error "record expected"

execute conf
    = error ("execute: undefined for " ++ show conf)


-- execution trace starting from an initial state
executeT :: Conf -> [Conf]
executeT conf = trace
    where confs = iterate execute conf
          trace = takeWhile (not.final) confs
          final (s, e, c, d, st) = null c 


-- run a sequence of machine instructions
-- returns the result value 
run :: Code -> Value
run code = value
    where trace = executeT ([],[],code,[],Map.empty)
          (value:_, _, _, _, _) = last trace


runTrace :: Code -> IO ()
runTrace code = mapM_ (\x -> do print x; putStrLn "") trace
    where trace = executeT ([],[],code,[],Map.empty)

-- valor, máximo comprimento de pilha e do dump
runStats :: Code -> (Value, Int, Int)
runStats code = (value, maxstack, maxdump)
  where trace = executeT ([],[],code,[],Map.empty)
        (value:_, _, _, _, _) = last trace
        maxstack = maximum [length s | (s,_,_,_,_)<-trace]
        maxdump  = maximum [length d | (_,_,_,d,_)<-trace]


-- compile a lambda term into SECD code
compile :: Term -> [Ident] -> [Instr]

compile (Var x) sym 
    = case elemIndex x sym of
        Nothing -> error ("free variable: " ++ show x)
        Just k -> [LD k]
-- "elemIndex x xs" 
-- gives the index of first occurence of x in xs or Nothing 

compile (Lambda x e) sym 
  = let code = compile e (x:sym) ++ [RTN]
    in [LDF code]

-- compile a recursive function
compile (Fix (Lambda f (Lambda x e1))) sym
  = let code = compile e1 (x:f:sym) ++ [RTN]
    in [LDRF code]

compile (App e1 e2) sym 
  = let code1 = compile e1 sym 
        code2 = compile e2 sym 
    in code1 ++ code2 ++ [AP]
       
compile (Const n) sym = [LDC n]

compile (e1 :+ e2) sym 
  = let code1= compile e1 sym 
        code2= compile e2 sym 
    in code1 ++ code2 ++ [ADD]

compile (e1 :- e2) sym 
  = let code1=compile e1 sym
        code2=compile e2 sym 
    in code1 ++ code2 ++ [SUB]

compile (e1 :* e2) sym 
  = let code1 = compile e1 sym 
        code2 = compile e2 sym 
    in code1 ++ code2 ++ [MUL]

compile (IfZero e1 e2 e3) sym
  = let code1 = compile e1 sym 
        code2 = compile e2 sym ++ [JOIN]
        code3 = compile e3 sym ++ [JOIN]
    in code1 ++ [SEL code2 code3]


compile (Let x e1 e2) sym
    = compile (App (Lambda x e2) e1) sym
 
-------------------------------------------------
--- Pairs ---------------------------------------
-------------------------------------------------

compile (Pair e1 e2) sym
    = let code1 = compile e1 sym
          code2 = compile e2 sym
    in code1 ++ code2 ++ [PAIR]

compile (Fst (Pair e _)) sym
    = compile e sym

compile (Fst e) sym
    = let code = compile e sym
      in code ++ [FST]

compile (Snd (Pair _ e)) sym
    = compile e sym

compile (Snd e) sym
    = let code = compile e sym
      in code ++ [SND]

-------------------------------------------------
--- Variants ------------------------------------
-------------------------------------------------

compile (Cons l e) sym
    = let code = compile e sym
      in code ++ [CONS l]  

compile (Case e alts) sym
    = let code  = compile e sym
          alts' = [ (l, compile e' (v:sym)) | (l, v, e') <- alts ]
      in code ++ [MATCH alts']

-------------------------------------------------
--- Records -------------------------------------
-------------------------------------------------

-- compile Unit sym = [UNIT]

-- compile (Rec decls) sym 
--     = let (_, values) = unzip decls
--           paired = foldr (Pair) Unit values
--       in compile paired sym

compile (Rec decls) sym = [REC decls']
    where decls' = map (\(name, value) -> (name, compile value sym)) decls

compile (Sel term name) sym =
    let code = compile term sym
    in  code ++ [PRJ name]

-- compile the main expression
compileMain :: Term ->  [Instr]
compileMain e = compile e [] ++ [HALT]

-- Given a label `l` and a list of (label, code), 
-- find the code labeled `l`
match l [] = Nothing
match l ((l', c):t)
    | l == l'   = Just c
    | otherwise = match l t
