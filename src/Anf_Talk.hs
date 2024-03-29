(25 rows)

--[0]-----------------------------------------------------------------

-- Module header to keep this talk type correct!

module Anf_Talk (main,
  Exp(..),Anf(..),Atom(..),Oper(..),Op(..),
  eval,evalByMachine,evalAnf,translate
  ) where

import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Data.Maybe (fromJust)

main :: IO ()
main = putStrLn "*anf-talk*"

transformN = undefined transformO
transformO = undefined transformA

freshVar :: () -> Identifier
freshVar = undefined

----------------------------------------------------------------------


--[1]-----------------------------------------------------------------

{- A simple expression language:


        numbers, variables, binary-ops (+) (-) (*)


-- An example:


        (a*b*c - d*e*f) * (a*b*c - d*e*f) + 1


-- Add `let` construct to express shared computations


        let x = (a*b*c - d*e*f)
        x*x + 1



----------------------------------------------------------------------}


--[2]-----------------------------------------------------------------

{- Same example:


        let x = (a*b*c - d*e*f)
        x*x + 1



-- Going crazy with let bindings:


        let ab = a * b
        let abc = ab * c
        let de = d * e
        let def = de * f
        let x = abc - def
        let xx = x * x
        xx + 1


----------------------------------------------------------------------}


--[3]-----------------------------------------------------------------

-- AST for our simple expression language:


type Identifier = String
type Number = Double

data Exp
  = EVar Identifier
  | ENum Number
  | EBin Op Exp Exp
  | ELet Identifier Exp Exp

data Op = Add | Sub | Mul




--      let x = (a*b*c - d*e*f) in x*x + 1   {- The starting example -}


----------------------------------------------------------------------


--[4]-----------------------------------------------------------------

-- Simple (recursive) expression evaluator

type Value = Number
type Env = Map Identifier Value -- "q"


eval :: Env -> Exp -> Value
eval q = \case
  EVar x -> fromJust $ Map.lookup x q
  ENum n -> n
  EBin op e1 e2 -> evalOp op (eval q e1) (eval q e2)
  ELet x rhs body -> let v = eval q rhs in eval (Map.insert x v q) body


evalOp :: Op -> Value -> Value -> Value -- (we reuse this definition later)
evalOp = \case
  Add -> (+)
  Sub -> (-)
  Mul -> (*)

----------------------------------------------------------------------


--[5]-----------------------------------------------------------------

-- Expression evaluation by "CEK" style machine:


-- Small step evaluator makes (cost of) recursion explicit.

type Machine = (Control, Env, Kont)

data Control = ControlE Exp | ControlV Value


-- "Kont" (Continuation) = "What to do next..."
-- And preserve the necessary information to do it.

data Kont
  = Kdone
  | KbinArg2 Env Op Exp Kont     -- save bin-op's ARG-2, while evaluating ARG-1
  | KbinOp Value Op Kont         -- save value of bin-op's ARG-1, while evaluating ARG-2
  | Klet Identifier Env Exp Kont -- save BODY of a let-expression, while evaluating the RHS


----------------------------------------------------------------------


--[6]-----------------------------------------------------------------

-- Evaluation by CEK machine

evalByMachine :: Env -> Exp -> Value
evalByMachine q0 exp0 = run (ControlE exp0, q0, Kdone)
  where
    run :: Machine -> Value     -- run is an iterative process
    run (c,q,k) = case c of
      ControlV value ->
        case k of
          Kdone -> value -- FINISHED!
          KbinArg2 q op e2 k -> run (ControlE e2, q, KbinOp value op k)
          KbinOp v1 op k -> run (ControlV (evalOp op v1 value), q, k)
          Klet x q body k  -> run (ControlE body, Map.insert x value q, k)
      ControlE exp ->
        case exp of
          EVar x -> run (ControlV (fromJust $ Map.lookup x q), q, k)
          ENum n -> run (ControlV n, q, k)
          EBin op e1 e2 -> run (ControlE e1, q, KbinArg2 q op e2 k)
          ELet x rhs body -> run (ControlE rhs, q, Klet x q body k)

----------------------------------------------------------------------


--[7]-----------------------------------------------------------------

{- ANF -- "Administrative Normal Form"


        "The Essence of Compiling with Continuations", Flanagan et al, 1993
                https://users.soe.ucsc.edu/~cormac/papers/pldi93.pdf


  "Only constants and variables may serve as arguments of function applications."
  "Every non-atomic expression must be bound by a let-expression or returned from a function."


-- Here is our example again in ANF form:

        let ab = a * b
        let abc = ab * c
        let de = d * e
        let def = de * f
        let x = abc - def
        let xx = x * x
        xx + 1
----------------------------------------------------------------------}


--[8]-----------------------------------------------------------------

-- AST for A-Normal-form (capture the invariants)



data Anf -- an expression in A-Normal-Form
  = ALet Identifier Oper Anf
  | AOper Oper

data Oper -- a single binary operation; both arguments are atomic
  = ABin Op Atom Atom
  | AAtom Atom

data Atom -- an atomic expression; the value is immediate during evalution
  = AVar Identifier
  | ANum Number





----------------------------------------------------------------------


--[9]-----------------------------------------------------------------

--Evaluation of ANF-expressions by machine. No Recursion. No continuations either!

evalAnf :: Env -> Anf -> Value
evalAnf = run
  where
    run :: Env -> Anf -> Value     -- run is an iterative process
    run q = \case
      ALet x rhs body -> let v = evalOper q rhs in run (Map.insert x v q) body
      AOper op -> evalOper q op

    evalOper :: Env -> Oper -> Value
    evalOper q = \case
      ABin op a1 a2 -> evalOp op (evalAtom q a1) (evalAtom q a2)
      AAtom atom -> evalAtom q atom

    evalAtom :: Env -> Atom -> Value
    evalAtom q = \case
      AVar x -> fromJust $ Map.lookup x q
      ANum n -> n

----------------------------------------------------------------------


--[10]-----------------------------------------------------------------

{- Function application & abstraction, in a PURE language:


        \f -> f A B C
                                -- curried application. Means: ((f A) B) C


-- ANF (is this ok?)

        \f -> let a = A         -- the order of the lets does not matter
              let b = B
              let c = C
              f a b c           -- optimized multi-argument application


-- All good when "f" is a simple function of 3 arguments:

        let f = \x y z -> BODY

                                -- curried abstraction. Means: \x -> \y -> \z -> BODY
----------------------------------------------------------------------}


--[11]-----------------------------------------------------------------

{- But what if... we add effects, and...

        f == \x -> let () = effectX() in
                   \y -> let () = effectY() in
                         \z -> BODY

        A == let () = effectA() in ...
        B == let () = effectB() in ...
        C == let () = effectC() in ...

-- What order are the effects?

        \f -> let a = A
              let b = B
              let c = C
              f a b c
                        --> effects: A, B, C, X, Y

        \f -> f A B C
                        --> ???
----------------------------------------------------------------------}


--[12]-----------------------------------------------------------------

{- Function THEN Argument. "left -> right"  (SML, DAML, ...)


-- (f,A,B,C as before)

        \f -> ((f A) B) C

                        --> effects: A, X, B, Y, C      -- Interleaving: intuitive?

-- ANF (L->R, fixed)


        \f -> let a = A
              let fa = f a              -- Sad :(
              let b = B
              let fab = fa b            -- Sad again :(
              let c = C
              fab c

                        --> effects: A, X, B, Y, C
----------------------------------------------------------------------}


--[13]-----------------------------------------------------------------

{- Argument THEN Function. "right -> left"  (Ocaml, Moscow ML, ...)


-- (f,A,B,C as before)

        \f -> ((f A) B) C

                        --> effects: C, B, A, X, Y

-- ANF (R->L)


        \f -> let c = C
              let b = B
              let a = A
              f a b c

                        --> effects: C, B, A, X, Y


----------------------------------------------------------------------}


--[14]-----------------------------------------------------------------

-- Translation to ANF via CPS style code

type Res = Anf
type K a = (a -> Res) -> Res

translate :: Exp -> Anf
translate exp = transformN exp $ \anf -> anf

transformN :: Exp -> K Anf
transformO :: Exp -> K Oper

transformA :: Exp -> K Atom
transformA exp k = case exp of
  EVar x -> k (AVar x)
  ENum n -> k (ANum n)
  exp -> do
    transformO exp $ \oper -> do
    let x = freshVar()
    let body = k (AVar x)       -- non-tail call of `k`
    ALet x oper body            -- allows let-binding to be wrapped around `body`
----------------------------------------------------------------------
