
module Anf_Talk(
  main,example,transformedExample,
  Exp(..),Anf(..),Atom(..),Oper(..),Op(..),
  eval,evalByMachine,evalAnf,
  translateN,
  translate
  ) where

import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Data.Maybe (fromJust)

main :: IO ()
main = putStrLn "*anf-talk*"


{-
our running example:

  (a*b*c - d*e*f) ^2 + 1

no square-op, so use multiply:

  (a*b*c - d*e*f) * (a*b*c - d*e*f) + 1

avoid repeated code with let:

  let x = (a*b*c - d*e*f) in x*x + 1

this is our running example.
-}
example :: Exp
example = undefined -- ELet "x" (...) (EBin Add (EBin Mul (EVar "x") (EVar "x")) (ENum 1.0))


type Identifier = String
type Number = Double

data Exp
  = EVar Identifier
  | ENum Number
  | EBin Op Exp Exp
  | ELet Identifier Exp Exp

data Op = Add | Sub | Mul


{-
running example, transformed by hand to ANF, by introduction of new let bindings

  let ab = a * b
  let abc = ab * c
  let de = d * e
  let def = de * f
  let x = abc - def
  let xx = x * x
  xx + 1
-}
transformedExample :: Anf
transformedExample = undefined


data Anf -- an expression in A-Normal-Form
  = ALet Identifier Oper Anf
  | AOper Oper

data Oper -- a single binary operation; both arguments are atomic
  = ABin Op Atom Atom
  | AAtom Atom

data Atom -- an atomic expression; the value is immediate during evlaution
  = AVar Identifier
  | ANum Number


{-
Simple (recursive) expression evaluator
-}

type Value = Number
type Env = Map Identifier Value -- "q"

eval :: Env -> Exp -> Value
eval q = \case
  EVar x -> fromJust $ Map.lookup x q
  ENum n -> n
  EBin op e1 e2 -> evalOp op (eval q e1) (eval q e2)
  ELet x rhs body -> let v = eval q rhs in eval (Map.insert x v q) body

evalOp :: Op -> Value -> Value -> Value
evalOp = \case
  Add -> (+)
  Sub -> (-)
  Mul -> (*)


{-
Expression evaluation by "CEK" style machine. No Recursion.
"What to do next" is made explicit by continuation component.
-}

type Machine = (Control,Env,Kont)
data Control = ControlE Exp | ControlV Value
data Kont
  = Kdone
  | KbinArg2 Env Op Exp Kont     -- save ARG-2 of a bin-op, while evaluating ARG-1
  | KbinOp Value Op Kont         -- save evaluated-value of ARG-1 of a bin-op, while evaluating the ARG-2
  | Klet Identifier Env Exp Kont -- save the BODY of a let-expression, while evaluating the RHS

evalByMachine :: Env -> Exp -> Value
evalByMachine q0 exp0 = run (ControlE exp0, q0, Kdone)
  where
    run :: Machine -> Value
    run (c,q,k) = case c of
      ControlV value ->
        case k of
          Kdone -> value -- finished!
          KbinArg2 q op e2 k -> run (ControlE e2, q, KbinOp value op k)
          KbinOp v1 op k -> run (ControlV (evalOp op v1 value), q, k)
          Klet x q body k  -> run (ControlE body, Map.insert x value q, k)
      ControlE exp ->
        case exp of
          EVar x -> run (ControlV (fromJust $ Map.lookup x q), q, k)
          ENum n -> run (ControlV n, q, k)
          EBin op e1 e2 -> run (ControlE e1, q, KbinArg2 q op e2 k)
          ELet x rhs body -> run (ControlE rhs, q, Klet x q body k)



{-
ANF-expression evaluation by machine. No Recursion. No continuations either!
-}

evalAnf :: Env -> Anf -> Value
evalAnf = run
  where
    run :: Env -> Anf -> Value
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



{-
Try (and fail) to code simple translation from Exp to Anf
-}

translateN :: Exp -> Anf
translateN = \case
  ELet x rhs body -> ALet x (translateO rhs) (translateN body)
  exp -> AOper (translateO exp)

translateO :: Exp -> Oper
translateO = \case
  EVar x -> AAtom (AVar x)
  ENum n -> AAtom (ANum n)
  EBin op e1 e2 -> ABin op (translateA e1) (translateA e2)
  ELet x rhs body -> do
    let oper = translateO rhs
    let anf = translateN body
    let _result = ALet x oper anf
    undefined -- PROBLEM 1

translateA :: Exp -> Atom
translateA = \case
  EVar x -> AVar x
  ENum n -> ANum n
  exp -> do
    let op = translateO exp
    let x = freshVar()
    let body = undefined -- PROBLEM 2
    let _wrap = ALet x op body
    AVar x

freshVar :: () -> Identifier
freshVar () = undefined




{-
Translate Exp to Anf, by coding in CPS style.
Then the problem cases are dealt with by using the continuation parameter in
non-tail position
-}

type Res = Anf
type K a = (a -> Res) -> Res

translate :: Exp -> Anf
translate exp = transformN exp $ \anf -> anf

transformN :: Exp -> K Anf
transformN exp0 k = case exp0 of
  ELet x rhs body ->
    transformO rhs $ \oper ->
    transformN body $ \anf ->
    k (ALet x oper anf)
  exp ->
    transformO exp $ \oper ->
    k (AOper oper)

transformO :: Exp -> K Oper
transformO exp k = case exp of
  EVar x -> k (AAtom (AVar x))
  ENum n -> k (AAtom (ANum n))
  EBin op e1 e2 ->
    transformA e1 $ \a1 ->
    transformA e2 $ \a2 ->
    k (ABin op a1 a2)
  ELet x rhs body ->
    transformO rhs $ \oper ->
    ALet x oper (transformO body k) -- SOLUTION 1 -- non-tail use of k

transformA :: Exp -> K Atom
transformA exp k = case exp of
  EVar x -> k (AVar x)
  ENum n -> k (ANum n)
  exp -> do
    transformO exp $ \oper -> do
    let x = freshVar()
    let body = k (AVar x) -- SOLUTION 2 -- non-tail use of k
    ALet x oper body
