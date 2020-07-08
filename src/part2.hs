
-- Try (and fail) to code simple translation from Exp to Anf
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
