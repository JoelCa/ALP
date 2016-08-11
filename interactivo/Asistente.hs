module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
--habitar (PState {term=Term _}) _ = error "habitar: no debería pasar"

habitar (PState {subp=p, position=n:ns, context=c:cs, ty=(t, tw):tys, term=ts}) Assumption =
  do i <- maybeToEither AssuE (findIndex (\x->snd x == tw) c)
     return $ PState {subp=p-1, position=ns, context=cs, ty=tys, term=simplify (Bound i) ts}

habitar (PState {subp=p, position=n:ns, context=c:cs, ty=(Fun t1 t2, TFun t1' t2'):tys, term=ts}) Intro =
  return $ PState {subp=p, position=(n+1):ns,context=((t1,t1'):c):cs, ty=(t2, t2'):tys, term=addHT (\x -> Lam t1' x) ts}

-- Arreglar. Si q está libre renombrar para imprimir correctamente las hipótesis
habitar (PState {subp=p, position=ns, context=c:cs, ty=(ForAll q t, TForAll t'):tys, term=ts}) Intro
  | not $ isFreeType q c = return $ PState {subp=p, position=ns,context=c:cs, ty=(t, t'):tys, term=addHT (\x -> BLam x) ts}
  | otherwise = throwError IntroE2

habitar _ Intro = throwError IntroE1

habitar st@(PState {position=n:ns,context=c:cs}) (Apply h) = do i <- getHypothesisValue n h
                                                                applyComm i st (c !! (n-i-1))
                                                          
habitar st@(PState {position=n:ns,context=c:cs}) (Elim h) = do i <- getHypothesisValue n h
                                                               elimComm i st (c !! (n-i-1))
                                                               
habitar (PState {subp=p, position=ns, context=cs, ty=(Or t1 t2 , TOr t1' t2'):tys, term=ts}) CLeft = 
  return $ PState {subp=p, position=ns, context=cs, ty=(t1,t1'):tys, term=addHT (\x -> (Free $ Global "intro_or1") :@: x) ts}

habitar (PState {subp=p, position=ns, context=cs, ty=(Or t1 t2 , TOr t1' t2'):tys, term=ts}) CRight = 
  return $ PState {subp=p, position=ns, context=cs, ty=(t2,t2'):tys, term=addHT (\x -> (Free $ Global "intro_or2") :@: x) ts}

-- Falta agregar "intro_and" al contexto
habitar (PState {subp=p, position=n:ns, context=c:cs, ty=(And t1 t2, TAnd t1' t2'):tys, term=ts}) Split =
  return $ PState {subp=p+1, position=n:n:ns, context=c:c:cs, ty=(t1,t1'):(t2,t2'):tys,
                   term=addDHT (\x y -> (Free $ Global "intro_and") :@: x :@: y) ts}


-- Asumimos que las tuplas del 3º arg. , tienen la forma correcta.
elimComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
elimComm i (PState {subp=p, position=ns, context=cs, ty=(t, t'):tys, term=ts}) (And t1 t2, TAnd t1' t2') =
  return $ PState {subp=p, position=ns, context=cs, ty=(Fun t1 (Fun t2 t), TFun t1' (TFun t2' t')):tys,
                   term=addHT (\x -> (Free $ Global "elim_and") :@: (Bound i) :@: x) ts}
elimComm _ _ _ = throwError ElimE1

applyComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
applyComm i (PState {subp=p, position=ns, context=cs, ty=(t, t'):tys, term=ts}) (Fun t1 t2, TFun t1' t2')
  | t' == t2' = return $ PState {subp=p, position=ns, context=cs, ty=(t1,t1'):tys, term=addHT (\x -> (Bound i) :@: x) ts}
  | otherwise = throwError ApplyE1
applyComm i (PState {subp=p, position=n:ns, context=c:cs, ty=(t,t'):tys, term=ts}) (ForAll v t1, TForAll t1') =
  do r <- unification (t1, t1') (t,t')
     case r of
       Nothing -> return $ PState {subp=p-1, position=ns, context=cs, ty=tys, term=simplify ((Bound i) :!: bottom) ts}
       Just x -> return $ PState {subp=p-1, position=ns, context=cs, ty=tys, term=simplify ((Bound i) :!: x) ts}
applyComm _ _ _ = throwError ApplyE2

intro_and :: TType -> TType -> Term
intro_and t1' t2' = Lam t1' $ Lam t2' $ BLam $ Lam (TFun t1' (TFun t2' (TBound 0))) (((Bound 0) :@: (Bound 2)) :@: (Bound 1))

simplify :: Term -> [SpecialTerm] -> [SpecialTerm]
simplify t [HoleT et] = [Term $ et t]
simplify t ((DoubleHoleT et):ts) = (HoleT $ et t):ts
simplify t ((HoleT et):(DoubleHoleT et'):ts) = (HoleT $ (et' . et) t):ts

addHT :: (Term->Term) -> [SpecialTerm] -> [SpecialTerm]
addHT et ((HoleT et'):ts) = (HoleT $ et' . et):ts
addHT et ((DoubleHoleT et'):ts) = (DoubleHoleT $ et' . et):ts

addDHT :: (Term->Term->Term) -> [SpecialTerm] -> [SpecialTerm]
addDHT et ((HoleT et'):ts) = (DoubleHoleT $ (\f -> et' . f) . et):ts
addDHT et ((DoubleHoleT et'):ts) = (DoubleHoleT et):(DoubleHoleT et'):ts


isFreeType' :: Var -> TType -> Bool
isFreeType' q (TFree p) = q == p
isFreeType' q (TBound p) = False
isFreeType' q (TFun a b) = isFreeType' q a || isFreeType' q b
isFreeType' q (TForAll a) = isFreeType' q a
isFreeType' q (TAnd a b) = isFreeType' q a || isFreeType' q b

isFreeType :: Var -> Context -> Bool
isFreeType q = foldl (\r x -> isFreeType' q (snd x) || r) False


getHypothesisValue :: Int -> String -> Either ProofExceptions Int
getHypothesisValue n h
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then return x
                     else throwError ApplyE3
  | otherwise = throwError ApplyE3

isDefault :: String -> Bool
isDefault ('H':xs) = isNumber xs
isDefault _ = False

isNumber :: String -> Bool
isNumber [x] = isDigit x
isNumber (x:xs) = (isDigit x) && (isNumber xs)
isNumber [] = False

getValue :: String -> Int
getValue (x:xs) = read xs :: Int
getValue _ = undefined

isValidValue :: Int -> Int -> Bool
isValidValue n value = (value >= 0) && (value < n)

--------------------------------------------------------------------

bottom :: (Type, TType)
bottom = (ForAll "a" (B "a"), TForAll (TBound 0))


typeWithoutName :: Type -> TType
typeWithoutName = typeWithoutName' []

typeWithoutName' :: [String] -> Type -> TType
typeWithoutName' xs (B t) = maybe (TFree t) TBound (t `elemIndex` xs)
typeWithoutName' xs (Fun t t') = TFun (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (ForAll v t) = TForAll $ typeWithoutName' (v:xs) t
typeWithoutName' xs (And t t') = TAnd (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (Or t t') = TOr (typeWithoutName' xs t) (typeWithoutName' xs t')


unification :: (Type,TType) -> (Type,TType) -> Either ProofExceptions (Maybe (Type,TType))
unification = unif 0 Nothing

unif :: Int -> Maybe (Type,TType) -> (Type,TType) -> (Type,TType) -> Either ProofExceptions (Maybe (Type,TType))
unif pos sust (t1,t2@(TBound n)) tt@(tt1,tt2)
  | n == pos = case sust of
    Nothing -> maybe (throwError Unif1) (return . return) (substitution pos tt)
    Just (s,s') -> if s' == tt2
                   then return $ Just (s,s')
                   else throwError Unif1
  | otherwise = if t2 == tt2
                then return $ sust
                else throwError Unif2
unif _ sust (t1,TFree n) (tt1,TFree m)
  | n == m = return sust
  | otherwise = throwError Unif3
unif pos sust (Fun t1 t2,TFun t1' t2') (Fun tt1 tt2, TFun tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (And t1 t2,TAnd t1' t2') (And tt1 tt2, TAnd tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (Or t1 t2,TOr t1' t2') (Fun tt1 tt2, TFun tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (ForAll _ t, TForAll t') (ForAll _ tt, TForAll tt') = unif (pos+1) sust (t,t') (tt,tt')
unif _ _ _ _ = throwError Unif4


substitution :: Int -> (Type, TType) -> Maybe (Type, TType)
substitution = substitution' 0

substitution' :: Int -> Int -> (Type, TType) -> Maybe (Type, TType)
substitution' m n (t,t'@(TBound x))
  | x >= n = return (t,TBound (x-n))
  | x < m = return (t,t')
  | otherwise = Nothing
substitution' _ _ (t, t'@(TFree f)) = return (t,t')
substitution' m n (Fun t1 t2,TFun t1' t2') = do (x,x') <- substitution' m n (t1,t1')
                                                (y,y') <- substitution' m n (t2,t2')
                                                return (Fun x y, TFun x' y')
substitution' m n (ForAll v t, TForAll t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
                                                return (ForAll v x, TForAll x')


--------------------------------------------------------------------


maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x