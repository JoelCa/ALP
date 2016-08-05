module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
--habitar (PState {term=Term _}) _ = error "habitar: no debería pasar"

habitar (PState {position=n:ns, context=c:cs, ty=(t, tw):tys, term=ts}) Assumption =
  do i <- maybeToEither AssuE (findIndex (\x->snd x == tw) c)
     return $ PState {position=ns, context=cs, ty=tys, term=simplifyTerms (Bound i) ts}

habitar (PState {position=n:ns, context=c:cs, ty=(Fun t1 t2, TFun t1' t2'):tys, term=ts}) Intro =
  return $ PState {position=(n+1):ns,context=((t1,t1'):c):cs, ty=(t2, t2'):tys, term=propagateTerm (\x -> Lam t1' x) ts}

-- Arreglar. Si q está libre renombrar para imprimir correctamente las hipótesis
habitar (PState {position=n:ns, context=c:cs, ty=(ForAll q t, TForAll t'):tys, term=ts}) Intro
  | not $ isFreeType q c = return $ PState {position=n:ns,context=c:cs, ty=(t, t'):tys, term=propagateTerm (\x -> BLam x) ts}
  | otherwise = throwError IntroE2

habitar _ Intro = throwError IntroE1

habitar st@(PState {position=n:ns,context=c:cs}) (Apply h) = do i <- getHypothesisValue n h
                                                                applyComm i st (c !! (n-i-1))
                                                          
--habitar st@(PState {position=n, context=c, ty=(And t1 t2, TAnd)d, term=HoleT empTerm:ts}) Split


-- Asumimos que las tuplas del 2º arg. de applyComm, tienen la forma correcta.
applyComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
applyComm i (PState {position=n:ns, context=c:cs, ty=(t, t'):tys, term=ts}) (Fun t1 t2, TFun t1' t2')
  | t' == t2' = return $ PState {position=n:ns, context=c:cs, ty=(t1,t1'):tys, term=propagateTerm (\x -> (Bound i) :@: x) ts}
  | otherwise = throwError ApplyE1
applyComm i (PState {position=n:ns, context=c:cs, ty=(t,t'):tys, term=ts}) (ForAll v t1, TForAll t1') =
  case unification (t1, t1') (t,t') of
    Nothing -> return $ PState {position=ns, context=cs, ty=tys, term=simplifyTerms ((Bound i) :!: bottom) ts}
    Just x -> return $ PState {position=ns, context=cs, ty=tys, term=simplifyTerms ((Bound i) :!: x) ts}
applyComm _ _ _ = throwError ApplyE2


simplifyTerms :: Term -> [SpecialTerm] -> [SpecialTerm]
simplifyTerms t [HoleT et] = [Term $ et t]
simplifyTerms t (DoubleHoleT et):ts = (HoleT $ et t):ts
simplifyTerms t (HoleT et):(DoubleHoleT et'):ts = (HoleT et' $ et $ t):ts

propagateTerm :: (Term->Term) -> [SpecialTerm] -> [SpecialTerm]
propagateTerm et (HoleT et'):ts = (HoleT $ et' . et):ts
propagateTerm et (DoubleHoleT et'):ts = (DoubleHoleT $ et' . et):ts

isFreeType' :: Var -> TType -> Bool
isFreeType' q (TFree p) = q == p
isFreeType' q (TBound p) = False
isFreeType' q (TFun a b) = isFreeType' q a || isFreeType' q b
isFreeType' q (TForAll a) = isFreeType' q a
                
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