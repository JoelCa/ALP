module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
habitar (PState {position=n, context=c, ty=(t, tw), term=EmptyTerm empTerm}) Assumption =
  do i <- maybeToEither AssuE (findIndex (\x->snd x == tw) c)
     return $ PState {position=n, context=c, ty=(t,tw), term=Term $ empTerm $ Bound i}

habitar (PState {position=n, context=c, ty=(Fun t1 t2, TFun t1' t2'), term=EmptyTerm empTerm}) Intro =
  return $ PState {position=n+1,context=(t1,t1'):c, ty=(t2, t2'), term=EmptyTerm $ empTerm . (\x -> Lam t1 x)}

habitar (PState {position=n, context=c, ty=(ForAll q t, TForAll t'), term=EmptyTerm empTerm}) Intro
  | not $ isFreeType q c = return $ PState {position=n,context=c, ty=(t, t'), term=EmptyTerm $ empTerm . (\x -> BLam q x)}
  | otherwise = throwError IntroE2

habitar _ Intro = throwError IntroE1

habitar st@(PState {position=n,context=c}) (Apply h) = do i <- getHypothesisValue n h
                                                          applyComm i st (c !! (n-i-1))
                                                                                     
habitar (PState {term=Term _}) _ = throwError CommandInvalid

habitar _ _ = error "error: no debería pasar, habitar"


-- Asumimos que las tuplas del 2º arg. de applyComm, tienen la forma correcta.
applyComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
applyComm i (PState {position=n, context=c, ty=(t, t'), term=EmptyTerm empTerm}) (Fun t1 t2, TFun t1' t2')
  | t' == t2' = return $ PState {position=n, context=c, ty=(t1,t1'), term=EmptyTerm $ empTerm . (\x -> (Bound i) :@: x)}
  | otherwise = throwError ApplyE1
applyComm i (PState {position=n, context=c, ty=(t,t'), term=EmptyTerm empTerm}) (ForAll v t1, TForAll t1') =
  do x <- unification t1' t'
     return $ PState {position=n, context=c, ty=(t,t'), term=Term $ empTerm $ (Bound i) :!: x}
applyComm _ _ _ = throwError ApplyE2


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
bottom :: TType
bottom = TForAll $ TBound 0


typeWithoutName :: Type -> TType
typeWithoutName = typeWithoutName' []

typeWithoutName' :: [String] -> Type -> TType
typeWithoutName' xs (B t) = maybe (TFree t) TBound (t `elemIndex` xs)
typeWithoutName' xs (Fun t t') = TFun (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (ForAll v t) = TForAll $ typeWithoutName' (v:xs) t


unification :: TType -> TType -> Either ProofExceptions TType
unification = unif 0 Nothing

unif :: Int -> Maybe TType -> TType -> TType -> Either ProofExceptions TType
unif pos sust t@(TBound n) t'
  | n == pos = case sust of
    Nothing -> maybeToEither Unif (substitution pos t)
    Just s -> if s == t'
              then return s
              else throwError Unif
  | otherwise = if t == t'
                then return $ maybe bottom id sust
                else throwError Unif
unif _ sust (TFree n) (TFree m)
  | n == m = return $ maybe bottom id sust
  | otherwise = throwError Unif
unif pos sust (TFun t1 t1') (TFun t2 t2') = do res <- unif pos sust t1 t2
                                               unif pos (Just res) t1' t2'
unif pos sust (TForAll t) (TForAll t') = unif (pos+1) sust t t'
unif _ _ _ _ = throwError Unif


substitution :: Int -> TType -> Maybe TType
substitution = substitution' 0

substitution' :: Int -> Int -> TType -> Maybe TType
substitution' m n t@(TBound x)
  | x < m = return t
  | x >= n = return $ TBound (x-n)
  | otherwise = Nothing
substitution' _ _ t@(TFree f) = return t
substitution' m n (TFun t t') = do x <- substitution' m n t
                                   y <- substitution' m n t'
                                   return $ TFun x y
substitution' m n (TForAll t) = substitution' (m+1) (n+1) t


--------------------------------------------------------------------


maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x