module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (elemIndex)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
habitar (PState {position=n, context=c, ty=t, term=EmptyTerm empTerm}) Assumption = do i <- maybeToEither AssuE (t `elemIndex` c)
                                                                                       return $ PState {position=n, context=c, ty=t, term=Term $ empTerm $ Bound i}
                                                                                       
habitar (PState {position=n, context=c, ty=Fun t1 t2, term=EmptyTerm empTerm}) Intro = return $ PState {position=n+1,context=t1:c, ty=t2, term=EmptyTerm $ empTerm . (\x -> Lam t1 x)}

habitar (PState {position=n, context=c, ty=ForAll q t, term=EmptyTerm empTerm}) Intro = if not $ isFreeType q c
                                                                                        then return $ PState {position=n,context=c, ty=t, term=EmptyTerm $ empTerm . (\x -> BLam q x)}
                                                                                        else throwError IntroE2
                                                                                             
habitar _ Intro = throwError IntroE1

habitar (PState {position=n,context=c, ty=t, term=EmptyTerm empTerm}) (Apply h) = do i <- getHypothesisValue n h
                                                                                     t1 <- getType t (c !! (n-i-1))
                                                                                     return (PState {position=n, context=c, ty=t1, term=EmptyTerm $ empTerm . (\x -> (Bound i) :@: x)})
                                                                                     
habitar (PState {position=n, context=c, ty=t, term=Term _}) _ = throwError CommandInvalid


isFreeType' :: Var -> Type -> Bool
isFreeType' q (B p) = q == p
isFreeType' q (Fun a b) = isFreeType' q a || isFreeType' q b
isFreeType' q (ForAll p a)
  | q == p = False
  | otherwise = isFreeType' q a
                
isFreeType :: Var -> Context -> Bool
isFreeType q [] = False
isFreeType q (x:xs) = isFreeType' q x || isFreeType q xs


getType :: Type -> Type -> Either ProofExceptions Type
getType t (Fun t' t'')
  | t'' == t = return t'
  | otherwise = throwError ApplyE1
getType _ _ = throwError ApplyE2


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

typeWithoutName :: Type -> TType
typeWithoutName = typeWithoutName' []

typeWithoutName' :: [String] -> Type -> TType
typeWithoutName' xs (B t) = TB $ maybe (Global t) Quote (t `elemIndex` xs)
typeWithoutName' xs (Fun t t') = TFun (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (ForAll v t) = TForAll $ typeWithoutName' (v:xs) t


unification :: TType -> TType -> Either String TType
unification = unif 0 Nothing

unif :: Int -> Maybe TType -> TType -> TType -> Either String TType
unif pos (Just (TB (Quote 0))) t t' = unif pos Nothing t t'
unif pos sust t@(TB (Quote n)) t'
  | t == t' = case sust of
    Nothing -> return $ TB $ Quote 0
    Just s -> return s
  | n == pos = case sust of
    Nothing -> if isFreeTypeVar (pos-1) t'
               then throwError $ "no unifican"
               else return t'
    Just s -> if s == t'
              then return s
              else throwError $ "no unifican"
  | otherwise = throwError $ "no unifican"
unif pos sust (TFun t1 t1') (TFun t2 t2') = do res <- unif pos sust t1 t2
                                               unif pos (Just res) t1' t2'
unif pos sust (TForAll t) (TForAll t') = unif (pos+1) sust t t'
unif pos sust t t'
  | t == t' = return $ TB $ Quote 0
  | otherwise = throwError $ "no unifican"


isFreeTypeVar :: Int -> TType -> Bool
isFreeTypeVar n (TB (Quote m)) = n == m
isFreeTypeVar n (TB (Global _)) = False
isFreeTypeVar n (TFun t t') = isFreeTypeVar n t && isFreeTypeVar n t'
isFreeTypeVar n (TForAll t) = isFreeTypeVar (n+1) t


--------------------------------------------------------------------


maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x