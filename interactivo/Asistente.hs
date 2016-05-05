module Asistente where

import Data.List
import Common
import Data.Char (isDigit)

type EmptyTerm = Term->Term

habitar :: (Int, Context, Type, Maybe EmptyTerm) -> Tactic -> Either ProofExceptions (Int, Context, Type, Either Term EmptyTerm)
habitar (n, c, t, Just empTerm) Assumption = do i <- maybeToEither AssuE (t `elemIndex` c)
                                                return (n, c,t, Left $ empTerm $ Bound i)
habitar (n, c, Fun t1 t2, Just empTerm) Intro = return (n+1,t1:c,t2, Right $ empTerm . (\x -> Lam t1 x))
habitar (n, c, Fun t1 t2, Nothing) Intro = return (n+1,t1:c,t2, Right (\x -> Lam t1 x))
habitar _ Intro = Left IntroE
habitar (n, c, t, Just empTerm) (Apply h) = do i <- getHypothesisValue n h
                                               t1 <- getType t (c !! (n-i-1))
                                               return (n,c,t1, Right $ empTerm . (\x -> (Bound i) :@: x))
habitar (n, c, t, Nothing) (Apply h) = do i <- getHypothesisValue n h
                                          t1 <- getType t (c !! (n-i-1))
                                          return (n,c,t1, Right (\x -> (Bound i) :@: x))
habitar (n, c, t,Nothing) _ = Left CommandInvalid


getType :: Type -> Type -> Either ProofExceptions Type
getType t (Fun t' t'')
  | t'' == t = Right t'
  | otherwise = Left ApplyE1
getType _ _ = Left ApplyE2


getHypothesisValue :: Int -> String -> Either ProofExceptions Int
getHypothesisValue n h
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then Right x
                     else Left ApplyE3
  | otherwise = Left ApplyE3

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



maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x