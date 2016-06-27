module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (elemIndex)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
habitar (PState {position=n, context=c, ty=t, term=EmptyTerm empTerm}) Assumption = do i <- maybeToEither AssuE (t `elemIndex` c)
                                                                                       return (PState {position=n, context=c, ty=t, term=Term $ empTerm $ Bound i})
habitar (PState {position=n, context=c, ty=Fun t1 t2, term=EmptyTerm empTerm}) Intro = return (PState {position=n+1,context=t1:c, ty=t2, term=EmptyTerm $ empTerm . (\x -> Lam t1 x)})
habitar _ Intro = throwError IntroE
habitar (PState {position=n,context=c, ty=t, term=EmptyTerm empTerm}) (Apply h) = do i <- getHypothesisValue n h
                                                                                     t1 <- getType t (c !! (n-i-1))
                                                                                     return (PState {position=n, context=c, ty=t1, term=EmptyTerm $ empTerm . (\x -> (Bound i) :@: x)})
habitar (PState {position=n, context=c, ty=t, term=Term _}) _ = throwError CommandInvalid


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



maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x