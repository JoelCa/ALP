module Asistente where

import Data.List
import Common
import Data.Char (isDigit)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
habitar (PState {position=n, context=c, ty=t, term=EmptyTerm empTerm}) Assumption = do i <- maybeToEither AssuE (t `elemIndex` c)
                                                                                       return (PState {position=n, context=c, ty=t, term=Term $ empTerm $ Bound i})
habitar (PState {position=n, context=c, ty=Fun t1 t2, term=EmptyTerm empTerm}) Intro = return (PState {position=n+1,context=t1:c, ty=t2, term=EmptyTerm $ empTerm . (\x -> Lam t1 x)})
habitar (PState {position=n, context=c, ty=Fun t1 t2, term=Nil}) Intro = return (PState {position=n+1,context=t1:c,ty=t2, term=EmptyTerm (\x -> Lam t1 x)})
habitar _ Intro = Left IntroE
habitar (PState {position=n,context=c, ty=t, term=EmptyTerm empTerm}) (Apply h) = do i <- getHypothesisValue n h
                                                                                     t1 <- getType t (c !! (n-i-1))
                                                                                     return (PState {position=n, context=c, ty=t1, term=EmptyTerm $ empTerm . (\x -> (Bound i) :@: x)})
habitar (PState {position=n, context= c, ty= t, term=Nil}) (Apply h) = do i <- getHypothesisValue n h
                                                                          t1 <- getType t (c !! (n-i-1))
                                                                          return (PState {position=n, context=c, ty=t1, term=EmptyTerm (\x -> (Bound i) :@: x)})
habitar (PState {position=n, context=c, ty=t, term=Nil}) _ = Left CommandInvalid


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