module Asistente where

import Data.List
import Common
import Control.Monad.Error
import Data.Char (isDigit)

type EmptyTerm = Term->Term

habitar :: (Int, Context, Type, Maybe EmptyTerm) -> Tactic -> Either String (Int, Context, Type, Either Term EmptyTerm)
habitar (n, c, t, Just empTerm) Assumption = do i <- maybeToEither "error: comando assumption mal aplicado" (t `elemIndex` c)
                                                return (n, c,t, Left $ empTerm $ Bound i)
habitar (n, c, Fun t1 t2, Just empTerm) Intro = return (n+1,t1:c,t2, Right $ empTerm . (\x -> Lam t1 x))
habitar (n, c, Fun t1 t2, Nothing) Intro = return (n+1,t1:c,t2, Right (\x -> Lam t1 x))
habitar _ Intro = Left "error: comando intro mal aplicado"
habitar (n, c, t, Just empTerm) (Apply h) = do i <- getHypothesisValue n h
                                               t1 <- getType t (c !! (n-i-1))
                                               return (n,c,t1, Right $ empTerm . (\x -> (Bound i) :@: x))
habitar (n, c, t, Nothing) (Apply h) = do i <- getHypothesisValue n h
                                          t1 <- getType t (c !! (n-i-1))
                                          return (n,c,t1, Right (\x -> (Bound i) :@: x))
habitar (n, c, t,Nothing) _ = Left "error: comando invalido"

-- eval :: Type -> [Tactics] -> Doc
-- eval ty tacs = maybe (text "Error") (\x -> printTerm x) $ habitar ty tacs

getType :: Type -> Type -> Either String Type
getType t (Fun t' t'')
  | t'' == t = Right t'
  | otherwise = Left "error: comando apply mal aplicado, función no coincide tipo"
getType _ _ = Left "error: comando apply mal aplicado, no es función"


getHypothesisValue :: Int -> String -> Either String Int
getHypothesisValue n h
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then Right x
                     else Left "error: hipótesis incorrecta"
  | otherwise = Left "error: hipótesis incorrecta"

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



maybeToEither :: MonadError e m =>
                 e                      -- ^ (Left e) will be returned if the Maybe value is Nothing
              -> Maybe a                -- ^ (Right a) will be returned if this is (Just a)
              -> m a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval