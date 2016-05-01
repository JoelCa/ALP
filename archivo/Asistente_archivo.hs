module Asistente_archivo where

import Data.List
import Common
import Asistente_PP
import Text.PrettyPrint.HughesPJ

habitar :: Type -> [Tactics] -> Maybe Term
habitar = habitar' -1 [] []

habitar' :: NumberVars -> SpecialRename -> Context -> Type -> [Tactics] -> Maybe Term
habitar' c t [Assumption] = do i <- t `elemIndex` c
                               return $ Bound i
habitar' vs c (Fun t1 t2) ((Intro Nothing):ts) = do x <- habitar' vs ((Nothing,t1):c) t2 ts
                                                    return $ Lam t1 x
habitar' vs c (Fun t1 t2) ((Intro (Just var)):ts) = if isValidRename c var
                                                    then do x <- habitar' vs ((Just var,t1):c) t2 ts
                                                            return $ Lam t1 x
                                                    else Nothing
habitar' c t ((Apply f):ts) = do (t1,_) <- getType (c !! f)
                                 x <- habitar' c t1 ts
                                 return $ (Bound f) :@: x
                                    where getType (Fun t' t'')
                                            | t'' == t = Just (t',t'')
                                            | otherwise = Nothing
                                          getType _ = Nothing
habitar' _ _ _ = Nothing


isValidRename :: Context -> NumberVars -> Var -> Bool
isValidRename c n v = if isDefaultVar v
                      then let value = getValue v
                           in if isValidValue n value
                      else True

isDefaultVar :: Var -> Bool
isDefaultVar ('H':xs) = isNumber xs
isDefaultVar _ = False

isNumber :: String -> Bool
isNumber [x] = isDigit x
isNumber (x:xs) = (isDigit x) && (isNumber xs)
isNumber [] = False

getValue :: Var -> Int
getValue (x:xs) = read xs :: Int
getValue _ = undefined

isValidValue :: NumberVars -> Int -> Bool
isValidValue n value = (value >= 0) && (value < n)


eval :: Type -> [Tactics] -> Doc
eval ty tacs = maybe (text "Error") (\x -> printTerm x) $ habitar ty tacs
