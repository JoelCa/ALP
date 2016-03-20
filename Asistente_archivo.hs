module Asistente_archivo where

import Data.List
import Common
import Asistente_PP
import Text.PrettyPrint.HughesPJ

habitar :: Type -> [Tactics] -> Maybe Term
habitar = habitar' []

habitar' :: Context -> Type -> [Tactics] -> Maybe Term
habitar' c t [Assumption] = do i <- t `elemIndex` c
                               return $ Bound i
habitar' c (Fun t1 t2) (Intro:ts) = do x <- habitar' (t1:c) t2 ts
                                       return $ Lam t1 x
habitar' c t ((Apply f):ts) = do (t1,_) <- getType (c !! f)
                                 x <- habitar' c t1 ts
                                 return $ (Bound f) :@: x
                                    where getType (Fun t' t'')
                                            | t'' == t = Just (t',t'')
                                            | otherwise = Nothing
                                          getType _ = Nothing
habitar' _ _ _ = Nothing

eval :: Type -> [Tactics] -> Doc
eval ty tacs = maybe (text "Error") (\x -> printTerm x) $ habitar ty tacs
