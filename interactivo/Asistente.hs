module Asistente where

import Data.List
import Common
import Control.Monad.Error

type EmptyTerm = Term->Term

habitar :: (Context, Type, Maybe EmptyTerm) -> Tactic -> Either String (Context, Type, Either Term EmptyTerm)
habitar (c, t, Just empTerm) Assumption = do i <- maybeToEither "error: comando assumption mal aplicado" (t `elemIndex` c)
                                             return (c,t, Left $ empTerm $ Bound i)
habitar (c, Fun t1 t2, Just empTerm) Intro = return (t1:c,t2, Right $ empTerm . (\x -> Lam t1 x))
habitar (c, Fun t1 t2, Nothing) Intro = return (t1:c,t2, Right (\x -> Lam t1 x))
habitar _ Intro = Left "error: comando intro mal aplicado"
habitar (c, t, Just empTerm) (Apply f) = do t1 <- getType t (c !! f)
                                            return (c,t1, Right $ empTerm . (\x -> (Bound f) :@: x))
habitar (c, t, Nothing) (Apply f) = do t1 <- getType t (c !! f)
                                       return (c,t1, Right (\x -> (Bound f) :@: x))
habitar (c,t,Nothing) _ = Left "error: comando invalido"

-- eval :: Type -> [Tactics] -> Doc
-- eval ty tacs = maybe (text "Error") (\x -> printTerm x) $ habitar ty tacs

getType :: Type -> Type -> Either String Type
getType t (Fun t' t'')
  | t'' == t = Right t'
  | otherwise = Left "error: comando apply mal aplicado, función no coincide tipo"
getType _ _ = Left "error: comando apply mal aplicado, no es función"


maybeToEither :: MonadError e m =>
                 e                      -- ^ (Left e) will be returned if the Maybe value is Nothing
              -> Maybe a                -- ^ (Right a) will be returned if this is (Just a)
              -> m a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval