module ProofState where

import Common
import Control.Monad.State.Lazy

newtype StateExceptions a = StateExceptions { runStateExceptions :: ProofState -> Either ProofExceptions (a, ProofState) }

instance Monad StateExceptions where
  return x = StateExceptions (\s -> Right (x, s))
  m >>= f = StateExceptions (\s -> case runStateExceptions m s of
                                     Right (a,b) -> runStateExceptions (f a) b
                                     Left e -> Left e)

instance Applicative StateExceptions where
  pure  = return
  (<*>) = ap
              
instance Functor StateExceptions where
  fmap = liftM

class Monad m => MonadException m where
  throw :: ProofExceptions -> m a

instance MonadException StateExceptions where
  throw e = StateExceptions (\_ -> Left e)


getType :: ProofState -> Either ProofExceptions (Maybe (Type, TType))
getType ps = let x = ty ps
             in if null x
                then throwError PSE
                else return $ head x

getContext :: ProofState -> Either ProofExceptions Context
getContext ps = let x = context ps
                in if null x
                   then throwError PSE
                   else return $ head x

getPosition :: ProofState -> Either ProofExceptions Int
getPosition ps = let x = position ps
                 in if null x
                    then throwError PSE
                    else return $ head x

getTypeContext :: ProofState -> Either ProofExceptions TypeContext
getTypeContext ps = let x = typeContext ps
                    in if null x
                       then throwError PSE
                       else return $ head x

addTerm :: ProofState ->  ([SpecialTerm] -> [SpecialTerm]) -> Either ProofExceptions ProofState
addTerm ps f = return $ ps {term = f $ term ps}

incrementPosition :: ProofState -> Either ProofExceptions ProofState
incrementPosition ps@(PState {position=n:ns}) = return $ ps {position = (n+1):ns}

addContext :: ProofState -> (Type,TType) -> Either ProofExceptions ProofState
addContext ps@(PState {context=c:cs}) x = return $ ps {context = (x:c):cs}

replaceType :: ProofState -> Maybe (Type, TType) -> Either ProofExceptions ProofState
replaceType ps x = return $ ps {ty = x : tail (ty ps)}

finishSubProof :: ProofState ->  Either ProofExceptions ProofState
finishSubProof ps@(PState {subp=p,
                           position=n:ns,
                           typeContext=tc:tcs,
                           context=c:cs,
                           ty=ty:tys}) =
  return $ ps {subp=p-1,
               position=ns,
               typeContext=tcs,
               context=cs,
               ty=tys}

throwError :: e -> Either e a
throwError x = Left x


------------------------------------------------------------------------------
-- PRUEBA!

type PStateExceptions = StateT ProofState (Either ProofExceptions)

hola :: State (Int, Int) (Either ProofExceptions (Int, Int))
hola = do put (1, 4)
          s <- get
          return (return s)
