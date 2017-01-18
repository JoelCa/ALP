module ProofState where

import Common
import Control.Monad

newtype StateExceptions a = StateExceptions { runStateExceptions :: ProofState -> Either ProofExceptions (a, ProofState) }

instance Monad StateExceptions where
  return x = StateExceptions (\s -> Right (x, s))
  m >>= f = StateExceptions (\s -> case runStateExceptions m s of
                                     Right (a,b) -> runStateExceptions (f a) b
                                     Left e -> Left e)

get :: StateExceptions ProofState
get = StateExceptions (\s -> Right (s, s))

set :: ProofState -> StateExceptions ()
set s = StateExceptions (\_ -> Right ((), s))  

modify :: (ProofState -> ProofState) -> StateExceptions ()
modify f = StateExceptions (\s -> Right ((), f s))

instance Applicative StateExceptions where
  pure  = return
  (<*>) = ap
              
instance Functor StateExceptions where
  fmap = liftM

class Monad m => MonadException m where
  throw :: ProofExceptions -> m a
  catch :: m a -> (ProofExceptions -> m a) -> m a

instance MonadException StateExceptions where
  throw e = StateExceptions (\_ -> Left e)
  catch m f = StateExceptions (\s -> case runStateExceptions m s of
                                       Left e -> runStateExceptions (f e) s
                                       Right x -> Right x)



getAttribute :: (ProofState -> [a]) -> StateExceptions a
getAttribute f = do ps <- get
                    let x = f ps
                    if null x
                      then throw PSE
                      else return $ head x

getType :: StateExceptions (Maybe (Type, TType))
getType = getAttribute ty

getContext :: StateExceptions Context
getContext = getAttribute context

getPosition :: StateExceptions Int
getPosition = getAttribute position

getTypeContext :: StateExceptions TypeContext
getTypeContext = getAttribute typeContext

addTerm :: ([SpecialTerm] -> [SpecialTerm]) -> StateExceptions ()
addTerm f = modify (\ps -> ps {term = f $ term ps})

incrementPosition :: StateExceptions ()
incrementPosition = modify incrementPosition'
  
incrementPosition' :: ProofState -> ProofState
incrementPosition' ps@(PState {position=n:ns}) = ps {position = (n+1):ns}

addContext :: (Type,TType) -> StateExceptions ()
addContext x = modify (addContext' x)

addContext' :: (Type,TType) -> ProofState -> ProofState
addContext' x ps@(PState {context=c:cs})= ps {context = (x:c):cs}

addTypeContext :: String -> StateExceptions ()
addTypeContext x = modify (addTypeContext' x)

addTypeContext' :: String -> ProofState -> ProofState
addTypeContext' x ps@(PState {typeContext=tc:tcs})= ps {typeContext = (x:tc):tcs}

replaceType :: Maybe (Type, TType) -> StateExceptions ()
replaceType x = modify (\ps -> ps {ty = x : tail (ty ps)})

finishSubProof :: StateExceptions ()
finishSubProof = modify finishSubProof'

finishSubProof' :: ProofState ->  ProofState
finishSubProof' ps@(PState {subp=p,
                            position=n:ns,
                            typeContext=tc:tcs,
                            context=c:cs,
                            ty=ty:tys}) =
  ps {subp=p-1,
      position=ns,
      typeContext=tcs,
      context=cs,
      ty=tys}

------------------------------------------------------------------------------
-- PRUEBA!

-- type PStateExceptions = StateT ProofState (Either ProofExceptions)

-- hola :: State (Int, Int) (Either ProofExceptions (Int, Int))
-- hola = do put (1, 4)
--           s <- get
--           return (return s)
