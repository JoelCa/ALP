module ProofState where

import Common

getAttribute :: (ProofState -> [a]) -> Proof a
getAttribute f = do ps <- get
                    let x = f ps
                    if null x
                      then throw PSE
                      else return $ head x

getType :: Proof (Maybe (Type, TType))
getType = getAttribute ty

getContext :: Proof Context
getContext = getAttribute context

getPosition :: Proof Int
getPosition = getAttribute position

getTypeContext :: Proof TypeContext
getTypeContext = getAttribute typeContext

incrementPosition :: (Int -> Int) -> Proof ()
incrementPosition f = modify $ incrementPosition' f
  
incrementPosition' :: (Int -> Int) -> ProofState -> ProofState
incrementPosition' f ps@(PState {position=n:ns}) = ps {position = (f n) : ns}

addContext :: (Type,TType) -> Proof ()
addContext x = modify (addContext' x)

addContext' :: (Type,TType) -> ProofState -> ProofState
addContext' x ps@(PState {context=c:cs})= ps {context = (x:c):cs}

addTypeContext :: String -> Proof ()
addTypeContext x = modify (addTypeContext' x)

addTypeContext' :: String -> ProofState -> ProofState
addTypeContext' x ps@(PState {typeContext=tc:tcs})= ps {typeContext = (x:tc):tcs}

replaceType :: (Type, TType) -> Proof ()
replaceType x = modifyType (\tys -> Just x : tail tys)

modifySubP :: (Int -> Int) -> Proof ()
modifySubP f = modify (\ps -> ps {subp = f $ subp ps})

modifyPosition :: ([Int] -> [Int]) -> Proof ()
modifyPosition f = modify (\ps -> ps {position = f $ position ps})

modifyTypeCont :: ([TypeContext] -> [TypeContext]) -> Proof ()
modifyTypeCont f = modify (\ps -> ps {typeContext = f $ typeContext ps})

modifyContext :: ([Context] -> [Context]) -> Proof ()
modifyContext f = modify (\ps -> ps {context = f $ context ps})

modifyTerm :: ([SpecialTerm] -> [SpecialTerm]) -> Proof ()
modifyTerm f = modify (\ps -> ps {term = f $ term ps})

modifyType :: ([Maybe (Type, TType)] -> [Maybe (Type, TType)]) -> Proof ()
modifyType f = modify (\ps -> ps {ty = f $ ty ps})


finishSubProof :: Proof ()
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

-- type PProof = StateT ProofState (Either ProofExceptions)

-- hola :: State (Int, Int) (Either ProofExceptions (Int, Int))
-- hola = do put (1, 4)
--           s <- get
--           return (return s)
