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

getSubPLevel :: (Int -> Maybe Int) -> Proof (Maybe Int)
getSubPLevel f = do ps <- get
                    let x = subplevel ps
                    if null x
                      then return $ Nothing
                      else return $ f (head x)

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

modifySubPLevel :: Int -> Proof ()
modifySubPLevel n
  | (n > 1) || (n == 0) = modify $ modifySubPLevel' n
  | n == 1 = error "error: modifySubPLevel."

modifySubPLevel' :: Int -> ProofState -> ProofState
modifySubPLevel' 0 ps@(PState {subplevel=s:spl})
  | s > 1 = ps {subplevel = (s-1) : spl}
  | s == 1 = case spl of
               [] -> ps {subplevel = []}
               x:xs -> ps {subplevel = (x-1):xs}
modifySubPLevel' 1 _ = error "error: modifySubPLevel'."
modifySubPLevel' x ps@(PState {subplevel=s:spl})
  | s > 1 = ps {subplevel = x : s : spl}
  | s == 1 = ps {subplevel = x :  spl}

-- finishSubProof :: Proof ()
-- finishSubProof = modify finishSubProof'

-- finishSubProof' :: ProofState ->  ProofState
-- finishSubProof' ps@(PState {subp=p,
--                             position=n:ns,
--                             typeContext=tc:tcs,
--                             context=c:cs,
--                             ty=ty:tys}) =
--   ps {subp=p-1,
--       position=ns,
--       typeContext=tcs,
--       context=cs,
--       ty=tys}

------------------------------------------------------------------------------

repeatHead :: Int -> [a] -> [a]
repeatHead _ [] = error "error: repeatHead 1."
repeatHead n xs
  | n == 0 = xs
  | n > 0 = head xs : (repeatHead (n-1) xs )
  | n < 0 = error "error: repeatHead 2."

modifySubProofs :: Int -> ([Maybe (Type, TType)] -> [Maybe (Type, TType)]) -> Proof ()
modifySubProofs n f
  | n > 1 =
      do modifySubP (+ (n-1))
         modifySubPLevel n
         modifyPosition $ repeatHead 1
         modifyTypeCont $ repeatHead 1
         modifyContext $ repeatHead 1
         modifyType (\tys -> f $ tail tys)
  | n == 0 =
      do modifySubP (+ (n-1))
         modifySubPLevel n
         modifyType (\tys -> f $ tail tys)
         w <- getSubPLevel (\x -> if x == 1 then Nothing else Just x)
         case w of
           Nothing ->
             do modifyPosition $ tail
                modifyTypeCont $ tail
                modifyContext $ tail
           Just _ -> 
             do modifyPosition $ repeatHead 1 . tail
                modifyTypeCont $ repeatHead 1 . tail
                modifyContext $ repeatHead 1 . tail
  | n == 1 = modifyType (\tys -> f $ tail tys)

    
  -- | n > 1 = 
  --     do modifySubP (+ (n-1))
  --        modifyPosition $ repeatHead 1
  --        modifyTypeCont $ repeatHead 1
  --        modifyContext $ repeatHead 1
  --        modifyType (\tys -> f $ tail tys)
  -- | n == 0 =
  --     do sp <- getSubProof
  --        if sp > 2
  --          then do modifySubP (+ (n-1))
  --                  modifyPosition $ repeatHead 1 . tail
  --                  modifyTypeCont $ repeatHead 1 . tail
  --                  modifyContext $ repeatHead 1 . tail
  --                  modifyType (\tys -> f $ tail tys)
  --          else do modifySubP (+ (n-1))
  --                  modifyPosition $ tail
  --                  modifyTypeCont $ tail
  --                  modifyContext $ tail
  --                  modifyType (\tys -> f $ tail tys)
  --  | n == 1 = modifyType (\tys -> f $ tail tys)

------------------------------------------------------------------------------
-- PRUEBA!

-- type PProof = StateT ProofState (Either ProofExceptions)

-- hola :: State (Int, Int) (Either ProofExceptions (Int, Int))
-- hola = do put (1, 4)
--           s <- get
--           return (return s)
