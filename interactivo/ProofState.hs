module ProofState where

import Common
import Control.Monad.State.Lazy (get, modify)
import Data.Map (Map)

getAttribute :: (ProofConstruction -> [a]) -> Proof a
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

getQuantifier :: Proof Int
getQuantifier = getAttribute quantifier

getTypeContext :: Proof TypeContext
getTypeContext = getAttribute typeContext

getSubPLevel :: (Int -> Maybe Int) -> Proof (Maybe Int)
getSubPLevel f = do ps <- get
                    let x = subplevel ps
                    if null x
                      then return $ Nothing
                      else return $ f (head x)

getOpers :: Proof [String]
getOpers = do ps <- get
              return $ copers ps

getTeorems :: Proof (Map String (Term,(Type,TType)))
getTeorems = do ps <- get
                return $ cteorems ps

incrementPosition :: (Int -> Int) -> Proof ()
incrementPosition f = modify $ incrementPosition' f
  
incrementPosition' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
incrementPosition' f ps@(PConstruction {position=n:ns}) = ps {position = (f n) : ns}

incrementQuantifier :: (Int -> Int) -> Proof ()
incrementQuantifier f = modify $ incrementQuantifier' f
  
incrementQuantifier' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
incrementQuantifier' f ps@(PConstruction {quantifier=n:ns}) = ps {quantifier = (f n) : ns}

addContext :: TypeVar -> Proof ()
addContext x = modify (addContext' x)

addContext' :: TypeVar -> ProofConstruction -> ProofConstruction
addContext' x ps@(PConstruction {context=c:cs})= ps {context = (x:c):cs}

addTypeContext :: String -> Proof ()
addTypeContext x = modify (addTypeContext' x)

addTypeContext' :: String -> ProofConstruction -> ProofConstruction
addTypeContext' x ps@(PConstruction {typeContext=tc:tcs})= ps {typeContext = (x:tc):tcs}

replaceType :: (Type, TType) -> Proof ()
replaceType x = modifyType (\tys -> Just x : tail tys)

modifySubP :: (Int -> Int) -> Proof ()
modifySubP f = modify (\ps -> ps {subp = f $ subp ps})

modifyPosition :: ([Int] -> [Int]) -> Proof ()
modifyPosition f = modify (\ps -> ps {position = f $ position ps})

modifyQuantifier :: ([Int] -> [Int]) -> Proof ()
modifyQuantifier f = modify (\ps -> ps {quantifier = f $ quantifier ps})

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

modifySubPLevel' :: Int -> ProofConstruction -> ProofConstruction
modifySubPLevel' 0 ps@(PConstruction {subplevel=s:spl})
  | s > 1 = ps {subplevel = (s-1) : spl}
  | s == 1 = case spl of
               [] -> ps {subplevel = []}
               x:xs -> ps {subplevel = (x-1):xs}
modifySubPLevel' 1 _ = error "error: modifySubPLevel'."
modifySubPLevel' x ps@(PConstruction {subplevel=s:spl})
  | s > 1 = ps {subplevel = x : s : spl}
  | s == 1 = ps {subplevel = x :  spl}

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
         modifyQuantifier $ repeatHead 1
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
             do modifyQuantifier tail
                modifyPosition tail
                modifyTypeCont tail
                modifyContext tail
           Just _ -> 
             do modifyQuantifier $ repeatHead 1 . tail
                modifyPosition $ repeatHead 1 . tail
                modifyTypeCont $ repeatHead 1 . tail
                modifyContext $ repeatHead 1 . tail
  | n == 1 = modifyType (\tys -> f $ tail tys)
