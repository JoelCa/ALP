module ProofState where

import Common
import Control.Monad.State.Lazy (get, modify)
import qualified Data.Sequence as S

getAttribute :: (ProofConstruction -> [a]) -> Proof a
getAttribute f = do ps <- get
                    let x = f ps
                    if null x
                      then throw PSE
                      else return $ head x

getType :: Proof (Maybe (Type, TType))
getType = getAttribute ty

getTermContext :: Proof TermContext
getTermContext = getAttribute termContexts

getBTypeContext :: Proof BTypeContext
getBTypeContext = getAttribute bTContexts

getLevelSubp :: (Int -> Maybe Int) -> Proof (Maybe Int)
getLevelSubp f = do ps <- get
                    let x = lsubp ps
                    if null x
                      then return $ Nothing
                      else return $ f (head x)

getOpers :: Proof [String]
getOpers = do ps <- get
              return $ opers $ cglobal $ ps

getTeorems :: Proof Teorems
getTeorems = do ps <- get
                return $ teorems $ cglobal $ ps

getFTypeContext :: Proof FTypeContext
getFTypeContext = do ps <- get
                     return $ fTContext $ cglobal $ ps

getTVars :: Proof Int
getTVars = getAttribute tvars

getTTermVars :: Proof Int
getTTermVars = do c <- getAttribute termContexts
                  return $ S.length c

getTBTypeVars :: Proof Int
getTBTypeVars = do tc <- getAttribute bTContexts
                   return $ S.length tc

incrementTVars :: (Int -> Int) -> Proof ()
incrementTVars f = modify $ incrementTVars' f
  
incrementTVars' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
incrementTVars' f ps@(PConstruction {tvars=n:ns}) = ps {tvars = (f n) : ns}

addTermContext :: TermVar -> Proof ()
addTermContext x = modify (addTermContext' x)

addTermContext' :: TermVar -> ProofConstruction -> ProofConstruction
addTermContext' x ps@(PConstruction {termContexts=c:cs})= ps {termContexts = (x S.<| c ):cs}

addBTypeContext :: BTypeVar -> Proof ()
addBTypeContext x = modify (addBTypeContext' x)

addBTypeContext' :: BTypeVar -> ProofConstruction -> ProofConstruction
addBTypeContext' x ps@(PConstruction {bTContexts=tc:tcs})= ps {bTContexts = (x S.<| tc):tcs}

replaceType :: (Type, TType) -> Proof ()
replaceType x = modifyType (\tys -> Just x : tail tys)

modifyTotalSubp :: (Int -> Int) -> Proof ()
modifyTotalSubp f = modify (\ps -> ps {tsubp = f $ tsubp ps})

modifyTVars :: ([Int] -> [Int]) -> Proof ()
modifyTVars f = modify (\ps -> ps {tvars = f $ tvars ps})

modifyBTypeCont :: ([BTypeContext] -> [BTypeContext]) -> Proof ()
modifyBTypeCont f = modify (\ps -> ps {bTContexts = f $ bTContexts ps})

modifyTermContext :: ([TermContext] -> [TermContext]) -> Proof ()
modifyTermContext f = modify (\ps -> ps {termContexts = f $ termContexts ps})

modifyTerm :: ([SpecialTerm] -> [SpecialTerm]) -> Proof ()
modifyTerm f = modify (\ps -> ps {term = f $ term ps})

modifyType :: ([Maybe (Type, TType)] -> [Maybe (Type, TType)]) -> Proof ()
modifyType f = modify (\ps -> ps {ty = f $ ty ps})

modifyLevelSubp :: Int -> Proof ()
modifyLevelSubp n
  | (n > 1) || (n == 0) = modify $ modifyLevelSubp' n
  | n == 1 = error "error: modifySubPLevel."

modifyLevelSubp' :: Int -> ProofConstruction -> ProofConstruction
modifyLevelSubp' 0 ps@(PConstruction {lsubp=s:spl})
  | s > 1 = ps {lsubp = (s-1) : spl}
  | s == 1 = case spl of
               [] -> ps {lsubp = []}
               x:xs -> ps {lsubp = (x-1):xs}
modifyLevelSubp' 1 _ = error "error: modifySubPLevel'."
modifyLevelSubp' x ps@(PConstruction {lsubp=s:spl})
  | s > 1 = ps {lsubp = x : s : spl}
  | s == 1 = ps {lsubp = x :  spl}

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
      do modifyTotalSubp (+ (n-1))
         modifyLevelSubp n
         modifyTVars $ repeatHead 1
         modifyBTypeCont $ repeatHead 1
         modifyTermContext $ repeatHead 1
         modifyType (\tys -> f $ tail tys)
  | n == 0 =
      do modifyTotalSubp (+ (n-1))
         modifyLevelSubp n
         modifyType (\tys -> f $ tail tys)
         w <- getLevelSubp (\x -> if x == 1 then Nothing else Just x)
         case w of
           Nothing ->
             do modifyTVars tail
                modifyBTypeCont tail
                modifyTermContext tail
           Just _ -> 
             do modifyTVars $ repeatHead 1 . tail
                modifyBTypeCont $ repeatHead 1 . tail
                modifyTermContext $ repeatHead 1 . tail
  | n == 1 = modifyType (\tys -> f $ tail tys)
