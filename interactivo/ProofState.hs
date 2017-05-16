module ProofState where

import Common
import Control.Monad.State.Lazy (get, modify)
import qualified Data.Vector as V
import Data.IntSet (IntSet)

-- Operaciones que modifican el estado de la monada Proof.
-- Es decir que, estas operaciones cambian la prueba.

getAttribute :: (SubProof -> a) -> Proof a
getAttribute f = do ps <- get
                    let x = subps ps
                    if null x
                      then throw PSE
                      else return $ f $ head x

getGlobalAttr :: (ProverGlobal -> a) -> Proof a
getGlobalAttr f = do ps <- get
                     return $ f $ cglobal $ ps

getType :: Proof (Maybe (Type, TType))
getType = do t <- getAttribute ty
             return $ head t

getTermContext :: Proof TermContext
getTermContext = getAttribute termContext

getBTypeContext :: Proof BTypeContext
getBTypeContext = getAttribute bTypeContext

getUsrOpers :: Proof FOperations
getUsrOpers = getGlobalAttr opers

getTeorems :: Proof Teorems
getTeorems = getGlobalAttr teorems

getFTypeContext :: Proof FTypeContext
getFTypeContext = getGlobalAttr fTypeContext

getConflictNames :: Proof IntSet
getConflictNames = getGlobalAttr conflict

getTVars :: Proof Int
getTVars = getAttribute tvars

getTTermVars :: Proof Int
getTTermVars = do c <- getAttribute termContext
                  return $ length c

getTBTypeVars :: Proof Int
getTBTypeVars = do tc <- getAttribute bTypeContext
                   return $ length tc

getSubProofLevel :: Proof (Maybe SubProof)
getSubProofLevel = do ps <- get
                      case tail $ subps ps of
                        [] -> return Nothing
                        tsb -> return $ return $ head tsb

modifyTVars :: (Int -> Int) -> Proof ()
modifyTVars = modify . modifyTVars'

modifyTVars' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
modifyTVars' f ps@(PConstruction {subps=sp:sps}) =
  ps {subps = sp {tvars = f $ tvars sp} : sps}
  
addTermContext :: TermVar -> Proof ()
addTermContext = modify . addTermContext'

addTermContext' :: TermVar -> ProofConstruction -> ProofConstruction
addTermContext' x ps@(PConstruction {subps=sp:sps}) =
  ps {subps = sp {termContext = V.cons x (termContext sp)} : sps}

updateTermContext :: Int -> TermVar -> Proof ()
updateTermContext n x = modify $ updateTermContext' n x

updateTermContext' :: Int -> TermVar -> ProofConstruction -> ProofConstruction
updateTermContext' n x ps@(PConstruction {subps=sp:sps}) =
  ps {subps = sp {termContext = V.update (termContext sp) $ V.singleton (n,x)} : sps}

addBTypeContext :: BTypeVar -> Proof ()
addBTypeContext = modify . addBTypeContext'

addBTypeContext' :: BTypeVar -> ProofConstruction -> ProofConstruction
addBTypeContext' x ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {bTypeContext = V.cons x $ bTypeContext sp} : sps}

modifyLevelSubp :: (Int -> Int) -> Proof ()
modifyLevelSubp = modify . modifyLevelSubp'

modifyLevelSubp' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
modifyLevelSubp' f ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {lsubp = f $ lsubp sp} : sps}

modifyTotalSubp :: (Int -> Int) -> Proof ()
modifyTotalSubp f = modify (\ps -> ps {tsubp = f $ tsubp ps})

replaceLevelSubp :: Int -> Proof ()
replaceLevelSubp n = modifyLevelSubp (\_ -> n)

modifyType :: ([Maybe (Type, TType)] -> [Maybe (Type, TType)]) -> Proof ()
modifyType = modify . modifyType'

modifyType' :: ([Maybe (Type, TType)] -> [Maybe (Type, TType)])
           -> ProofConstruction -> ProofConstruction
modifyType' f ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {ty = f $ ty sp} : sps}

replaceMaybeTypes :: [Maybe (Type, TType)] -> Proof ()
replaceMaybeTypes ts = modifyType (\_ -> ts)

replaceType :: (Type, TType) -> Proof ()
replaceType t = modifyType (\_ -> [Just t])

removeFirstType :: Proof ()
removeFirstType = modifyType tail

modifyTerm :: ([SpecialTerm] -> [SpecialTerm]) -> Proof ()
modifyTerm f = modify (\ps -> ps {term = f $ term ps})

modifySubps :: ([SubProof] -> [SubProof]) -> Proof ()
modifySubps f = modify (\ps -> ps {subps = f $ subps ps})

------------------------------------------------------------------------------
-- Crea una subprueba para el tipo objetivo dado por el 1º arg.
-- Lo agrega a la lista de subpruebas del 2º arg.
newSubProof :: Maybe (Type, TType) -> [SubProof] -> [SubProof]
newSubProof t sp =  SP { termContext = x
                       , bTypeContext = y
                       , tvars = z
                       , lsubp = 1
                       , ty =  [t] } : sp
  where s = head sp
        x = termContext s
        y = bTypeContext s
        z = tvars s

-- Representa la creación de las subpruebas para cada tipo
-- objetivo dado por el 2º arg.
newSubProofs :: Int -> [Maybe (Type, TType)] -> Proof ()
newSubProofs n ts
  | n > 1 = do replaceMaybeTypes $ tail ts
               replaceLevelSubp (n-1)
               modifyTotalSubp (+ (n-1))
               modifySubps $ newSubProof $ head ts
  | otherwise = error "error: newSubProofs, no debería pasar."

-- De acuerdo al 1º argumento, mantiene, crea o termina una subprueba.
evaluateSubProof :: Int -> [Maybe (Type, TType)] -> Proof ()
evaluateSubProof n ts
  | n == 1 = replaceMaybeTypes ts
  | n == 0 = endSubProof
  | n > 1 = newSubProofs n ts

endSubProof :: Proof ()
endSubProof =
  do level <- getSubProofLevel
     modifySubps tail
     modifyTotalSubp (+ (-1))
     case level of
       Just l -> if lsubp l == 1
                 then return ()
                 else do modifyType tail
                         modifyLevelSubp (+ (-1))
                         modifySubps $ newSubProof $ head $ ty l
       Nothing -> return ()
