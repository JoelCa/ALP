module Proof where

import Common
import LambdaTermDefinition (LamDefs)
import TypeDefinition (TypeDefs)
import GlobalState
import TermsWithHoles
import Control.Monad.State.Lazy (get, modify)
import qualified Data.Sequence as S
import Hypothesis
  
type Proof = StateExceptions ProofConstruction SemanticException


  -- Construcción de la prueba.
data ProofConstruction = PConstruction { tsubp :: Int              -- Cantidad total de subpruebas activas.
                                       , subps :: [SubProof]       -- Datos de las subpruebas, ordenas por nivel.
                                       , cglobal :: GlobalState    -- Inicialmente es una copia de los datos globales.
                                       , term :: LTermHoles        -- Lambda termino con aujeros.
                                       }

  -- Conjunto de subpruebas.
data SubProof = SP { termContext :: TermContext    -- Vars. de término.
                   , bTypeContext :: BTypeContext  -- Vars. de tipo ligadas.
                                                   -- Útil para el pretty printer.
                   , lsubp :: Int                  -- Cantidad de subpruebas activas contenidas.
                   , tvars :: Int                  -- Cantidad total de variables de tipo y
                                                   -- términos disponibles. Útil para el pretty printer.
                   , ty :: [Maybe DoubleType]      -- Tipo objetivo, de cada subprueba contenida.
                   }
              deriving Show

-- Operaciones que modifican el estado de la monada Proof.
-- Es decir que, estas operaciones cambian la prueba.

addConflicNameInProof :: String -> Proof ()
addConflicNameInProof = modify . addConflicNameInProof'

addConflicNameInProof' :: String -> ProofConstruction -> ProofConstruction
addConflicNameInProof' name ps@(PConstruction {cglobal = cg}) =
  ps {cglobal = addConflictName name cg}

getGlobalAttr :: (GlobalState -> a) -> Proof a
getGlobalAttr f = do ps <- get
                     return $ f $ cglobal $ ps

getAttribute :: (SubProof -> a) -> Proof a
getAttribute f = do ps <- get
                    let x = subps ps
                    if null x
                      then error "error: getAttribute, no debería pasar."
                      else return $ f $ head x

getType :: Proof (Maybe DoubleType)
getType = do t <- getAttribute ty
             return $ head t

getTermContext :: Proof TermContext
getTermContext = getAttribute termContext

getBTypeContext :: Proof BTypeContext
getBTypeContext = getAttribute bTypeContext

getTypeDefinitions :: Proof TypeDefs
getTypeDefinitions = getGlobalAttr typeDef

getLamDefinitions :: Proof LamDefs
getLamDefinitions = getGlobalAttr lamDef

getFTypeContext :: Proof FTypeContext
getFTypeContext = getGlobalAttr fTypeContext

getConflictNames :: Proof ConflictNames
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
  
addTermContext :: TermVarWithType -> Proof ()
addTermContext = modify . addTermContext'

addTermContext' :: TermVarWithType -> ProofConstruction -> ProofConstruction
addTermContext' x ps@(PConstruction {subps=sp:sps}) =
  ps {subps = sp {termContext = x S.<| termContext sp} : sps}

updateTermContext :: Int -> TermVarWithType -> Proof ()
updateTermContext n x = modify $ updateTermContext' n x

updateTermContext' :: Int -> TermVarWithType -> ProofConstruction -> ProofConstruction
updateTermContext' n x ps@(PConstruction {subps=sp:sps}) =
  ps {subps = sp {termContext = S.update n x $ termContext sp} : sps}

addBTypeContext :: BTypeVar -> Proof ()
addBTypeContext = modify . addBTypeContext'

addBTypeContext' :: BTypeVar -> ProofConstruction -> ProofConstruction
addBTypeContext' x ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {bTypeContext = x S.<| bTypeContext sp} : sps}

modifyLevelSubp :: (Int -> Int) -> Proof ()
modifyLevelSubp = modify . modifyLevelSubp'

modifyLevelSubp' :: (Int -> Int) -> ProofConstruction -> ProofConstruction
modifyLevelSubp' f ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {lsubp = f $ lsubp sp} : sps}

modifyTotalSubp :: (Int -> Int) -> Proof ()
modifyTotalSubp f = modify (\ps -> ps {tsubp = f $ tsubp ps})

replaceLevelSubp :: Int -> Proof ()
replaceLevelSubp n = modifyLevelSubp (\_ -> n)

modifyType :: ([Maybe DoubleType] -> [Maybe DoubleType]) -> Proof ()
modifyType = modify . modifyType'

modifyType' :: ([Maybe DoubleType] -> [Maybe DoubleType])
           -> ProofConstruction -> ProofConstruction
modifyType' f ps@(PConstruction {subps=sp:sps})=
  ps {subps = sp {ty = f $ ty sp} : sps}

replaceMaybeTypes :: [Maybe DoubleType] -> Proof ()
replaceMaybeTypes ts = modifyType (\_ -> ts)

replaceType :: DoubleType -> Proof ()
replaceType t = modifyType (\_ -> [Just t])

removeFirstType :: Proof ()
removeFirstType = modifyType tail

modifyTerm :: (LTermHoles -> LTermHoles) -> Proof ()
modifyTerm f = modify (\ps -> ps {term = f $ term ps})

modifySubps :: ([SubProof] -> [SubProof]) -> Proof ()
modifySubps f = modify (\ps -> ps {subps = f $ subps ps})

------------------------------------------------------------------------------
-- Crea una subprueba para el tipo objetivo dado por el 1º arg.
-- Lo agrega a la lista de subpruebas del 2º arg.
addSubProof :: Maybe DoubleType -> [SubProof] -> [SubProof]
addSubProof t sp =  SP { termContext = x
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
newSubProofs :: Int -> [Maybe DoubleType] -> Proof ()
newSubProofs n ts
  | n > 1 = do replaceMaybeTypes $ tail ts
               replaceLevelSubp (n-1)
               modifyTotalSubp (+ (n-1))
               modifySubps $ addSubProof $ head ts
  | otherwise = error "error: newSubProofs, no debería pasar."

-- De acuerdo al 1º argumento, mantiene, crea o termina una subprueba.
evaluateSubProof :: Int -> [Maybe DoubleType] -> Proof ()
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
                         modifySubps $ addSubProof $ head $ ty l
       Nothing -> return ()

------------------------------------------------------------------------------
-- Funciones sobre ProofConstruction

newSubProof :: Int -> DoubleType -> SubProof
newSubProof n t = SP { termContext = S.empty,
                       bTypeContext = S.empty,
                       lsubp = 1,
                       tvars = n,
                       ty = [Just t]
                      }


newProofC :: GlobalState -> DoubleType -> ProofConstruction
newProofC g t = PConstruction { tsubp = 1
                              , subps = [newSubProof (length $ fTypeContext $ g) t]
                              , cglobal = g
                              , term = emptyLTerm
                              }

-- Obtiene el lambda término final de la prueba construida.
getLTermFromProof :: ProofConstruction -> DoubleType -> DoubleLTerm
getLTermFromProof (PConstruction {term=t}) ty =
  case getLTermNoHoles t of
    Just x -> x ::: ty
    Nothing -> error "getTermFromProof: no debería pasar."

-- Funciones auxiliares.
-- Chequea si la prueba a terminado.
isFinalTerm :: ProofConstruction -> Bool
isFinalTerm (PConstruction {term=t}) = withoutHoles t
