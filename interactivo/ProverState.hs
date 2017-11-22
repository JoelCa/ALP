module ProverState where

import Common
import GlobalState
import Proof (ProofConstruction, newProofC, getLTermFromProof)
import Data.Maybe (isJust)
import System.IO (Handle)

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState          -- Datos de la posible prueba en construcción.
                       , global :: GlobalState              -- Datos "globales".
                       , tempSave :: (FilePath, Handle)     -- Dirección del historial de comandos ingresados por el usuario.
                       , input :: Input                     -- Datos de un comando compuesto.
                       , cc :: Int                          -- Contador del número de entradas dadas por el usuario.
                       }
                   
  -- Mantiene datos para la construcción de un comando compuesto.
data Input = Inp { commands :: [PComm]                      -- Comandos completos que componen la penúltima entrada incompleta del usuario.
                 , incomplete :: Maybe PIncompleteComm      -- Posible comando incompleto de la penúltima entrada incompleta del usuario.
                 }
             
  -- Estado de la prueba que se está construyendo.
data ProofState = PState { name :: String
                         , types :: DoubleType
                         , constr :: ProofConstruction
                         , history :: [String]
                         }

-- Estado inicial.
initialProver :: (FilePath, Handle) -> ProverState
initialProver h = PSt { global = initialGlobal
                      , proof = Nothing
                      , tempSave = h
                      , input = Inp {commands = [], incomplete = Nothing}
                      , cc = 0
                      }

-- Inicia una nueva prueba.
newProof :: String -> DoubleType -> DoubleType -> ProverState -> ProverState
newProof name ty tyr p = p {proof = Just $ newProof' (global p) name ty tyr}

-- Genera una nueva prueba.
newProof' :: GlobalState -> String -> DoubleType -> DoubleType -> ProofState
newProof' g name ty tyr = PState { name = name
                                 , types = ty
                                 , constr = newProofC g tyr
                                 , history = []
                                 }

getProofC :: ProverState -> ProofConstruction
getProofC (PSt {proof = Just pr}) = constr pr
getProofC _ = error "error: getProofC, no debería pasar."

getTypeProof :: ProverState -> DoubleType
getTypeProof (PSt {proof = Just pr}) = types pr
getTypeProof _ = error "error: getTypeProof, no debería pasar."


-- Borra la prueba.
deleteProof :: ProverState -> ProverState
deleteProof p = p {proof = Nothing}

-- La prueba pasa a ser un teorema.
newLamDefFromProof :: ProverState -> ProverState
newLamDefFromProof p@(PSt {proof = Just pr}) =
  newLamDefinition (name pr) (getLTermFromProof (constr pr) (types pr)) (types pr) p

newLamDefinition :: String -> DoubleLTerm -> DoubleType -> ProverState -> ProverState
newLamDefinition name te ty  = modifyGlobal (addConflictName name . addLamTerm name te ty)

newEmptyLamDefinition :: String -> DoubleType -> ProverState -> ProverState
newEmptyLamDefinition name ty  = modifyGlobal (addConflictName name . addEmptyLamTerm name ty)

-- Indica si se inicio una prueba.
proofStarted :: ProverState -> Bool
proofStarted p = isJust $ proof p

modifyGlobal :: (GlobalState -> GlobalState) -> ProverState -> ProverState
modifyGlobal f p = p {global = f $ global p}

setProofC :: ProofConstruction -> ProverState -> ProverState
setProofC pc p@(PSt {proof = Just pr}) = p {proof = Just $ pr {constr = pc}}
setProofC _ _ = error "error: setProofC, no debería pasar."

theoremName :: ProverState -> String
theoremName (PSt {proof = Just pr}) = name pr
theoremName _ = error "error: theoremName, no debería pasar."

addInput :: String -> ProverState -> ProverState
addInput input p@(PSt {proof = Just pr}) = p {proof = Just $ pr {history = input : history pr}}
addInput _ (PSt {proof = Nothing}) = error "error: addProofCommand, no debería pasar"

addIncompleteInput :: PIncompleteComm -> ProverState -> ProverState
addIncompleteInput (pos, inc) p@(PSt {input = Inp {incomplete = x}}) =
  case x of
    Nothing -> p {input = (input p) {incomplete = Just (pos, inc)}}
    Just (_,inc') -> p {input = (input p) {incomplete = Just (pos, inc' ++ inc)}}

setIncompleteInput :: PIncompleteComm -> ProverState -> ProverState
setIncompleteInput ic p = p {input = (input p) {incomplete = Just ic}}

getIncompleteComm :: ProverState -> Maybe PIncompleteComm
getIncompleteComm = incomplete . input

getCompleteCommands :: ProverState -> [PComm]
getCompleteCommands = commands . input

joinIncompleteComm :: String -> ProverState -> String
joinIncompleteComm x (PSt {input = Inp {incomplete = y}}) =
  case y of
    Just (_,inc) -> inc ++ x
    Nothing -> x

addCommands :: [PComm] -> ProverState -> ProverState
addCommands xs p@(PSt {input = Inp {commands = ys}}) =
  p {input = (input p) {commands = ys ++ xs}}

cleanCommands :: ProverState -> ProverState
cleanCommands p = p {input = (input p) {commands = []}}

cleanIncCommand :: ProverState -> ProverState
cleanIncCommand p = p {input = (input p) {incomplete = Nothing}}

cleanInput :: ProverState -> ProverState
cleanInput = cleanIncCommand . cleanCommands

hasIncompleteInp :: ProverState -> Bool
hasIncompleteInp (PSt {input = Inp {incomplete = Just _}}) = True
hasIncompleteInp _ = False

setTempHandle :: Handle -> ProverState -> ProverState
setTempHandle h p@(PSt {tempSave = (name, _)}) = p {tempSave = (name, h)}

getTempFile :: ProverState -> (FilePath, Handle)
getTempFile (PSt {tempSave = file}) = file

getProofCommands :: ProverState -> [String]
getProofCommands (PSt {proof = Just pr}) = history pr
getProofCommands _ = error "error: getProofCommands, no debería pasar."

addCount :: ProverState -> ProverState
addCount p = p {cc = cc p + 1}

getCounter :: ProverState -> Int
getCounter (PSt {cc = n}) = n
