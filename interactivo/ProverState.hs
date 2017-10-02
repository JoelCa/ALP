module ProverState where

import Common
import GlobalState
import Proof (ProofConstruction, newProofC, getLTermFromProof)
import Data.Maybe (isJust)
import Data.Sequence (Seq)
import System.IO (Handle)

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: GlobalState
                       , save :: Maybe Handle
                       , lastComm :: Maybe String
                       , cc :: Int                    -- Contador del número de entradas dadas por el usuario.
                       }


  -- Estado de la prueba que se está construyendo.
data ProofState = PState { name :: String
                         , types :: DoubleType
                         , constr :: ProofConstruction
                         , history :: [String]
                         }

-- Genera una nueva prueba.
newProof' :: GlobalState -> String -> DoubleType -> DoubleType -> ProofState
newProof' g name ty tyr = PState { name = name
                                 , types = ty
                                 , constr = newProofC g tyr
                                 , history = []
                                 }

-- Inicia una nueva prueba.
newProof :: String -> DoubleType -> DoubleType -> ProverState -> ProverState
newProof name ty tyr p = p {proof = Just $ newProof' (global p) name ty tyr}

getProofC :: ProverState -> ProofConstruction
getProofC (PSt {proof = Just pr}) = constr pr
getProofC _ = error "error: getProofC, no debería pasar."

getTypeProof :: ProverState -> DoubleType
getTypeProof (PSt {proof = Just pr}) = types pr
getTypeProof _ = error "error: getTypeProof, no debería pasar."


-- Finaliza la prueba.
finishProof :: ProverState -> ProverState
finishProof p = p {proof = Nothing}

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

-- Estado inicial.
initialProver :: ProverState
initialProver = PSt { global = initialGlobal
                    , proof = Nothing
                    , save = Nothing
                    , lastComm = Nothing
                    , cc = 0
                    }

modifyGlobal :: (GlobalState -> GlobalState) -> ProverState -> ProverState
modifyGlobal f p = p {global = f $ global p}

setProofC :: ProofConstruction -> ProverState -> ProverState
setProofC pc p@(PSt {proof = Just pr}) = p {proof = Just $ pr {constr = pc}}
setProofC _ _ = error "error: setProofC, no debería pasar."

theoremName :: ProverState -> String
theoremName (PSt {proof = Just pr}) = name pr
theoremName _ = error "error: theoremName, no debería pasar."

addLastComm :: ProverState -> ProverState
addLastComm p@(PSt {proof = Just pr, lastComm = Just c}) = p {proof = Just $ pr {history = c : history pr}}
addLastComm p@(PSt {proof = Nothing, lastComm = Just _}) = p

saveHistory :: Handle -> ProverState -> ProverState
saveHistory file p  = p {save = Just file}

isWithHistory :: ProverState -> Bool
isWithHistory (PSt {save = s}) = isJust s

setLastCommand :: String -> ProverState -> ProverState
setLastCommand c p  = p {lastComm = Just c}

getLastCommand :: ProverState -> String
getLastCommand (PSt {lastComm = Just c}) = c
getLastCommand _ = error "error: getLastCommand, no debería pasar."

getHistoryFile :: ProverState -> Handle
getHistoryFile (PSt {save = Just file}) = file
getHistoryFile _ = error "error: getFileHistory, no debería pasar."

getProofCommands :: ProverState -> [String]
getProofCommands (PSt {proof = Just pr}) = history pr
getProofCommands _ = error "error: getProofCommands, no debería pasar."

addCount :: ProverState -> ProverState
addCount p = p {cc = cc p + 1}

getCounter :: ProverState -> Int
getCounter (PSt {cc = n}) = n
