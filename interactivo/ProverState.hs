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
                       , tempSave :: (FilePath, Handle)
                       , input :: Input
                       , cc :: Int                    -- Contador del número de entradas dadas por el usuario.
                       }
                   
  -- Mantiene datos de la entrada del usuario.
data Input = Inp { inp :: String                            -- Entrada del usuario. 
                 , commands :: [(EPosition,Command)]        -- Comandos ingresados por el usuario.
                 , incomplete :: Maybe (EPosition,String)   -- Posible comando incompleto ingresado por el usuario.
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
initialProver :: (FilePath, Handle) -> ProverState
initialProver h = PSt { global = initialGlobal
                      , proof = Nothing
                      , tempSave = h
                      , input = Inp {inp = [], commands = [], incomplete = Nothing}
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

setLastInput :: String -> ProverState -> ProverState
setLastInput x p@(PSt {input = i}) = p {input = i {inp = x}}

addLastInput :: String -> ProverState -> ProverState
addLastInput c p@(PSt {input = Inp {inp = x}}) =
  p {input = (input p) {inp = x ++ c}}

getLastInput :: ProverState -> String
getLastInput p@(PSt {input = Inp {inp = x}}) = x

addProofCommand :: ProverState -> ProverState
addProofCommand p@(PSt {proof = Just pr, input = Inp {inp = cs}}) = p {proof = Just $ pr {history = history pr ++ [cs]}}
addProofCommand p@(PSt {proof = Nothing}) = error "error: addProofCommand, no debería pasar"

addIncompleteInput :: (EPosition,String) -> ProverState -> ProverState
addIncompleteInput (pos, inc) p@(PSt {input = Inp {incomplete = x}}) =
  case x of
    Nothing -> p {input = (input p) {incomplete = Just (pos, inc)}}
    Just (_,inc') -> p {input = (input p) {incomplete = Just (pos, inc' ++ inc)}}

setTempHandle :: Handle -> ProverState -> ProverState
setTempHandle h p@(PSt {tempSave = (name, oldh)}) = p {tempSave = (name, h)}


getIncompleteComm :: ProverState -> Maybe (EPosition,String)
getIncompleteComm = incomplete . input

getLineCommands :: ProverState -> [(EPosition,Command)]
getLineCommands = commands . input

getIncompleteInput :: ProverState -> String
getIncompleteInput = inp . input


getTempFile :: ProverState -> (FilePath, Handle)
getTempFile (PSt {tempSave = file}) = file

getProofCommands :: ProverState -> [String]
getProofCommands (PSt {proof = Just pr}) = history pr
getProofCommands _ = error "error: getProofCommands, no debería pasar."

addCount :: ProverState -> ProverState
addCount p = p {cc = cc p + 1}

getCounter :: ProverState -> Int
getCounter (PSt {cc = n}) = n
