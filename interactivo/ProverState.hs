module ProverState where

import Common
import GlobalState
import Proof (ProofConstruction, newProofC, getLTermFromProof)
import Data.Maybe (isJust)
import Data.Sequence (Seq)

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: GlobalState
                       , cc :: Int                    -- Contador del número de entradas dadas por el usuario.
                       }


  -- Estado de la prueba que se está construyendo.
data ProofState = PState { name :: String
                         , types :: DoubleType
                         , constr :: ProofConstruction
                         }

-- Genera una nueva prueba.
newProof' :: GlobalState -> String -> DoubleType -> DoubleType -> ProofState
newProof' g name ty tyr = PState { name = name
                                 , types = ty
                                 , constr = newProofC g tyr
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
newLamDefinition name te ty  = modifyGlobal (checkConflictName name . addLamTerm name te ty)

newEmptyLamDefinition :: String -> DoubleType -> ProverState -> ProverState
newEmptyLamDefinition name ty  = modifyGlobal (checkConflictName name . addEmptyLamTerm name ty)


-- Indica si se inicio una prueba.
proofStarted :: ProverState -> Bool
proofStarted p = isJust $ proof p

-- Estado inicial.
initialProver :: ProverState
initialProver = PSt { global = initialGlobal
                    , proof = Nothing
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

addCount :: ProverState -> ProverState
addCount p = p {cc = cc p + 1}

getCounter :: ProverState -> Int
getCounter (PSt {cc = n}) = n
