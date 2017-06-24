module ProverState where

import Common
import Parser (UsrParser, basicInfixParser)
import GlobalState
import Proof (ProofConstruction, newProofC, getLTermFromProof)
import Data.Maybe (isJust)
import Data.Sequence (Seq)

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: GlobalState
                       , infixParser :: UsrParser
                       }


  -- Estado de la prueba que se está construyendo.
data ProofState = PState { name :: String
                         , types :: (Type,TType)
                         , constr :: ProofConstruction
                         }

-- Genera una nueva prueba.
newProof' :: GlobalState -> String -> (Type,TType) -> (Type, TType) -> ProofState
newProof' g name ty tyr = PState { name = name
                                 , types = ty
                                 , constr = newProofC g tyr
                                 }

-- Inicia una nueva prueba.
newProof :: String -> (Type,TType) -> (Type, TType) -> ProverState -> ProverState
newProof name ty tyr p = p {proof = Just $ newProof' (global p) name ty tyr}

getProofC :: ProverState -> ProofConstruction
getProofC (PSt {proof = Just pr}) = constr pr
getProofC _ = error "error: getProofC, no debería pasar."

getTypeProof :: ProverState -> (Type,TType)
getTypeProof (PSt {proof = Just pr}) = types pr
getTypeProof _ = error "error: getTypeProof, no debería pasar."


-- Finaliza la prueba.
finishProof :: ProverState -> ProverState
finishProof p = p {proof = Nothing}

-- La prueba pasa a ser un teorema.
newTheoremFromProof :: ProverState -> ProverState
newTheoremFromProof p@(PSt {proof = Just pr}) =
  newTheorem (name pr) (getLTermFromProof (constr pr) (types pr)) p

newTheorem :: String -> Term -> ProverState -> ProverState
newTheorem name te  = modifyGlobal (checkConflictName name . addTheorem name te)

-- Indica si se inicio una prueba.
proofStarted :: ProverState -> Bool
proofStarted p = isJust $ proof p

-- Estado inicial.
initialProver :: ProverState
initialProver = PSt { global = initialGlobal
                    , proof = Nothing
                    , infixParser = basicInfixParser
                    }

modifyGlobal :: (GlobalState -> GlobalState) -> ProverState -> ProverState
modifyGlobal f p = p {global = f $ global p}

modifyUsrParser :: (UsrParser -> UsrParser) -> ProverState -> ProverState
modifyUsrParser f p = p {infixParser = f $ infixParser p}

setProofC :: ProofConstruction -> ProverState -> ProverState
setProofC pc p@(PSt {proof = Just pr}) = p {proof = Just $ pr {constr = pc}}
setProofC _ _ = error "error: setProofC, no debería pasar."

theoremName :: ProverState -> String
theoremName (PSt {proof = Just pr}) = name pr
theoremName _ = error "error: theoremName, no debería pasar."

