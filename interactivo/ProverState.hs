module ProverState where

import Common
import Parser (UsrParser, basicInfixParser)
import GlobalState
import Proof (ProofConstruction, newProofC, getTermFromProof)
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
newProof :: GlobalState -> String -> (Type,TType) -> (Type, TType) -> ProverState -> ProverState
newProof g name ty tyr p = p {proof = Just $ newProof' g name ty tyr}

getProofC :: ProverState -> ProofConstruction
getProofC (PSt {proof = Just pr}) = constr $ pr
getProofC (PSt {proof = Nothing}) = error $ show $ "error: getProofC, no debería pasar"

-- Finaliza la prueba.
finishProof :: ProverState -> ProverState
finishProof p = p {proof = Nothing}

-- La prueba pasa a ser un teorema.
newTheoremFromProof :: ProverState -> ProverState
newTheoremFromProof p@(PSt {proof = Just pr}) =
  newTheorem (name pr) (getTermFromProof (constr pr) (types pr)) p

newTheorem :: String -> Term -> ProverState -> ProverState
newTheorem name te p@(PSt {global = g}) =
  p { global = (checkConflictName name .
                addTheorem name te) g }
  
-- Estado inicial.
initialProver :: ProverState
initialProver = PSt { global = initialGlobal
                    , proof = Nothing
                    , infixParser = basicInfixParser
                    }

addFreeVarsProver :: Seq TypeVar -> ProverState -> ProverState
addFreeVarsProver vars p@(PSt {global = g}) = p {global = addFreeVars vars g}

--Crear: invalidPropositionName, y invalidDefinitionName (en base a las funciones de GlobalState)