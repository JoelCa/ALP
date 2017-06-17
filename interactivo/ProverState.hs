module ProverState where

import Common
import Parser (UsrParser)
import GlobalState (GlobalState)
import Proof (ProofConstruction)

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
