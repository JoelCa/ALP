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

-- Crea una prueba.
newProof :: GlobalState -> String -> Type -> Type -> TType -> ProofState
newProof pglobal name ty tyr tty =
  let s = SP { termContext = S.empty
             , bTypeContext = S.empty
             , lsubp = 1
             , tvars = length $ fTypeContext $ pglobal
             , ty = [Just (tyr, tty)]
             }
      c = PConstruction { tsubp = 1
                        , subps = [s]
                        , cglobal = pglobal
                        , term = [HoleT id]
                        }
  in PState { name = name
            , types = (ty, tty)
            , constr = c
            }

