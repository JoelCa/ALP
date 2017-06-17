module GlobalState where

import Common
import Data.IntSet

type TeoremsName = IntSet


-- Definiciones globales.
data GlobalState = Global { fTypeContext :: FTypeContext
                          , teorems :: Teorems             -- Teoremas.
                          , opers :: FOperations           -- Operaciones "foldeables"
                          , conflict :: TeoremsName        -- Nombres de teoremas conflictivos.
                          }
