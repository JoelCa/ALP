module GlobalState where

import Common
import Data.IntSet
import qualified Data.Map as Map
import qualified Data.Sequence as S
import Parser (getHypothesisValue)
import Rules
import DefaultOperators

type TheoremsNames = IntSet

-- Definiciones globales.
data GlobalState = Global { fTypeContext :: FTypeContext
                          , theorems :: Theorems             -- Teoremas.
                          , opers :: FOperations             -- Operaciones "foldeables"
                          , conflict :: TheoremsNames        -- Nombres de teoremas conflictivos.
                          }

-- Teoremas iniciales.
initialTheorems = [ ("intro_and", intro_and),
                    ("elim_and", elim_and),
                    ("intro_or1", intro_or1),
                    ("intro_or2", intro_or2),
                    ("elim_or", elim_or),
                    ("intro_bottom", intro_bottom),
                    ("elim_bottom", elim_bottom)
                  ]


addTheorem :: String -> Term -> GlobalState -> GlobalState
addTheorem name lt g = g {theorems = Map.insert name lt $ theorems g}

addOperator :: FoldeableOp -> GlobalState -> GlobalState
addOperator op g = g {opers = (opers g) S.|> op}

checkConflictName :: String -> GlobalState -> GlobalState
checkConflictName s g = g {conflict = addConflictName s $ conflict g}

addConflictName :: String -> TheoremsNames -> TheoremsNames
addConflictName s c = case getHypothesisValue s of
                        Just n -> insert n c
                        Nothing -> c

initialGlobal :: GlobalState
initialGlobal = Global { theorems = Map.fromList initialTheorems
                       , fTypeContext = S.empty
                       , opers = S.fromList [not_op, iff_op]
                       , conflict = empty
                       }

isTheorem :: String -> GlobalState -> Bool
isTheorem name g = Map.member name $ theorems g

isFreeVar :: String -> GlobalState -> Bool
isFreeVar name g = elem name $ fTypeContext g

isFoldeableOp :: String -> GlobalState -> Bool
isFoldeableOp name g = any (\(x,_,_,_) -> x == name) $ opers g

invalidName :: String -> GlobalState -> Bool
invalidName name g =  isTheorem name g
                      || isFreeVar name g
                      || isFoldeableOp name g
                      || isNotFoldeableOp name
                                 
addFreeVars :: S.Seq TypeVar -> GlobalState -> GlobalState
addFreeVars vars g = g {fTypeContext = vars S.>< fTypeContext g}

getLTerm :: String -> GlobalState -> Term
getLTerm name (Global {theorems = te}) = te Map.! name
