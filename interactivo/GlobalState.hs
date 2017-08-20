module GlobalState where

import Common
import Data.IntSet
import LambdaTermDefinition as LTD
import qualified Data.Sequence as S
import Parser (getHypothesisValue)
import Rules
import DefaultOperators

type ConflictNames = IntSet

-- Definiciones globales.
data GlobalState = Global { fTypeContext :: FTypeContext
                          , lamDef :: LamDefs               -- Lambda términos definidos.
                          , typeDef :: TypeDefs             -- Tipos definidos.
                          , conflict :: ConflictNames       -- Nombres de teoremas conflictivos
                                                            -- con los nombres de hipótesis.
                          }

-- Teoremas iniciales.
-- initialTheorems = [ ("intro_and", intro_and),
--                     ("elim_and", elim_and),
--                     ("intro_or1", intro_or1),
--                     ("intro_or2", intro_or2),
--                     ("elim_or", elim_or),
--                     ("intro_bottom", intro_bottom),
--                     ("elim_bottom", elim_bottom)
--                   ]


addTheorem :: String -> LTerm2 -> GlobalState -> GlobalState
addTheorem name lt g = g {lamDef = LTD.insert name lt $ lamDef g}

addOperator :: FoldeableOp -> GlobalState -> GlobalState
addOperator op g = g {opers = (opers g) S.|> op}

checkConflictName :: String -> GlobalState -> GlobalState
checkConflictName s g = g {conflict = addConflictName s $ conflict g}

addConflictName :: String -> ConflictNames -> ConflictNames
addConflictName s c = case getHypothesisValue s of
                        Just n -> insert n c
                        Nothing -> c

initialGlobal :: GlobalState
initialGlobal = Global { lamDef = LTD.empty
                       , fTypeContext = S.empty
                       , opers = S.fromList [not_op, iff_op]
                       , conflict = empty
                       }

isLamDef :: String -> GlobalState -> Bool
isLamDef name g = LTD.member name $ lamDef g

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

getLamTerm :: String -> GlobalState -> LTerm2
getLamTerm name (Global {lamDef = te}) = te LTD.! name
