module GlobalState where

import Common
import Data.IntSet as IS
import LambdaTermDefinition as LTD
import TypeDefinition as TD
import qualified Data.Sequence as S
import Parser (getHypothesisValue)

type ConflictNames = IS.IntSet

-- Definiciones globales.
data GlobalState = Global { fTypeContext :: FTypeContext
                          , lamDef :: LTD.LamDefs           -- Lambda términos definidos.
                          , typeDef :: TD.TypeDefs          -- Tipos definidos.
                          , conflict :: ConflictNames       -- Nombres de teoremas conflictivos
                                                            -- con los nombres de hipótesis.
                          }


addEmptyLamTerm :: String -> DoubleType -> GlobalState -> GlobalState
addEmptyLamTerm name t g = g {lamDef = LTD.insertWithoutLamTerm name t $ lamDef g}

addLamTerm :: String -> LTerm2 -> DoubleType -> GlobalState -> GlobalState
addLamTerm name lt t g = g {lamDef = LTD.insertWithLamTerm name lt t $ lamDef g}

addType :: String -> TypeDefNoName -> GlobalState -> GlobalState
addType s d g = g {typeDef = TD.insert s d $ typeDef g}

checkConflictName :: String -> GlobalState -> GlobalState
checkConflictName s g = g {conflict = addConflictName s $ conflict g}

addConflictName :: String -> ConflictNames -> ConflictNames
addConflictName s c = case getHypothesisValue s of
                        Just n -> IS.insert n c
                        Nothing -> c

initialGlobal :: GlobalState
initialGlobal = Global { fTypeContext = S.empty
                       , lamDef = LTD.empty
                       , typeDef = TD.empty
                       , conflict = IS.empty
                       }

isLamDef :: String -> GlobalState -> Bool
isLamDef name g = LTD.member name $ lamDef g

isFreeVar :: String -> GlobalState -> Bool
isFreeVar name g = elem name $ fTypeContext g

isType :: String -> GlobalState -> Bool
isType name g = TD.member name $ typeDef g

invalidName :: String -> GlobalState -> Bool
invalidName name g =  isLamDef name g
                      || isFreeVar name g
                      || isType name g
                                 
addFreeVars :: S.Seq TypeVar -> GlobalState -> GlobalState
addFreeVars vars g = g {fTypeContext = vars S.>< fTypeContext g}

getLamTerm :: String -> GlobalState -> Maybe LTerm2
getLamTerm name (Global {lamDef = te}) = LTD.getLamTerm te name

getLamTermType :: String -> GlobalState -> DoubleType
getLamTermType name (Global {lamDef = te}) = LTD.getType te name

 
