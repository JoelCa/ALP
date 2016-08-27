{-# LANGUAGE DeriveDataTypeable #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException
import Data.Map (Map)

  -- Tipos de los nombres
data Name
     =  Global  String
     |  Quote   Int
     deriving (Show, Eq)
              
  -- Entornos
type NameEnv v t = [(Name, (v, t))]
    
type Var = String

  -- Tipo de los tipos
data Type = B Var
          | Fun Type Type
          | ForAll Var Type
          | Exists Var Type
          | And Type Type
          | Or Type Type 
          deriving (Show, Eq)
  
  -- Tipo de los tipos localmente sin nombre
data TType = TBound Int
           | TFree Var
           | TFun TType TType
           | TForAll TType
           | TExists TType
           | TAnd TType TType
           | TOr TType TType
           deriving (Show, Eq)

  -- Términos con nombres (NO seria necesario)
data LamTerm  =  LVar String
              |  Abs String Type LamTerm
              |  App LamTerm LamTerm
              deriving (Show, Eq)

  -- Términos pseudo localmente sin nombres
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam TType Term
           | BLam Term
           | Term :!: (Type,TType)
           deriving (Show, Eq)

  -- Valores
data Value = VLam Type Term

  -- Contextos del tipado
type Context = [(Type,TType)]
type TypeContext = [String]
  
  --Comandos
data Command = Ty String Type | Ta Tactic | Props [String] deriving (Show)

  -- Tácticas
data Tactic = Assumption | Apply String | Intro | Split | Elim String | CLeft | CRight | Print String deriving (Show)


  -- Excepciones
data ProofExceptions = PNotFinished | PNotStarted | PExist String |
                       PNotExist String | SyntaxE | AssuE | IntroE1 |
                       IntroE2 | ApplyE1 | ApplyE2 |
                       ApplyE3 | ApplyE4 | Unif1 |
                       Unif2 | Unif3 | Unif4 | ElimE1 |
                       CommandInvalid | PropRepeated1 String | PropRepeated2 String |
                       PropNotExists String
                     deriving (Show, Typeable)
                              
instance Exception ProofExceptions


  -- Estado de la prueba
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: ProverGlobal
                       }
                   
data ProverGlobal = PGlobal { props :: [String]
                         , terms :: Map String Term
                         }


data ProofState = PState {position :: [Int]
                         , context :: [Context]
                         , typeContext :: [TypeContext]
                         , ty :: [(Type, TType)]
                         , term :: [SpecialTerm]
                         , subp :: Int
                         , name :: String
                         }
                  

                                    
data SpecialTerm = HoleT (Term->Term) | DoubleHoleT (Term->Term->Term) | Term Term
