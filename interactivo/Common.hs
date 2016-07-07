{-# LANGUAGE DeriveDataTypeable #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException

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
          deriving (Show, Eq)
  
  -- Tipo de los tipos localmente sin nombre
data TType = TB Name
          | TFun TType TType
          | TForAll TType
          deriving (Show, Eq)

  -- Términos con nombres (NO seria necesario)
data LamTerm  =  LVar String
              |  Abs String Type LamTerm
              |  App LamTerm LamTerm
              deriving (Show, Eq)

data Tactic = Assumption | Apply String | Intro deriving (Show)

  -- Términos pseudo localmente sin nombres
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam Type Term
           | BLam Var Term
           | Term :!: Type
           deriving (Show, Eq)

  -- Valores
data Value = VLam Type Term

  -- Contextos del tipado
type Context = [Type]
  
  --Comandos
data Command = Ty Type | Ta Tactic deriving (Show)

data ProofExceptions = PNotFinished | PNotStarted | SyntaxE | AssuE | IntroE1 | IntroE2 | ApplyE1 | ApplyE2 |
                       ApplyE3 | CommandInvalid
                     deriving (Show, Typeable)
                              
instance Exception ProofExceptions

data ProofState = PState {position :: Int
                         , context :: Context
                         , ty :: Type
                         , term :: SpecialTerm
                         }
                                    
data SpecialTerm = EmptyTerm (Term->Term) | Term Term
