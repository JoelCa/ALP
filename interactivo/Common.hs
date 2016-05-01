module Common where

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
            deriving (Show, Eq)
  
  -- Términos con nombres (NO seria necesario)
  data LamTerm  =  LVar String
                |  Abs String Type LamTerm
                |  App LamTerm LamTerm
                deriving (Show, Eq)


  data Tactic = Assumption | Apply Int | Intro deriving (Show)

  -- Términos localmente sin nombres
  data Term  = Bound Int
             | Free Name 
             | Term :@: Term
             | Lam Type Term
             | Let2 Name Term Term
             | As2 Term Type
             | Unit2
          deriving (Show, Eq)

  -- Valores
  data Value = VLam Type Term

  -- Contextos del tipado
  type Context = [Type]
  
  --Comandos
  data Command = Ty Type | Ta Tactic deriving (Show)

