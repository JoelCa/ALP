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


  data Tactics = Assumption | Apply Var | Intro VarRename deriving (Show)

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
  type VarRename = Maybe Var
  type Context = [(VarRename,Type)]
  type DefaultVar = Int --last default name var
  type SpecialRename = [Int]
