{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Data.Map (Map)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy

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
          | RenameTy String [Type]
          deriving (Show, Eq)
  
  -- Tipo de los tipos localmente sin nombre
data TType = TBound Int
           | TFree Var
           | TFun TType TType
           | TForAll TType
           | RenameTTy Int [TType]
           deriving (Show, Eq)

and_op = "/" ++ [head "\\"]
or_op = [head "\\"] ++ "/"

  -- Términos con nombres
data LamTerm  =  LVar String
              |  Abs String Type LamTerm
              |  App LamTerm LamTerm
              |  BAbs String LamTerm
              |  BApp LamTerm Type
              deriving (Show, Eq)

  -- Términos sin nombres
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam (Type,TType) Term
           | BLam Var Term
           | Term :!: (Type,TType)
           deriving (Show, Eq)

-- data TypeOp = Op2 Int String Bool (Type -> Type -> Type)
--             | Op1 Int String Bool (Type -> Type)

data TypeBody = Unary ((Type, TType) -> (Type, TType))
              | Double ((Type, TType) -> (Type, TType) -> (Type, TType))

  -- Valores
data Value = VLam Type Term

  -- Contextos del tipado.

type TypeVar = (Int,Type,TType)
  -- Contexto de variables de términos. Para cada variable, tenemos
  -- su tipo con y sin nombre, junto con la profundidad con la que se
  -- añadio al contexto (la profundidad se refiere a la cantidad de
  -- cuantificadores construidos).
type Context = [TypeVar]
  -- Contexto de variables de tipos.
type TypeContext = [String]
  
  --Comandos
data Command = Ty String Type
             | Ta Tactic
             | Props [String]
             | TypeDef (String, Bool, Type)
             deriving (Show)

  -- Tácticas
-- Arreglar el Exact para que tome lambda términos
data Tactic = Assumption | Apply String | Intro | Intros | Split
            | Elim String | CLeft | CRight | Print String 
            | CExists Type | Cut Type | Exact (Either Type LamTerm) | Infer LamTerm
            deriving (Show)


  -- Excepciones
data ProofExceptions = PNotFinished | PNotStarted | PExist String
                     | PNotExist String | SyntaxE | AssuE
                     | IntroE1 | ApplyE1 Type Type | ApplyE2
                     | Unif1 | Unif2 | Unif3 | Unif4
                     | ElimE1 | CommandInvalid | PropRepeated1 String
                     | PropRepeated2 String | PropNotExists String
                     | OpE String | ExactE1 Type | ExactE2 Type
                     | PSE | EmptyType | TermE String
                     | InferE1 String | InferE2 Type | InferE3 Type
                     | InferE4 Type
                     deriving (Show, Typeable)
                              
instance Exception ProofExceptions

  -- Estado de la prueba
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: ProverGlobal
                       }
                   
data ProverGlobal = PGlobal { props :: TypeContext                         -- Proposiciones de tipos.
                            , teorems :: Map String (Term,(Type,TType))    -- Teoremas.
                            , opers :: [String]                            -- Operaciones
                            }

data ProofState = PState { name :: String
                         , types :: (Type,TType)
                         , constr :: ProofConstruction
                         }

data ProofConstruction = PConstruction { position :: [Int]
                                       , context :: [Context]
                                       , typeContext :: [TypeContext] -- Indica las proposiciones de tipos disponibles.
                                                                      -- por nivel. Util para el pretty printer.
                                       , ty :: [Maybe (Type, TType)]
                                       , term :: [SpecialTerm]
                                       , subp :: Int           -- Cantidad de subpruebas activas en total.
                                       , tyFromCut :: [Type]
                                       , subplevel :: [Int]    -- Indica la cantidad de subpruebas que están activas
                                                               -- por nivel.
                                       , quantifier :: [Int]   -- Indica la cantidad de variables de tipo en el contexto.
                                       , copers :: [String]     -- Conjunto de operaciones "custom". Copia del dato global.
                                       , cteorems :: Map String (Term,(Type,TType)) -- Teoremas. Copia del dato global.
                                       }

                                    
data SpecialTerm = HoleT (Term->Term) | DoubleHoleT (Term->Term->Term) |
                   Term Term | TypeH TypeHole

data TypeHole = HTe ((Type, TType) -> Term) | HTy ((Type, TType) -> TypeHole)


newtype StateExceptions s e a = StateExceptions { runStateExceptions :: s -> Either e (a, s) }

type Proof = StateExceptions ProofConstruction ProofExceptions

instance Monad (StateExceptions s e) where
  return x = StateExceptions (\s -> Right (x, s))
  m >>= f = StateExceptions (\s -> case runStateExceptions m s of
                                     Right (a,b) -> runStateExceptions (f a) b
                                     Left e -> Left e)

instance MonadState s (StateExceptions s e) where
    get = StateExceptions (\s -> Right (s, s))
    put s = StateExceptions (\_ -> Right ((), s))
    state f = StateExceptions (\s -> Right $ f s)

instance Applicative (StateExceptions s e) where
  pure  = return
  (<*>) = ap
              
instance Functor (StateExceptions s e) where
  fmap = liftM

class Monad m => MonadException m e where
  throw :: e -> m a
  catch :: m a -> (e -> m a) -> m a

instance MonadException (StateExceptions s e) e where
  throw e = StateExceptions (\_ -> Left e)
  catch m f = StateExceptions (\s -> case runStateExceptions m s of
                                       Left e -> runStateExceptions (f e) s
                                       Right x -> Right x)

instance MonadException (Either e) e where
  throw e = Left e
  catch m f = case m of
                Left x -> f x
                Right x -> Right x
