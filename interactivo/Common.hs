{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Data.Map (Map)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy
import Data.Sequence (Seq)

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


-- data TypeBody = Unary ((Type, TType) -> (Type, TType))
--               | Double ((Type, TType) -> (Type, TType) -> (Type, TType))

  -- Valores
-- data Value = VLam Type Term

  -- Para cada variable de término, tenemos (por posición en la 4-tupla):
  -- 1. Su posición en el contexto, a la hora de imprimirlo.
  -- 2. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 3-4. Su tipo con y sin nombres, respectivamente.
type TermVar = (Int,Int,Type,TType)

  -- Contexto de variables de términos. 
type TermContext = Seq TermVar

  -- Para cada variable de tipo ligada, tenemos (por posición en la tupla):
  -- 1. Su posición en el contexto. Útil a la hora de imprimirlo.
  -- 2. El nombre.
type BTypeVar = (Int,String)

  -- Contexto de variables de tipo ligadas.
type BTypeContext = Seq BTypeVar

  -- Tabla de teoremas
  -- Clave: Nombre del teorema.
  -- Valor: El lambda término de la prueba, junto con su tipo, con y sin nombres.
type Teorems = Map String (Term,(Type,TType))

type FTypeVar = String

  -- Contexto de variables de tipo libre.
type FTypeContext = [FTypeVar]

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

  -- Operaciones no básicas, donde:
  -- 1. Texto de la operación.
  -- 2. Es True si es un operador binario.
and_ = ("/" ++ [head "\\"], True)
or_ = ([head "\\"] ++ "/", True)

and_text = fst and_

and_code :: Int
and_code = -2

or_text = fst or_

or_code :: Int
or_code = -1

  -- Conjunto de operaciones no básicas.
defaults_op :: [(String,Bool)]
defaults_op = [and_, or_]

num_defaults_op :: Int
num_defaults_op = 2

  -- Operación (a lo sumo binaria), definida por el usuario, donde:
  -- 1. El texto que la identifica.
  -- 2. Es True si es un operador infijo.
  -- 3. Es True si es un operador binario.
type UserOperation = (String, Bool, Bool)

  -- Estado de la prueba
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: ProverGlobal
                       }
                   
data ProverGlobal = PGlobal { fTContext :: FTypeContext
                            , teorems :: Teorems                -- Teoremas.
                            , opers :: [UserOperation]              -- Operaciones "custom".
                            }

data ProofState = PState { name :: String
                         , types :: (Type,TType)
                         , constr :: ProofConstruction
                         }

data ProofConstruction = PConstruction { termContexts :: [TermContext]
                                       , bTContexts :: [BTypeContext] -- Indica las proposiciones de tipos disponibles.
                                                                      -- por nivel. Útil para el pretty printer.
                                       , ty :: [Maybe (Type, TType)]
                                       , term :: [SpecialTerm]
                                       , tsubp :: Int           -- Cantidad de subpruebas activas en total.
                                       , lsubp :: [Int]         -- Indica la cantidad de subpruebas que están activas
                                                                -- por nivel.
                                       , tvars :: [Int]         -- La cantidad total de variables de tipo y términos disponibles.
                                                                -- Útil para el pretty printer.
                                       , cglobal :: ProverGlobal  -- Copia del dato global.
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
