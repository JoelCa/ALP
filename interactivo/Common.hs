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

  -- Nombres.
data Name
     =  Global  String
     |  Quote   Int
     deriving (Show, Eq)
    
type Var = String

  -- Tipos con nombre.
data Type = B Var
          | Fun Type Type
          | ForAll Var Type
          | RenameTy String [Type]
          deriving (Show, Eq)
  
  -- Tipos sin nombre.
data TType = TBound Int
           | TFree Var
           | TFun TType TType
           | TForAll TType
           | RenameTTy Int [TType]
           deriving (Show, Eq)

  -- Lambda términos con nombres.
data LamTerm  =  LVar String
              |  Abs String Type LamTerm
              |  App LamTerm LamTerm
              |  BAbs String LamTerm
              |  BApp LamTerm Type
              deriving (Show, Eq)

  -- Lambda términos sin nombres.
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam (Type,TType) Term
           | BLam Var Term
           | Term :!: (Type,TType)
           deriving (Show, Eq)

  -- Para cada variable de término, tenemos (por posición en la 4-tupla):
  -- 1. Su posición en el contexto, a la hora de imprimirlo.
  -- 2. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 3-4. Su tipo con y sin nombres, respectivamente.
type TermVar = (Int,Int,Type,TType)

  -- Secuencia de variables de términos. 
type TermContext = Seq TermVar

  -- Para cada variable de tipo ligada, tenemos (por posición en la tupla):
  -- 1. Su posición en el contexto. Útil a la hora de imprimirlo.
  -- 2. El nombre.
type BTypeVar = (Int,String)

  -- Secuencia de variables de tipo ligadas.
type BTypeContext = Seq BTypeVar

  -- Tabla de teoremas.
  -- Clave: Nombre del teorema.
  -- Valor: El lambda término de la prueba, junto con su tipo, con y sin nombres.
type Teorems = Map String (Term,(Type,TType))

type FTypeVar = String

  -- Secuencua de variables de tipo libres.
type FTypeContext = [FTypeVar]

  --Comandos.
data Command = Ty String Type
             | Ta Tactic
             | Props [String]
             | TypeDef (String, Type, Operands, Bool)
             deriving (Show)

  -- Tácticas.
data Tactic = Assumption | Apply String | Intro | Intros | Split
            | Elim String | CLeft | CRight | Print String 
            | CExists Type | Cut Type | Exact (Either Type LamTerm)
            | Infer LamTerm | Unfold String (Maybe String)
            deriving (Show)


  -- Excepciones.
data ProofExceptions = PNotFinished | PNotStarted | PExist String
                     | PNotExist String | SyntaxE | AssuE
                     | IntroE1 | ApplyE1 Type Type | ApplyE2
                     | Unif1 | Unif2 | Unif3 | Unif4
                     | ElimE1 | CommandInvalid | PropRepeated1 String
                     | PropRepeated2 String | PropNotExists String
                     | OpE1 String | OpE2 String | ExactE1 Type
                     | ExactE2 Type | PSE | EmptyType | TermE String
                     | InferE1 String | InferE2 Type | InferE3 Type
                     | InferE4 Type | DefE String | UnfoldE1 String
                     | UnfoldE2
                     deriving (Show, Typeable)
                              
instance Exception ProofExceptions

  -- Cantidad de operandos de una operación.
data Operands = Empty
              | Unary
              | Binary
              deriving (Show)

  -- Operaciones por default, NO "foldeables", donde:
  -- 1. Texto de la operación.
  -- 2. Código que identifica a la operación.
  -- 3. Cantidad de operandos (a lo sumo 2).
and_ = (['/','\\'] , -1, Binary)
or_ = (['\\','/'], -2, Binary)
bottom_ = ("False", -3, Empty
          )
and_text = fst3 and_
or_text = fst3 or_
bottom_text = fst3 bottom_

and_code = snd3 and_
or_code = snd3 or_
bottom_code = snd3 bottom_

  -- Operaciones por default, "foldeables".
not_text = "~"
iff_text = "<->"

not_code = 0 :: Int

  -- Conjunto de operaciones NO "foldeables".
notFoldeableOps :: [(String, Int, Operands)]
notFoldeableOps = [and_, or_, bottom_]

num_notFOps :: Int
num_notFOps = 3

  -- Operación "foldeable", donde:
  -- 1. El texto que la identifica.
  -- 2. Cuerpo de la operación.
  -- 3. Indica la cantidad de operandos.
  -- 4. Es True sii es un operador infijo.
  -- Todas las operaciones que define el usuario son foldeables.
type FoldeableOp = (String, (Type, TType), Operands, Bool)
type FOperations = [FoldeableOp]

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: ProverGlobal
                       }

  -- Definiciones globales.
data ProverGlobal = PGlobal { fTypeContext :: FTypeContext
                            , teorems :: Teorems             -- Teoremas.
                            , opers :: FOperations           -- Operaciones "foldeables".
                            }
                    
  -- Estado de la prueba que se está construyendo.
data ProofState = PState { name :: String
                         , types :: (Type,TType)
                         , constr :: ProofConstruction
                         }

  -- Construcción de la prueba.
data ProofConstruction = PConstruction { tsubp :: Int              -- Cantidad total de subpruebas activas.
                                       , subps :: [SubProof]       -- Datos de las subpruebas, ordenas por nivel.
                                       , cglobal :: ProverGlobal   -- Copia de los datos globales.
                                       , term :: [SpecialTerm]     -- Lambda termino.
                                       }

  -- Conjunto de subpruebas.
data SubProof = SP { termContext :: TermContext    -- Vars. de término.
                   , bTypeContext :: BTypeContext  -- Vars. de tipo ligadas.
                                                   -- Útil para el pretty printer.
                   , lsubp :: Int                  -- Cantidad de subpruebas activas contenidas.
                   , tvars :: Int                  -- Cantidad total de variables de tipo y
                                                   -- términos disponibles. Útil para el pretty printer.
                   , ty :: [Maybe (Type, TType)]   -- Tipo objetivo, de cada subprueba contenida.
                   }


  -- Lamda términos con aujeros.
data SpecialTerm = HoleT (Term->Term) | DoubleHoleT (Term->Term->Term) |
                   Term Term | TypeH TypeHole

  -- Tipos con aujeros.
data TypeHole = HTe ((Type, TType) -> Term) | HTy ((Type, TType) -> TypeHole)


  -- Instancias.
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

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x
