{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Data.Map (Map)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy
import Text.Megaparsec
import Control.Monad.Reader (Reader)
import Data.Sequence (Seq, foldlWithIndex)
  
  -- Nombres.
data Name
     =  NGlobal  String
     |  Quote   Int
     deriving (Show, Eq)

type TermVar = String

type TypeVar = String

  -- Tipos con nombre.
data Type = B TypeVar
          | Fun Type Type
          | ForAll TypeVar Type
          | Exists TypeVar Type
          | RenameTy String Int [Type]
          deriving (Show, Eq)
  
  -- Tipos sin nombre.
data TType = TBound Int
           | TFree TypeVar
           | TFun TType TType
           | TForAll TType
           | TExists TType
           | RenameTTy Int [TType]
           deriving (Show, Eq)

  -- Lambda términos con nombres.
data LamTerm  = LVar TermVar
              | Abs TermVar Type LamTerm
              | App LamTerm LamTerm
              | BAbs TypeVar LamTerm
              | BApp LamTerm Type
              | EPack Type LamTerm Type
              | EUnpack TypeVar TermVar LamTerm LamTerm
              | As LamTerm Type
              deriving (Show, Eq)

  -- Lambda términos sin nombres.
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam (Type,TType) Term
           | BLam TypeVar Term
           | Term :!: (Type,TType)
           | Pack (Type,TType) Term (Type,TType)
           | Unpack TypeVar Term Term
           | Term ::: (Type,TType)
           deriving (Show, Eq)

-- Para cada variable de término, tenemos (por posición en la 4-tupla):
  -- 1. Su posición en el contexto, a la hora de imprimirlo.
  -- 2. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 3-4. Su tipo con y sin nombres, respectivamente.
type TermVarWithType = (Int,Int,Type,TType)

  -- Secuencia de variables de términos. 
type TermContext = Seq TermVarWithType

  -- Para cada variable de tipo ligada, tenemos (por posición en la tupla):
  -- 1. Su posición en el contexto. Útil a la hora de imprimirlo.
  -- 2. El nombre.
type BTypeVar = (Int, TypeVar)

  -- Secuencia de variables de tipo ligadas.
type BTypeContext = Seq BTypeVar


type FTypeVar = TypeVar

  -- Secuencia de variables de tipo libres.
type FTypeContext = Seq FTypeVar

  -- Tabla de teoremas.
  -- Clave: Nombre del teorema.
  -- Valor: El lambda término de la prueba.
type Teorems = Map String Term


  --Comandos.
data Command = Ty String Type
             | Ta Tactic
             | Types (Seq TypeVar)
             | Definition String BodyDef
             deriving (Show)

data BodyDef = LTerm LamTerm
             | Type TypeDefinition
             | Ambiguous (GenTree String)
             deriving (Show)

  -- Definición de una "operación".
  -- 1. Cuerpo de la operación.
  -- 2. Cantidad de operandos.
  -- 3. Lista de los nombres de los argumentos.
  -- 4. Boleano. True sii es una operación binaria infija.
type TypeDefinition = (Type, Operands, Seq TypeVar, Bool)

  -- Tácticas.
data Tactic = Assumption | Apply Int | Intro | Intros | Split
            | Elim Int | CLeft | CRight | Print String 
            | CExists Type | Cut Type | Exact ExactB
            | Infer LamTerm | Unfold String (Maybe Int)
            | Absurd Type
            deriving (Show)

data ExactB = LamT LamTerm
            | T Type
            | Appl (GenTree String)
            deriving (Show)

  -- Excepciones.
data ProofExceptions = PNotFinished | PNotStarted | ExistE String
                     | NotExistE String | SyntaxE String | AssuE
                     | IntroE1 | ApplyE1 Type Type | HypoE Int
                     | Unif1 | Unif2 | Unif3 | Unif4
                     | ElimE1 | CommandInvalid | TypeRepeated String
                     | TypeNotExists String | OpE1 String | OpE2 String | ExactE1 Type
                     | ExactE2 Type | ExactE3 | PSE | EmptyType | TypeE String
                     | InferE LamTerm InferExceptions | DefE String | UnfoldE1 String
                     deriving (Show, Typeable)

data InferExceptions = InferE1 String | InferE2 LamTerm Type
                     | InferE3 LamTerm String | InferE4 LamTerm
                     deriving (Show, Typeable)
                              
instance Exception ProofExceptions

  -- Arbol general.
data GenTree a = Nil | Node a [GenTree a]
               deriving (Show)


  -- Cantidad de operandos de una operación.
type Operands = Int

  -- Operación NO "foldeable".
type NotFoldeableOp = (String, Int, Operands)

  -- Operación "foldeable", donde:
  -- 1. Identificador.
  -- 2. Cuerpo de la operación (sin los para todos).
  -- 3. Cantidad de operandos.
  -- 4. Booleano. True sii es una operación binaria infija.
  -- Todas las operaciones que define el usuario son foldeables.
type FoldeableOp = (String, (Type, TType), Operands, Bool)

  -- Operaciones "foldeables".
type FOperations = Seq FoldeableOp

getNumArgs :: FoldeableOp -> Operands
getNumArgs (_,_,n,_) = n

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x


  -- Instancias.
newtype StateExceptions s e a = StateExceptions { runStateExceptions :: s -> Either e (a, s) }


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

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throw errorval
maybeToEither _ (Just normalval) = return normalval

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

getElemIndex :: (a -> Bool) -> Seq a -> Maybe (Int, a)
getElemIndex f xs = foldlWithIndex (\r i x -> if f x then Just (i, x) else r) Nothing xs
