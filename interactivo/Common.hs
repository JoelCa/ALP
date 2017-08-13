{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Data.Map (Map)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy
import Data.Void (Void)
import Text.Megaparsec (ParseError)
import Control.Monad.Reader (Reader)
import Data.Sequence (Seq, foldlWithIndex)

type TermVar = String

type TypeVar = String

data VarName a = Free a
               | Bound Int
               deriving (Show, Eq)

  -- Tipo con nombre.
type Type1 = Type TypeVar TypeVar

type DoubleTypeVar = (TypeVar, VarName TypeVar)

  -- Tipo con y sin nombre.
type DoubleType = Type TypeVar DoubleTypeVar


data Type a b = TVar b
              | Fun (Type a b) (Type a b)
              | ForAll a (Type a b)
              | Exists a (Type a b)
              | RenamedType a [Type a b]
              deriving (Show)

instance Eq (DoubleType) where
  (TVar (_,x)) == (TVar (_,y)) = x == y
  (Fun t1 t2) == (Fun t1' t2') = t1 == t1' &&  t2 == t2'
  (ForAll _ t) == (ForAll _ t') = t == t'
  (Exists _ t) == (Exists _ t') = t == t'
  (RenamedType s xs) == (RenamedType s' ys) =
    if s == s'
    then aux xs ys
    else False
    where aux [] [] = True
          aux (x:xs) (y:ys) = if x == y
                              then aux xs ys
                              else False
  _ == _ = False

  -- Lambda término con nombre, y tipos con nombres.
type LTerm1 = LamTerm TermVar TermVar Type1

  -- Lambda término sin nombre, y tipos con y sin nombres.
type LTerm2 = LamTerm () (VarName TermVar) DoubleType

type DoubleLTerm = LamTerm TermVar (TermVar, VarName TermVar) DoubleType

data LamTerm a b c = LVar b
                   | Abs a c (LamTerm a b c)
                   | BAbs TypeVar (LamTerm a b c)
                   | LamTerm a b c :@: LamTerm a b c
                   | LamTerm a b c :!: c
                   | EPack c (LamTerm a b c) c
                   | EUnpack TypeVar a (LamTerm a b c) (LamTerm a b c)
                   | LamTerm a b c ::: c
                   deriving (Show, Eq)

  -- Para cada variable de término, tenemos (por posición en la 4-tupla):
  -- 1. Su posición en el contexto, a la hora de imprimirlo.
  -- 2. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 3. Su tipo con y sin nombre.
type TermVarWithType = (Int, Int, DoubleType)

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


  --Comandos del lenguaje.
data Command = Theorem String Type1
             | Ta Tactic
             | Types (Seq TypeVar)
             | Definition String BodyDef
             | Axiom String Type1
             deriving (Show)

-- Comandos de la línea de comandos
data CLICommand = Escaped ECommand
                | Lang Command

data ECommand = Exit
              | Reset
              | Load [String]
              | Help
              deriving (Show)

data BodyDef = LTerm LTerm1
             | Type TypeDefinition
             | Ambiguous (GenTree String)
             deriving (Show)

  -- Definición de una "operación".
  -- 1. Cuerpo de la operación.
  -- 2. Cantidad de operandos.
  -- 3. Lista de los nombres de los argumentos.
  -- 4. Boleano. True sii es una operación binaria infija.
type TypeDefinition = (Type1, Operands, Seq TypeVar, Bool)

  -- Tácticas.
data Tactic = Assumption | Apply Int | Intro | Intros | Split
            | Elim Int | CLeft | CRight | Print String 
            | CExists Type1 | Cut Type1 | Exact ExactB
            | Infer LTerm1 | Unfold String (Maybe Int)
            | Absurd Type1
            deriving (Show)

data ExactB = LamT LTerm1
            | T Type1
            | Appl (GenTree String)
            deriving (Show)

  -- Excepciones.
data ProofException = PNotFinished | PNotStarted | ExistE String
                    | NotExistE String | SyntaxE (ParseError Char Void) | AssuE
                    | IntroE1 | ApplyE1 DoubleType DoubleType | HypoE Int
                    | Unif1 | Unif2 | Unif3 | Unif4
                    | ElimE1 | CommandInvalid | TypeRepeated String
                    | TypeNotExists String | OpE1 String | OpE2 String | ExactE1 DoubleType
                    | ExactE2 DoubleType | ExactE3 | PSE | EmptyType | TypeE String
                    | InferE DoubleLTerm InferException | UnfoldE1 String
                    | FileE IOError
                    deriving (Show, Typeable)

type EPosition = (String, Int)

type ExceptionPos = (EPosition, ProofException)

data InferException = InferE1 String | InferE2 DoubleLTerm DoubleType
                    | InferE3 DoubleLTerm String | InferE4 DoubleLTerm
                     deriving (Show, Typeable)
                              
instance Exception ExceptionPos --ProofExceptions

  -- Arbol general.
data GenTree a = Nil | Node a [GenTree a]
               deriving (Show)


  -- Cantidad de operandos de una operación.
type Operands = Int

  -- Operación NO "foldeable".
type NotFoldeableOp = (String, Operands)

  -- Operación "foldeable", donde:
  -- 1. Identificador.
  -- 2. Cuerpo de la operación (sin los para todos).
  -- 3. Cantidad de operandos.
  -- 4. Booleano. True sii es una operación binaria infija.
  -- Todas las operaciones que define el usuario son foldeables.
type FoldeableOp = (String, DoubleType, Operands, Bool)

  -- Operaciones "foldeables".
type FOperations = Seq FoldeableOp

getNumArgs :: FoldeableOp -> Operands
getNumArgs (_,_,n,_) = n


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
