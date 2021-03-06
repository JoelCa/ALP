{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy
import Data.Void (Void)
import Text.Megaparsec (ParseError)
import Data.Sequence (Seq)

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
          aux (a:as) (b:bs) = if a == b
                              then aux as bs
                              else False
          aux _ _ = False
  _ == _ = False

  -- Lambda término con nombre, y tipos con nombres.
type LTerm1 = LamTerm TermVar TermVar Type1

  -- Lambda término con y sin nombre, y tipos con y sin nombre.
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
  -- 1. Nombre.
  -- 2. Su posición en el contexto.
  -- 3. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 4. Su tipo con y sin nombre.
type TermVarWithType = (TermVar, Int, Int, Maybe DoubleType)

  -- Secuencia de variables de términos. 
type TermContext = Seq TermVarWithType

  -- Para cada variable de tipo ligada, tenemos (por posición en la tupla):
  -- 1. El nombre.
  -- 2. Su posición en el contexto. Útil a la hora de imprimirlo.
type BTypeVar = (TypeVar, Int)

  -- Secuencia de variables de tipo ligadas.
type BTypeContext = Seq BTypeVar

type FTypeVar = TypeVar

  -- Secuencia de variables de tipo libres.
type FTypeContext = Seq FTypeVar


  -- Comandos del lenguaje.
data Command = Theorem String Type1
             | Axiom String Type1
             | Tac Tactic
             | Vars (Seq TypeVar)
             | Definition String BodyDef
             | Print String
             | PrintAll
             | Infer LTerm1
             deriving (Show)

  -- Comandos del lenguaje, y comandos de control. 
data ExtCommand = Escaped ECommand
                | Lang Command
                deriving (Show)

  -- Comandos de control.
data ECommand = Exit
              | Abort
              | Load [String]
              | Save String
              | Help
              deriving (Show)

  -- Comandos provenientes de la línea de comandos.
data CLICommands = Simple PExtComm
                 | Compound PCompoundCommand
                 deriving (Show)

  -- Comando del lenguaje, junto con su posición de aparición en la línea de comandos.
type PCommand = (EPosition, Command)

type PCommandWithInput a = (EPosition, String, a)

  -- Comando, junto con su posición.
  -- En sus dos representaciones, concreta y abstracta.
type PExtComm = PCommandWithInput ExtCommand

  -- Comando del lenguaje, junto con su posición
  -- En sus dos representaciones, concreta y abstracta.
type PComm = PCommandWithInput Command

  -- Comando incompleto, junto con su posición.
type PIncompleteComm = (EPosition, String)

  -- Comando compuesto, donde:
  -- 1. Posible comando incompleto, que precede a los comandos completos.
  -- 2. Comandos completos.
  -- 3. Posible comando incompleto, que sucede a los comandos completos.
type PCompoundCommand = (Maybe PIncompleteComm, [PComm], Maybe PIncompleteComm)

  -- Comando de declaración de lambda términos o tipos.
data BodyDef = LTerm LTerm1
             | EmptyLTerm Type1
             | Type TypeDefWithName
             | Ambiguous (GenTree String)
             deriving (Show)

  -- Datos de una definición de tipo.
  -- Donde:
  -- 1. Algún dato.
  -- 2. Cantidad de argumentos.
  -- 3. Boleano. True sii es un tipo binario infijo.
type TypeDef a = (a, Int, Bool)

  -- Tipo definido (tipo con nombre). 
type TypeDefWithName = TypeDef (Type1, Seq TypeVar)

  -- Tipo definido (tipo con nombre y sin nombre).
type TypeDefNoName = TypeDef DoubleType

  -- Tácticas de prueba.
data Tactic = Assumption | Apply Int | Intro
            | Intros | Split | Elim Int
            | CLeft | CRight | CExists Type1
            | Cut Type1 | Exact ExactB | Unfold String (Maybe Int)
            | Absurd Type1 | Show
            deriving (Show)

  -- Táctica "exact".
data ExactB = LamT LTerm1
            | T Type1
            | Appl (GenTree String)
            deriving (Show)

  -- Excepciones del lenguaje.
data SemanticException = PNotFinished | PNotStarted | ExistE String
                       | NotExistE String | AssuE
                       | IntroE1 | ApplyE1 DoubleType DoubleType | HypoE Int
                       | Unif1 | Unif2 | Unif3 | Unif4
                       | ElimE1 | InvalidCommand | TypeRepeated String
                       | OpE1 String | OpE2 String | ExactE1 DoubleType
                       | ExactE2 DoubleType | ExactE3 | EmptyType | TypeE String
                       | InferE DoubleLTerm InferException | UnfoldE1 String
                       | TermVarE String | TypeVarE String | InvalidCompComm
                       deriving (Show, Typeable)

data PException a = SemanticE a
                  | SyntaxE (ParseError Char Void)
                  | FileE String
                  deriving (Show, Typeable)

  -- Excepciones junto con su posición de aparición. 
type ProverExceptionPos = PException (EPosition, SemanticException)

  -- Excepciones, sin su posición.
type ProverException = PException SemanticException

  -- Posición.
type EPosition = (String, Int)

  -- Errores del comando "infer",
data InferException = InferE1 String | InferE2 DoubleLTerm DoubleType
                    | InferE3 DoubleLTerm String | InferE4 DoubleLTerm
                     deriving (Show, Typeable)
                              
  -- Árbol. Útil en la representación de una aplicación "ambigua"
  -- (a priori no se sabe si es una aplicación de lambda términos, o "aplicación" de tipos).
data GenTree a = Nil | Node a [GenTree a]
               deriving (Show)


  -- Nombre de los tipos declarados en el preludio.
and_id = ['/', '\\']
or_id = ['\\', '/']
bottom_id = "False"
iff_id = "<->"
not_id = "~"


--------------------------------------------------------------------------------------
-- Instancias.

instance Exception ProverExceptionPos

-- Estado.
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

lambTermVar :: String -> DoubleLTerm
lambTermVar s = LVar (s, Free s)
