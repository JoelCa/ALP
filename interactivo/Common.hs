{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Common where

import Data.Typeable
import System.Console.Haskeline.MonadException (Exception)
import Data.Map (Map)
import Control.Monad (ap, liftM)
import Control.Monad.State.Lazy
import Parsing (ParserState)
import Data.Vector (Vector, ifoldl)
import Data.IntSet
import Text.Megaparsec
import Control.Monad.Reader (Reader)

type UsrParser = ParserParser Type

type Parser = ParsecT Dec String (Reader UsrParser)

newtype ParserParser a = PP { getParser :: Parser a }


  -- Nombres.
data Name
     =  Global  String
     |  Quote   Int
     deriving (Show, Eq)
    
type TermV = String
type TypeV = String

  -- Tipos con nombre.
data Type = B TypeV
          | Fun Type Type
          | ForAll TypeV Type
          | Exists TypeV Type
          | RenameTy String Int [Type]
          deriving (Show, Eq)
  
  -- Tipos sin nombre.
data TType = TBound Int
           | TFree TypeV
           | TFun TType TType
           | TForAll TType
           | TExists TType
           | RenameTTy Int [TType]
           deriving (Show, Eq)

  -- Lambda términos con nombres.
data LamTerm  = LVar TermV
              | Abs TermV Type LamTerm
              | App LamTerm LamTerm
              | BAbs TypeV LamTerm
              | BApp LamTerm Type
              | EPack Type LamTerm Type
              | EUnpack TypeV TermV LamTerm LamTerm
              | As LamTerm Type
              deriving (Show, Eq)

  -- Lambda términos sin nombres.
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
           | Lam (Type,TType) Term
           | BLam TypeV Term
           | Term :!: (Type,TType)
           | Pack (Type,TType) Term (Type,TType)
           | Unpack TypeV Term Term
           | Term ::: (Type,TType)
           deriving (Show, Eq)

  -- Para cada variable de término, tenemos (por posición en la 4-tupla):
  -- 1. Su posición en el contexto, a la hora de imprimirlo.
  -- 2. La profundidad con la que se añadio al contexto,
  -- (la profundidad se refiere a la cantidad de cuantificadores construidos).
  -- 3-4. Su tipo con y sin nombres, respectivamente.
type TermVar = (Int,Int,Type,TType)

  -- Secuencia de variables de términos. 
type TermContext = Vector TermVar

  -- Para cada variable de tipo ligada, tenemos (por posición en la tupla):
  -- 1. Su posición en el contexto. Útil a la hora de imprimirlo.
  -- 2. El nombre.
type BTypeVar = (Int, String)

  -- Secuencia de variables de tipo ligadas.
type BTypeContext = Vector BTypeVar

  -- Tabla de teoremas.
  -- Clave: Nombre del teorema.
  -- Valor: El lambda término de la prueba.
type Teorems = Map String Term

type FTypeVar = String

  -- Secuencia de variables de tipo libres.
type FTypeContext = [FTypeVar]

  --Comandos.
data Command = Ty String Type
             | Ta Tactic
             | Types [String]
             | Definition String BodyDef
             deriving (Show)

data BodyDef = LTerm LamTerm
             | Type TypeDefinition
             | Ambiguous (GenTree String)
             deriving (Show)
             
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

  -- Conjunto de operaciones NO "foldeables".
notFoldeableOps :: [(String, Int, Operands)]
notFoldeableOps = [and_, or_, bottom_]

  -- Operaciones por default, NO "foldeables", donde:
  -- 1. Texto de la operación.
  -- 2. Código que identifica a la operación.
  -- 3. Cantidad de operandos (a lo sumo 2).
and_ = (['/','\\'] , -1, 2)
or_ = (['\\','/'], -2, 2)
bottom_ = ("False", -3, 0)

and_text = fst3 and_
or_text = fst3 or_
bottom_text = fst3 bottom_

and_code = snd3 and_
or_code = snd3 or_
bottom_code = snd3 bottom_

  -- Operaciones por default, "foldeables".
not_text = "~"
iff_text = "<->"

iff_code = 1 :: Int
not_code = 0 :: Int


  -- Operación "foldeable", donde:
  -- 1. Identificador.
  -- 2. Cuerpo de la operación (sin los para todos).
  -- 3. Cantidad de operandos.
  -- 4. Booleano. True sii es una operación binaria infija.
  -- Todas las operaciones que define el usuario son foldeables.
type FoldeableOp = (String, (Type, TType), Operands, Bool)

type FOperations = Vector FoldeableOp

  -- Definición de una "operación".
  -- 1. Cuerpo de la operación.
  -- 2. Cantidad de operandos.
  -- 3. Lista de los nombres de los argumentos.
  -- 4. Boleano. True sii es una operación binaria infija.
type TypeDefinition = (Type, Operands, [String], Bool)

  -- Estado general.
data ProverState = PSt { proof :: Maybe ProofState
                       , global :: ProverGlobal
                       , infixParser :: UsrParser
                       }

  -- Definiciones globales.
data ProverGlobal = PGlobal { fTypeContext :: FTypeContext
                            , teorems :: Teorems             -- Teoremas.
                            , opers :: FOperations           -- Operaciones "foldeables"
                            , conflict :: IntSet             -- Nombres de teoremas conflictivos.
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

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throw errorval
maybeToEither _ (Just normalval) = return normalval

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

getElemIndex :: (a -> Bool) -> Vector a -> Maybe (Int, a)
getElemIndex f v = ifoldl (\r i x -> if f x then Just (i, x) else r) Nothing v
