module Parser where

import Common
import DefaultOperators
import Text.Megaparsec hiding (State)
import qualified Text.Megaparsec.Lexer as L
import qualified Text.Megaparsec.String as S
import Control.Applicative (empty)
import Control.Monad (void)
import Control.Monad.Reader
import qualified Data.Sequence as S (Seq, empty, (<|), (|>), singleton, fromList)
import qualified Control.Exception as E (try)
import Data.List (isSuffixOf)
import Data.Char (isSpace)
  
type UsrParser = ParserParser Type1

type Parser = ParsecT Dec String (Reader UsrParser)

newtype ParserParser a = PP { getParser :: Parser a }

type ProofCommands = Either ProofException [(SourcePos, Command)]

type CommandLineCommand = Either ProofException (SourcePos, CLICommand)


emptyPos = initialPos ""

reservedWords = ["Propositions", "Types", "Theorem", "Print", "Check", "forall", "exists",
                 "let", "in", "as", "False", "assumption", "intro", "intros", "split",
                 "left", "right", "apply", "elim", "absurd", "cut", "unfold", "exact"]

reservedSymbols = ["=", "~"]

sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt empty
  where lineCmnt  = L.skipLineComment "//"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces2 :: Parser a -> Parser b -> Parser (a, b)
braces2 p1 p2 = between (symbol "{") (symbol "}")
                (do x <- p1
                    symbol ","
                    y <- p2
                    return (x,y))

comma :: Parser String
comma = symbol ","

colon :: Parser String
colon = symbol ":"

dot :: Parser String
dot = symbol "."

equal :: Parser String
equal = symbol "="

nat :: Parser Int
nat = fromInteger <$> lexeme L.integer

rword :: String -> Parser ()
rword w = try $ string w *> notFollowedBy alphaNumChar *> sc

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many (alphaNumChar <|> char '_')
    check x = if x `elem` reservedWords
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

symbolIdent :: Parser String
symbolIdent = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> symbolChar <*> many symbolChar
    check x = if x `elem` reservedSymbols
                then fail $ "keyword " ++ show x ++ " cannot be an symbolic identifier"
                else return x


commandsFromFile :: String -> UsrParser -> IO ProofCommands
commandsFromFile file p =
  do content <- E.try $ readFile file
     case content of
       Right r ->
         case runReader (runParserT (space *> commands) file r) p of
           Right x -> return $ Right x
           Left e -> return $ Left $ SyntaxE  e
       Left e -> return $ Left $ FileE e


commands :: Parser [(SourcePos, Command)]
commands = many ((\x y -> (x,y)) <$> getPosition <*> command)

double :: Monad m => m a -> m b -> m (a,b)
double p1 p2 = do x <- p1
                  y <- p2
                  return (x, y)
          

getCommand :: String -> UsrParser -> CommandLineCommand
getCommand s p = case runReader (runParserT (space *> ((\ x -> (initialPos "", x)) <$> cliCommand) <* eof) "" s) p of
                      Right x -> Right x
                      Left e -> Left $ SyntaxE  e

cliCommand :: Parser CLICommand
cliCommand = do c <- command
                return $ Lang c
             <|> do ec <- escapedCommand
                    return $ Escaped ec

testeo :: Show a => Parser a -> String -> IO ()
testeo p s = case runReader (runParserT p "" s) (PP unit4) of
               Left e -> putStrLn $ parseErrorPretty e
               Right x -> putStrLn $ show x

--------------------------------------------------------------------------------------
-- Parser de los comandos.
command :: Parser Command
command = do rword "Theorem"
             name <- identifier
             colon
             t <- typeTerm
             dot
             return $ Ty name t
         <|> do rword "Propositions" <|> rword "Types"
                ps <- sepByCommaSeq identifier
                dot
                return $ Types ps
         <|> do tac <- tactic
                return $ Ta tac
         <|> do (name, def) <- definition
                return $ Definition name def

escapedCommand :: Parser ECommand
escapedCommand =
  do string ":quit" <|> string ":q"
     return Exit
  <|> do string ":reset" <|> string ":r"
         return Reset
  <|> do string ":load" <|> string ":l"
         spaceChar
         name <- fileName
         return $ Load name

-- VER
fileName :: Parser String
fileName = do name <- many $ satisfy (not . isSpace)
              if isSuffixOf ".pr" name
                then return name
                else return (name ++ ".pr")
              

--------------------------------------------------------------------------------------
-- Parser del lambda término con nombre.
lambTerm :: Parser LTerm1
lambTerm = abstraction
           <|> do t <- app
                  (do a <- abstraction
                      return $ t :@: a
                   <|> return t)

app :: Parser LTerm1
app = do x <- unitTerm
         f <- app'
         return $ f x

app' :: Parser (LTerm1 -> LTerm1)
app' = do t <- brackets typeTerm
          f <- app'
          return $ \a -> f $ a :!: t
       <|> do u <- unitTerm
              f <- app'
              return $ \a -> f $ a :@: u
       <|> return id

unitTerm :: Parser LTerm1
unitTerm = do u <- unitaryTerm
              (do rword "as"
                  t <- typeTerm
                  return $ u ::: t
               <|> return u)

unitaryTerm :: Parser LTerm1
unitaryTerm = do x <- identifier
                 return $ LVar x
              <|> parens lambTerm

abstraction :: Parser LTerm1
abstraction = do symbol "\\"
                 v <- identifier
                 (do colon
                     t <- typeTerm
                     dot
                     e <- lambTerm
                     return $ Abs v t e
                  <|> do dot
                         e <- lambTerm
                         return $ BAbs v e)
              <|> do (t, e) <- braces2 (symbol "*" *> typeTerm) lambTerm
                     rword "as"
                     t' <- typeTerm
                     return $ EPack t e t'
              <|> do rword "let"
                     (v1, v2) <- braces2 identifier identifier
                     equal
                     e1 <- lambTerm
                     rword "in"
                     e2 <- lambTerm
                     return $ EUnpack v1 v2 e1 e2


--------------------------------------------------------------------------------------
-- Parser de los tipos (o fórmulas lógicas).

typeTerm :: Parser Type1
typeTerm = do u <- unit1
              (do symbol iff_id
                  t <- typeTerm
                  return $ RenamedType iff_id [u, t]
               <|> return u)
  
unit1 :: Parser Type1
unit1 = infixP "->" Fun unit2

unit2 :: Parser Type1
unit2 = infixP or_id (\x y -> RenamedType or_id [x,y]) unit3

unit3 :: Parser Type1
unit3 = do infixOps <- ask
           infixP and_id (\x y -> RenamedType and_id [x,y]) (getParser infixOps)

unit4 :: Parser Type1
unit4 = do symbol not_id
           u <- unit4
           return $ RenamedType not_id [u]
        <|> try prefixOps
        <|> unit5                -- OBS: unit5 DEBE ir despues de prefixOps. De lo contrario,
                                 -- el nombre de una operación que se parsea puede ser
                                 -- tomada como un tipo/proposición.
        <|> quantifiers

unit5 :: Parser Type1
unit5 = parens typeTerm
        <|> do rword "False"
               return $ RenamedType bottom_id []
        <|> do v <- identifier
               return $ TVar v

quantifiers :: Parser Type1
quantifiers = do rword "forall"
                 v <- identifier
                 comma
                 t <- typeTerm
                 return $ ForAll v t
              <|> do rword "exists"
                     v <- identifier
                     comma
                     t <- typeTerm
                     return $ Exists v t

prefixOps :: Parser Type1
prefixOps = applications (\_ -> sepBy1 unit5 space) (identifier <|> symbolIdent) TVar addArgs

addArgs :: Type1 -> [Type1] -> Type1
addArgs (TVar op) xs = RenamedType op xs
addArgs (RenamedType op ys) xs = RenamedType op (ys ++ xs)


-- Añade el parser de una operación infija.
infixP :: String -> (Type1 -> Type1 -> Type1)
       -> Parser Type1 -> Parser Type1
infixP s c p = do u <- p
                  (do symbol s
                      t <- infixP s c p
                      return $ c u t
                   <|> return u)

-- Parser de una secuencia de expresiones, separadas por espacios.

-- Considera cero, o más expresiones.
-- Retorna la secuencia leida en el orden inverso.
seqReverseOrd0 :: Parser a -> Parser (Int, S.Seq a)
seqReverseOrd0 p = do x <- p
                      (n, xs) <- seqReverseOrd0 p
                      return (n+1, xs S.|> x)
                   <|> return (0, S.empty)

-- Considera una, o más expresiones.
-- Retorna la secuencia leida en el orden inverso.
seqReverseOrd1 :: Parser a -> Parser (Int, S.Seq a)
seqReverseOrd1 p = do x <- p
                      (do (n, xs) <- seqReverseOrd1 p
                          return (n+1, xs S.|> x)
                       <|> return (1, S.singleton x))

sepByCommaSeq :: Parser a -> Parser (S.Seq a)
sepByCommaSeq p = do x <- p
                     (do xs <- comma >> sepByCommaSeq p
                         return (x S.<| xs)
                      <|> return (S.singleton x))


--------------------------------------------------------------------------------------
-- Parser de aplicaciones (genérico).
applications :: (Parser a -> Parser b) -> Parser u -> (u -> a) -> (a -> b -> a) -> Parser a
applications args unit c appendApp =
  do par <- app
     x <- args app
     return $ appendApp par x
     where
       app =
         do v <- unit
            return $ c v
         <|> (parens $ applications args unit c appendApp)

--------------------------------------------------------------------------------------
-- Parser de las tácticas.
tactic :: Parser Tactic
tactic = assumptionP
         <|> applyP
         <|> elimP
         <|> introP
         <|> introsP
         <|> splitP
         <|> leftP
         <|> rightP
         <|> printP
         <|> exactP
         <|> existsP
         <|> checkP
         <|> unfoldP
         <|> absurdP
         <|> cutP

assumptionP :: Parser Tactic
assumptionP = tacticZeroArg "assumption" Assumption

introP :: Parser Tactic
introP = tacticZeroArg "intro" Intro

introsP :: Parser Tactic
introsP = tacticZeroArg "intros" Intros

splitP :: Parser Tactic
splitP = tacticZeroArg "split" Split

leftP :: Parser Tactic
leftP = tacticZeroArg "left" CLeft

rightP :: Parser Tactic
rightP = tacticZeroArg "right" CRight

applyP :: Parser Tactic
applyP = tacticIndexArg "apply" Apply

elimP :: Parser Tactic
elimP = tacticIndexArg "elim" Elim

printP :: Parser Tactic
printP = tacticIdentArg "Print" Print

checkP :: Parser Tactic
checkP = tacticOneArg lambTerm "Check" Infer

absurdP :: Parser Tactic
absurdP = tacticType1Arg "absurd" Absurd

cutP :: Parser Tactic
cutP = tacticType1Arg "cut" Cut

existsP :: Parser Tactic
existsP = tacticType1Arg "exists" CExists

unfoldP :: Parser Tactic
unfoldP = do rword "unfold"
             op <- identifier <|> symbolIdent
             (do rword "in"
                 char 'H'
                 h <- nat
                 dot
                 return $ Unfold op $ Just h
              <|> do dot
                     return $ Unfold op Nothing)

exactP :: Parser Tactic
exactP = do rword "exact"
            r <- try (do xs <- ambiguousApp <|> parens ambiguousApp
                         return $ Appl xs)
                 <|> try (do te <- lambTerm
                             return $ LamT te)
                 <|> do ty <- typeTerm
                        return $ T ty
            dot
            return $ Exact r

-- Funciones auxiliares para el parser de las tácticas.
tacticZeroArg :: String -> Tactic -> Parser Tactic
tacticZeroArg s tac = do rword s
                         dot
                         return tac

tacticOneArg :: Parser a -> String -> (a -> Tactic) -> Parser Tactic
tacticOneArg p s tac = do rword s
                          arg <- p
                          dot
                          return $ tac arg

tacticIdentArg :: String -> (String -> Tactic) -> Parser Tactic
tacticIdentArg = tacticOneArg identifier

tacticType1Arg :: String -> (Type1 -> Tactic) -> Parser Tactic
tacticType1Arg = tacticOneArg typeTerm

tacticIndexArg :: String -> (Int -> Tactic) -> Parser Tactic
tacticIndexArg = tacticOneArg (char 'H' >> nat)

--------------------------------------------------------------------------------------
-- Parser de una definición.

definition :: Parser (String, BodyDef)
definition = do x <- identifier
                (try (equal >>
                       (try (do ap <- ambiguousApp
                                dot
                                return (x, Ambiguous ap)))
                        <|> do lt <- lambTerm
                               dot
                               return (x, LTerm lt))
                 <|> try (do (n, xs) <- seqReverseOrd0 identifier
                             equal
                             t <- typeTerm
                             dot
                             return (x, Type (t, n, xs, False)))
                 <|> do y <- symbolIdent
                        z <- identifier
                        equal
                        t <- typeTerm
                        dot
                        return (y, Type (t, 2, S.fromList [z, x], True)))
             <|> do name <- symbolIdent
                    (n, xs) <- seqReverseOrd1 identifier
                    equal
                    t <- typeTerm
                    dot
                    return (name, Type (t, n, xs, False))

--------------------------------------------------------------------------------------
-- Parser de aplicaciones "ambiguas".                            
ambiguousApp :: Parser (GenTree String)
ambiguousApp = applications ambiguousArgs identifier (\x -> Node x []) appendApp

appendApp :: (GenTree String) -> [GenTree String] -> (GenTree String)
appendApp (Node x xs) ys = Node x (xs ++ ys)

ambiguousArgs :: Parser (GenTree String) -> Parser [GenTree String]
ambiguousArgs p = do a <- p
                     as <- ambiguousArgs p
                     return $ a : as
                  <|> return []

--------------------------------------------------------------------------------------
-- Parser del nombre de una hipótesis.
sc2 :: S.Parser ()
sc2 = L.space (void spaceChar) empty empty

lexeme2 :: S.Parser a -> S.Parser a
lexeme2 = L.lexeme sc2

nat2 :: S.Parser Int
nat2 = fromInteger <$> lexeme2 L.integer

getHypothesisValue :: String -> Maybe Int
getHypothesisValue s = parseMaybe (char 'H' >> nat2) s

getInt :: String -> Maybe Int
getInt s = parseMaybe nat2 s

--------------------------------------------------------------------------------------
-- Construcción del parser de las operaciones del usuario.

-- Genera el parser de la operaciones infijas definidas por el usuario.
-- Argumentos:
-- 1º La nueva operación infija.
-- 2º El parser de operaciones infijas (con más precedencia),
usrInfixParser :: String -> Parser Type1 -> UsrParser
usrInfixParser s p = PP $ infixP s (\x y -> RenamedType s [x, y]) p

basicInfixParser :: UsrParser
basicInfixParser = PP unit4
