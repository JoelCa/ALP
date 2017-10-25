module Parser where

import Common
import Text.Megaparsec hiding (State)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Control.Applicative (empty)
import Data.Void (Void)
import Control.Monad.Reader
import qualified Data.Sequence as S (Seq, empty, (<|), (|>), singleton, fromList)
import qualified Control.Exception as E (try)
import Data.List (isSuffixOf)
import Data.Char (isSpace)
import qualified Data.List.NonEmpty as LNE (fromList)

type Parser = Parsec Void String

type ProofCommands = Either ProverException [(EPosition, Command)]

type CommandLineCommand = Either ProverException (Maybe (EPosition,String), [(EPosition,CLICommand)], Maybe (EPosition,String))


interactive :: String
interactive = "<interactive>"

reservedWords = ["Propositions", "Types", "Theorem", "Axiom", "Print", "Check", "forall"
                , "exists",  "let", "in", "as","assumption", "intro", "intros", "split",
                 "left", "right", "apply", "elim", "absurd", "cut", "unfold", "exact",
                 ":load", ":abort", ":quit", ":help", ":save", ":l", ":a", ":q", ":h", ":s"]

reservedSymbols = ["=", "->", ":", "//", "/*", "*/"] --, and_id, or_id, iff_id, not_id]

sc :: Parser ()
sc = L.space space1 empty blockCmnt
  where --lineCmnt  = L.skipLineComment "%%"
        blockCmnt = L.skipBlockComment "(*" "*)"

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
nat = fromInteger <$> lexeme L.decimal

rword :: String -> Parser ()
rword w = try $ string w *> notFollowedBy alphaNumChar *> sc

rsym :: String -> Parser ()
rsym w = try $ string w *> notFollowedBy symbolChar *> sc


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
    p       = (:) <$> sym <*> many sym
    check x = if x `elem` reservedSymbols
                then fail $ "keyword " ++ show x ++ " cannot be an symbolic identifier"
                else return x
    sym = symbolChar <|> char '/' <|> char '\\' <|> char '-'


commandsFromFiles :: [String] -> IO ProofCommands
commandsFromFiles files =
  do content <- mapM (\f -> either Left (\x -> Right (f, x)) <$> (E.try $ readFile f)) files
     case sequence content of
       Right xs ->
         case mapM (\(f,s) -> parse (lexeme space *> commands <* eof) f s) xs of
           Right x -> return $ Right $ concat x
           Left e -> return $ Left $ SyntaxE  e
       Left e -> return $ Left $ FileE e

commands :: Parser [(EPosition, Command)]
commands = many ((\x y -> (x,y)) <$> (getLinePos <$> getPosition) <*> command)
-- commands = do xs <- many p
--               (do x <- p
--                   return (xs++[x])
--                <|> do eof
--                       return xs)
--   where p = (\x y -> (x,y)) <$> (getLinePos <$> getPosition) <*> command

commandsLine :: EPosition -> Parser [(EPosition, Command)]
commandsLine pos = many $ try ((\x -> (pos,x)) <$> command) 

getLinePos :: SourcePos -> EPosition
getLinePos (SourcePos n l c) = (n, unPos l)

newPosition :: String -> Int -> SourcePos
newPosition name line = SourcePos name (mkPos line) pos1

getCommand :: String -> Int -> CommandLineCommand
getCommand s line =
  case parse (cliWithPosition line) interactive s  of
    Right x -> Right x
    Left e -> Left $ SyntaxE  e

cliWithPosition :: Int -> Parser (Maybe (EPosition,String), [(EPosition,CLICommand)], Maybe (EPosition,String))
cliWithPosition line =
  do setPosition (newPosition interactive line)
     lexeme space *> cliCommand <* eof

cliCommand :: Parser (Maybe (EPosition,String), [(EPosition,CLICommand)], Maybe (EPosition,String))
cliCommand = do pos <- getLinePos <$> getPosition
                (do ec <- escapedCommand
                    return (Nothing, [(pos,Escaped ec)], Nothing)
                 <|> do (x,cs,y)  <- langCommands pos
                        return (x, map (\(x,y) -> (x,Lang y)) cs, y))
              

testeo :: Show a => Parser a -> String -> IO ()
testeo p s = case parse p "" s of
               Left e -> putStrLn $ parseErrorPretty e
               Right x -> putStrLn $ show x

-- Retorna una tupla donde:
-- 1. Posible comando incompleto, terminado con un punto.
-- 2. Comandos completos.
-- 3. Posible comando incompleto, NO terminado por un punto.
langCommands :: EPosition -> Parser (Maybe (EPosition,String), [(EPosition,Command)], Maybe (EPosition,String))
langCommands pos =
  do (pre, cs) <- lexeme space *> langCommands' pos
     space
     end <- atEnd
     if end
       then return (pre, cs, Nothing)
       else (do --satisfy (\x -> x /= '.') <?> "comando"
                post <- incompleteCommand1
                return (pre, cs, Just (pos,post)))
       where resto =
               do r <- lexeme $ takeWhileP Nothing (\x -> x /= '.')
                  (do dot
                      unexpected EndOfInput
                   <|> return r) 

langCommands' :: EPosition -> Parser (Maybe (EPosition,String), [(EPosition,Command)])
langCommands' pos =
  do x <- initial
     cs <- commandsLine pos
     case x of
       Just (Left y) -> return (Nothing, (pos,y):cs)
       Just (Right z) -> return (Just (pos,z), cs)
       Nothing -> return (Nothing, cs)
  where initial = do c <- try $ command
                     return $ Just $ Left c
                  <|> do ic <- try $ incompleteCommand0
                         return $ Just $ Right ic
                  <|> return Nothing

-- Parsea una string que termine con un punto, omitiendo
-- los comentarios.
incompleteCommand0 :: Parser String
incompleteCommand0 =
  do c <- lexeme $ takeWhileP Nothing (\x -> (x /= '.') && (x /= '('))
     (do dot
         return $ c ++ ['.']
      <|> do char '('
             rest <- incompleteCommand0
             return $ c ++ ['('] ++ rest
      <|> do end <- atEnd
             if end
             then unexpected EndOfInput
             else do rest <- incompleteCommand0
                     return $ c ++ rest)

incompleteCommand1 :: Parser String
incompleteCommand1 =
  do c <- lexeme $ takeWhileP Nothing (\x -> (x /= '.') && (x /= '('))
     (do dot
         unexpected EndOfInput
      <|> do char '('
             rest <- incompleteCommand1
             return $ c ++ ['('] ++ rest
      <|> do end <- atEnd
             if end
             then return c
             else do rest <- incompleteCommand1
                     return $ c ++ rest)


-- incompleteCommand :: Parser String
-- incompleteCommand =
--   do c <- lexeme $ takeWhileP Nothing (\x -> x /= '.')
--      (do dot
--          return $ c ++ ['.']
--       <|> unexpected EndOfInput)


-- input1 :: Parser String
-- input1 = do c <- takeWhile1P Nothing (\x -> x /= '.')
--             dot
--             return $ c ++ ['.']

--------------------------------------------------------------------------------------
-- Parser de los comandos.
command :: Parser Command
command = do rword "Theorem"
             name <- identifier
             colon
             t <- typeTerm
             dot
             return $ Theorem name t
         <|> do rword "Axiom"
                name <- identifier
                colon
                t <- typeTerm
                dot
                return $ Axiom name t
         <|> do rword "Propositions" <|> rword "Types"
                ps <- sepByCommaSeq identifier
                dot
                return $ Types ps
         <|> try (do tac <- tactic
                     return $ Tac tac)
         <|> do (name, def) <- definition
                return $ Definition name def

escapedCommand :: Parser ECommand
escapedCommand =
  do rword ":quit" <|> rword ":q"
     return Exit
  <|> do rword ":abort" <|> rword ":a"
         return Abort
  <|> do rword ":load" <|> rword ":l"
         names <- many (proofFileName <* space)
         return $ Load names
  <|> do rword ":save" <|> rword ":s"
         name <- fileName
         space
         return $ Save name
  <|> do rword ":help" <|> rword ":h"
         return Help


fileName :: Parser String
fileName = many $ satisfy (not . isSpace)

proofFileName :: Parser String
proofFileName =
  do name <- fileName
     if isSuffixOf ".pr" name
       then return name
       else empty
              

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
unit3 = infixP and_id (\x y -> RenamedType and_id [x,y]) infixOps

infixOps :: Parser Type1
infixOps = do x <- unit4
              (do s <- symbolIdent
                  y <- infixOps
                  return $ RenamedType s [x,y]
               <|> return x)


unit4 :: Parser Type1
unit4 = do rsym not_id
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
         <|> try printAllP
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
printP = tacticOneArg (identifier <|> symbolIdent) "Print" Print

checkP :: Parser Tactic
checkP = tacticOneArg lambTerm "Check" Infer

absurdP :: Parser Tactic
absurdP = tacticType1Arg "absurd" Absurd

cutP :: Parser Tactic
cutP = tacticType1Arg "cut" Cut

existsP :: Parser Tactic
existsP = tacticType1Arg "exists" CExists

printAllP :: Parser Tactic
printAllP = do rword "Print"
               symbol "_"
               dot
               return PrintAll

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
                             return (x, Type ((t, xs), n, False)))
                 <|> do y <- symbolIdent
                        z <- identifier
                        equal
                        t <- typeTerm
                        dot
                        return (y, Type ((t, S.fromList [z, x]), 2, True)))
                 <|> do colon
                        t <- typeTerm
                        dot
                        return (x, EmptyLTerm t)
             <|> do name <- symbolIdent
                    (n, xs) <- seqReverseOrd1 identifier
                    equal
                    t <- typeTerm
                    dot
                    return (name, Type ((t, xs), n, False))

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
type SParser = Parsec Void String

sc2 :: SParser ()
sc2 = L.space space1 empty empty

lexeme2 :: SParser a -> SParser a
lexeme2 = L.lexeme sc2
  
nat2 :: SParser Int
nat2 = fromInteger <$> lexeme2 L.decimal

-- ARREGLAR
-- NO debe tomar cosas de la forma H0024
getHypothesisValue :: String -> Maybe Int
getHypothesisValue = parseMaybe $
                     char 'H' >> nat2


getInt :: String -> Maybe Int
getInt s = parseMaybe nat2 s

--------------------------------------------------------------------------------------
-- Parser para identificar el comando escapado "load".
isLoadOrSaveCommand :: String -> Bool
isLoadOrSaveCommand s = case parse (space *> rword2 ":load" <|> rword2 ":l"
                                     <|> rword2 ":save" <|> rword2 ":s") "" s of
                    Left _ -> False
                    Right _ -> True 

rword2 :: String -> SParser ()
rword2 w = try $ string w *> sc2
