module Parser where

import Common
import Text.Megaparsec hiding (State)
import qualified Text.Megaparsec.Lexer as L
import qualified Text.Megaparsec.String as S
import Control.Applicative (empty)
import Control.Monad (void)
import Control.Monad.Reader

type ProofCommand = Either ProofExceptions Command

reservedWords = ["Propositions", "Types", "Theorem", "Print", "forall", "exists", "let", "in",
                 "as", "False", "assumption", "intro", "intros", "split", "left",
                 "right", "apply", "elim", "absurd", "cut", "unfold", "exact"]

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
braces2 p1 p2 = do symbol "{"
                   x <- p1
                   symbol ","
                   y <- p2
                   symbol "}"
                   return (x,y)
                   
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
    p       = (:) <$> letterChar <*> many alphaNumChar
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


getCommand :: String -> UsrParser -> ProofCommand
getCommand s p = case runReader (runParserT (space *> exprTy) "" s) p of
                   Right x -> Right x
                   Left e -> Left $ SyntaxE $ parseErrorPretty e

testeo :: Show a => Parser a -> String -> IO ()
testeo p s = case runReader (runParserT p "" s) (PP unit4) of
               Left e -> putStrLn $ parseErrorPretty e
               Right x -> putStrLn $ show x

--------------------------------------------------------------------------------------
-- Parser de los comandos.
exprTy :: Parser Command
exprTy = do rword "Theorem"
            name <- identifier
            colon
            t <- typeTerm
            dot
            return $ Ty name t
         <|> do rword "Propositions" <|> rword "Types"
                ps <- identifier `sepBy` comma
                dot
                return $ Types ps
         <|> do tac <- tactic
                return $ Ta tac
         <|> do (name, def) <- definition
                return $ Definition name def

--------------------------------------------------------------------------------------
-- Parser del lambda término con nombre.
lambTerm :: Parser LamTerm
lambTerm = abstraction
           <|> do t <- app
                  (do a <- abstraction
                      return $ App t a
                   <|> return t)

app :: Parser LamTerm
app = do x <- unitTerm
         f <- app'
         return $ f x

app' :: Parser (LamTerm -> LamTerm)
app' = do t <- brackets typeTerm
          f <- app'
          return $ \a -> f $ BApp a t
       <|> do u <- unitTerm
              f <- app'
              return $ \a -> f $ App a u
       <|> return id

unitTerm :: Parser LamTerm
unitTerm = do u <- unitaryTerm
              (do rword "as"
                  t <- typeTerm
                  return $ As u t
               <|> return u)

unitaryTerm :: Parser LamTerm
unitaryTerm = do x <- identifier
                 return $ LVar x
              <|> parens lambTerm

abstraction :: Parser LamTerm
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

typeTerm :: Parser Type
typeTerm = do u <- unit1
              (do symbol iff_text
                  t <- typeTerm
                  return $ RenameTy iff_text 2 [u, t]
               <|> return u)
  
unit1 :: Parser Type
unit1 = infixP "->" Fun unit2

unit2 :: Parser Type
unit2 = infixP or_text (\x y -> RenameTy or_text 2 [x,y]) unit3

unit3 :: Parser Type
unit3 = do infixOps <- ask
           infixP and_text (\x y -> RenameTy and_text 2 [x,y]) (getParser infixOps)

unit4 :: Parser Type
unit4 = do symbol not_text
           u <- unit4
           return $ RenameTy not_text 1 [u]
        <|> try prefixOps
        <|> unit5                -- OBS: unit5 DEBE ir despues de prefixOps. De lo contrario,
                                 -- el nombre de una operación que se parsea puede ser
                                 -- tomada como un tipo/proposición.
        <|> quantifiers

unit5 :: Parser Type
unit5 = parens typeTerm
        <|> do rword "False"
               return $ RenameTy bottom_text 0 []
        <|> do v <- identifier
               return $ B v

quantifiers :: Parser Type
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

prefixOps :: Parser Type
prefixOps = applications (\_ -> opArgs1 unit5) (identifier <|> symbolIdent) B addArgs

addArgs :: Type -> (Int, [Type]) -> Type
addArgs (B op) (n,xs) = RenameTy op n xs
addArgs (RenameTy op m ys) (n,xs) = RenameTy op (m + n) (ys ++ xs)


-- Añade el parser de una operación infija.
infixP :: String -> (Type -> Type -> Type)
       -> Parser Type -> Parser Type
infixP s c p = do u <- p
                  (do symbol s
                      t <- infixP s c p
                      return $ c u t
                   <|> return u)

-- Parser de los argumentos de una operación.
-- Cero, o más argumentos.
opArgs0 :: Parser a -> Parser (Int, [a])
opArgs0 p = do x <- p
               (n, xs) <- opArgs0 p
               return (n+1, x:xs)
            <|> return (0, [])

-- Uno, o más argumentos.
opArgs1 :: Parser a -> Parser (Int, [a])
opArgs1 p = do x <- p
               (do (n, xs) <- opArgs1 p
                   return (n+1, x:xs)
                <|> return (1, [x]))

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
         <|> inferP
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

inferP :: Parser Tactic
inferP = tacticOneArg lambTerm "infer" Infer

absurdP :: Parser Tactic
absurdP = tacticTypeArg "absurd" Absurd

cutP :: Parser Tactic
cutP = tacticTypeArg "cut" Cut

existsP :: Parser Tactic
existsP = tacticTypeArg "exists" CExists

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
            r <- do xs <- ambiguousApp <|> parens ambiguousApp
                    return $ Appl xs
                 <|> do te <- lambTerm
                        return $ LamT te
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

tacticTypeArg :: String -> (Type -> Tactic) -> Parser Tactic
tacticTypeArg = tacticOneArg typeTerm

tacticIndexArg :: String -> (Int -> Tactic) -> Parser Tactic
tacticIndexArg = tacticOneArg (char 'H' >> nat)

--------------------------------------------------------------------------------------
-- Parser de una definición.

definition :: Parser (String, BodyDef)
definition = do x <- identifier
                (try (equal >>
                       (do ap <- ambiguousApp
                           dot
                           return (x, Ambiguous ap))
                        <|> do lt <- lambTerm
                               dot
                               return (x, LTerm lt))
                 <|> try (do (n, xs) <- opArgs0 identifier
                             equal
                             t <- typeTerm
                             dot
                             return (x, Type (t, n, reverse xs, False)))
                 <|> do y <- symbolIdent
                        z <- identifier
                        equal
                        t <- typeTerm
                        dot
                        return (y, Type (t, 2, [z, x], True)))
             <|> do name <- symbolIdent
                    (n, xs) <- opArgs1 identifier
                    equal
                    t <- typeTerm
                    dot
                    return (name, Type (t, n, reverse xs, False))

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

--------------------------------------------------------------------------------------
-- Construcción del parser de las operaciones del usuario.

-- Genera el parser de la operaciones infijas definidas por el usuario.
-- Argumentos:
-- 1º La nueva operación infija.
-- 2º El parser de operaciones infijas (con más precedencia),
usrInfixParser :: String -> Parser Type -> Parser Type
usrInfixParser s p = infixP s (\x y -> RenameTy s 2 [x, y]) p

basicInfixParser :: Parser Type
basicInfixParser = unit4

--------------------------------------------------------------------------------------
-- PRUEBAS

prueba1 :: Parser String
prueba1 = do i <- identifier
             symbol "."
             j <- identifier
             return $ i ++ j
              

unitPrueba :: Parser Type
unitPrueba = do u <- identifier
                return $ B u

trying :: String -> ParsecT Dec String (Reader [String]) a -> ParsecT Dec String (Reader [String]) a
trying s p = local (++ ["trying " ++ s]) p


test :: ParsecT Dec String (Reader [String]) [String]
test = (trying "'a'" $ char 'a' >> ask)
   <|> (trying "'b'" $ char 'b' >> ask)

prueba2 = show $ runReader (runParserT test "" "b") ["jojo"]

run :: Show a => Parser a -> String -> IO ()
run p s = case runReader (runParserT p "" s) (PP unit4) of
            Left e -> putStrLn $ parseErrorPretty e
            Right x -> putStrLn $ show x

