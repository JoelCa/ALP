module Parser where

import Parsing
import Common
import Control.Applicative hiding (many)
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

reservedWords = ["Theorem", "Definition", "forall", "False", "exists", "let", "in", "as"]
reservedSymbols = [':', '.', '[', ']','{','}','(',')']
reservedWords2 = ["=", "\\", "->", and_text, or_text, bottom_text, not_text, iff_text]

-- Identificadores alfa-numéricos (incluido el guión bajo), exceptuando las palabras reservados.
validIdent1 :: Parser String
validIdent1 = vIdent1 reservedWords

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
-- Tampoco puede ser una palabra reservada.
validIdent2 :: Parser String
validIdent2 = vIdent2 reservedSymbols reservedWords

validIdent3 :: Parser String
validIdent3 = vIdent2 reservedSymbols (reservedWords ++ reservedWords2)

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
validSymbol :: Parser String
validSymbol = vSymbol reservedSymbols

opArgs0 :: Parser a -> Parser (Int, [a])
opArgs0 p = do x <- p
               (n, xs) <- opArgs0 p
               return (n+1, x:xs)
            <|> return (0, [])

opArgs1 :: Parser a -> Parser (Int, [a])
opArgs1 p = do x <- p
               (do (n, xs) <- opArgs1 p
                   return (n+1, x:xs)
                <|> return (1, [x]))


getCommand :: String -> UsrOpsParsers -> ProofCommand
getCommand s op = case parse exprTy s op of
                    [(x,[],_)] -> return x
                    _ -> throw SyntaxE

exprTy :: Parser Command
exprTy = do symbol "Theorem"
            name <- validIdent1
            symbol ":"
            t <- typeTerm
            symbol "." -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return $ Ty name t
         <|> do symbol "Props" <|> symbol "Types"
                ps <- sepBy (validIdent1) space
                char '.'
                return $ Types ps
         <|> do tac <- termTac
                return $ Ta tac
         <|> do def <- typeDef
                return $ TypeDef def
         
-- Parser de los tipos (o fórmulas lógicas).
typeTerm :: Parser Type
typeTerm = do u <- unit1                                   -- OBS: los unit primados DEBEN ir antes que unit1,
              (do symbol iff_text                          -- pues unit1 NO falla cuando no puede parsear más.
                  t <- typeTerm
                  return $ RenameTy iff_text 2 [u, t]
               <|> return u)

infixP :: String -> (Type -> Type -> Type)
       -> Parser Type -> Parser Type
infixP s c p = do u <- p
                  (do symbol s
                      t <- infixP s c p
                      return $ c u t
                   <|> return u)

quantifiers :: Parser Type
quantifiers = do symbol "forall"
                 v <- validIdent1
                 symbol ","
                 t <- typeTerm
                 return $ ForAll v t
              <|> do symbol "exists"
                     v <- validIdent1
                     symbol ","
                     t <- typeTerm
                     return $ Exists v t
  
unit1 :: Parser Type
unit1 = infixP "->" Fun unit2

unit2 :: Parser Type
unit2 = infixP or_text (\x y -> RenameTy or_text 2 [x,y]) unit3

unit3 :: Parser Type
unit3 = do infixOps <- get
           infixP and_text (\x y -> RenameTy and_text 2 [x,y]) (runParser infixOps)

unit4 :: Parser Type
unit4 = do symbol not_text
           u <- unit4
           return $ RenameTy not_text 1 [u]
        <|> prefixOps
        <|> unit5                -- OBS: unit5 DEBE ir despues de prefixOps. De lo contrario,
                                 -- el nombre de una operación que se parsea puede ser
                                 -- tomada como un tipo/proposición.
        <|> quantifiers

unit5 :: Parser Type
unit5 = parens typeTerm
        <|> do symbol "False"
               return $ RenameTy bottom_text 0 []
        <|> do v <- validIdent1
               return $ B v

prefixOps :: Parser Type
prefixOps = do x <- (validIdent1 <|> validIdent3)
               (n, xs) <- opArgs1 unit5
               return $ RenameTy x n xs


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
              (do symbol "as"
                  t <- typeTerm
                  return $ As u t
               <|> return u)

unitaryTerm :: Parser LamTerm
unitaryTerm = do x <- validIdent1
                 return $ LVar x
              <|> parens lambTerm

abstraction :: Parser LamTerm
abstraction = do char '\\'
                 v <- validIdent1
                 (do symbol ":"
                     t <- typeTerm
                     symbol "."
                     e <- lambTerm
                     return $ Abs v t e
                  <|> do symbol "."
                         e <- lambTerm
                         return $ BAbs v e)
              <|> do (t, e) <- braces2 (symbol "*" >> typeTerm) lambTerm
                     symbol "as"
                     t' <- typeTerm
                     return $ EPack t e t'
              <|> do symbol "let"
                     (v1, v2) <- braces2 validIdent1 validIdent1
                     symbol "="
                     e1 <- lambTerm
                     symbol "in"
                     e2 <- lambTerm
                     return $ EUnpack v1 v2 e1 e2

-- Parser de definición de tipos.
typeDef :: Parser TypeDefinition
typeDef = do op <- validIdent1
             (n, xs) <- opArgs0 validIdent1
             symbol "="
             t <- typeTerm
             symbol "."
             return (op, n, xs, t, False)
          <|> do op <- validIdent3
                 (n, xs) <- opArgs1 validIdent1
                 symbol "="
                 t <- typeTerm
                 symbol "."
                 return (op, n, xs, t, False)
          <|> do a <- validIdent1
                 op <- validIdent3
                 b <- validIdent1
                 symbol "="
                 t <- typeTerm
                 symbol "."
                 return (op, 2, [a,b], t, True)


-- Parser de las tácticas.
termTac :: Parser Tactic
termTac = assumptionP
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
printP = tacticIdentArg "print" Print

inferP :: Parser Tactic
inferP = tacticOneArg lambTerm "infer" Infer

absurdP :: Parser Tactic
absurdP = tacticTypeArg "absurd" Absurd

cutP :: Parser Tactic
cutP = tacticTypeArg "cut" Cut

existsP :: Parser Tactic
existsP = tacticTypeArg "exists" CExists

unfoldP :: Parser Tactic
unfoldP = do symbol "unfold"
             op <- validIdent2
             (do symbol "in"
                 char 'H'
                 h <- nat
                 symbol "."
                 return $ Unfold op $ Just h
              <|> do symbol "."
                     return $ Unfold op Nothing)

exactP :: Parser Tactic
exactP = do symbol "exact"
            parens $
              do te <- lambTerm
                 char '.'
                 return $ Exact $ LambdaT te
              <|> do ty <- typeTerm
                     char '.'
                     return $ Exact $ TypeT ty

tacticZeroArg :: String -> Tactic -> Parser Tactic
tacticZeroArg s tac = do symbol s
                         char '.'
                         return tac

tacticOneArg :: Parser a -> String -> (a -> Tactic) -> Parser Tactic
tacticOneArg p s tac = do symbol s
                          arg <- p
                          char '.'
                          return $ tac arg

tacticIdentArg :: String -> (String -> Tactic) -> Parser Tactic
tacticIdentArg = tacticOneArg identifier

tacticTypeArg :: String -> (Type -> Tactic) -> Parser Tactic
tacticTypeArg = tacticOneArg typeTerm

tacticIndexArg :: String -> (Int -> Tactic) -> Parser Tactic
tacticIndexArg = tacticOneArg (char 'H' >> nat)

getHypothesisValue :: String -> Maybe Int
getHypothesisValue s = case parse (char 'H' >> nat) s [] of
                         [(x,[],_)] -> return x
                         _ -> Nothing

--------------------------------------------------------------------------------------

-- Genera el parser de la operaciones infijas definidas por el usuario.
-- Argumentos:
-- 1º La nueva operación infija.
-- 2º El parser de operaciones infijas (con más precedencia),
usrInfixParser :: String -> Parser Type -> Parser Type
usrInfixParser s p = infixP s (\x y -> RenameTy s 2 [x, y]) p

basicInfixParser :: Parser Type
basicInfixParser = unit4

--------------------------------------------------------------------------------------

apps :: Parser (GenTree String)
apps = do x <- validIdent1
          xs <- apps'
          return $ Node x xs

apps' :: Parser [GenTree String]
apps' = do x <- validIdent1
           xs <- apps'
           return $ (Node x []) : xs
        <|> do t <- parens apps
               xs <- apps'
               return $ t : xs
        <|> return []
