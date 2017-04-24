module Parser where

import Parsing
import Common
import Control.Applicative
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

reservedWords = ["Theorem", "Definition", "forall", "False", "exists", "let", "in"]
reservedSymbols = [':', '.', '\\', '[', ']','{','}']

-- Identificadores alfa-numéricos (incluido el guión bajo), exceptuando las palabras reservados.
validIdent1 :: Parser String
validIdent1 = vIdent1 reservedWords

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
-- Tampoco puede ser una palabra reservada.
validIdent2 :: Parser String
validIdent2 = vIdent2 reservedSymbols reservedWords

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
validSymbol :: Parser String
validSymbol = vSymbol reservedSymbols

getCommand :: String -> UsrOpsParsers -> ProofCommand
getCommand s op = case parse exprTy s op of
                    [(x,[],y)] -> return x
                    _ -> throw SyntaxE

exprTy :: Parser Command
exprTy = do symbol "Theorem"
            name <- validIdent1
            symbol ":"
            t <- typeTerm
            symbol "." -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return $ Ty name t
         <|> do symbol "Props"
                ps <- sepBy (validIdent1) space
                char '.'
                return $ Props ps
         <|> do tac <- termTac
                return $ Ta tac
         <|> do def <- typeDef
                return $ TypeDef def
         
-- Parser de los tipos (o fórmulas lógicas).
typeTerm :: Parser Type
typeTerm = do u <- unit1                                   -- OBS: los unit primados DEBEN ir antes que unit1,
              (do symbol iff_text                          -- pues unit1 NO falla cuando no puede parsear más.
                  t <- typeTerm
                  return $ RenameTy iff_text [u, t]
               <|> return u)

infixParser :: String -> (Type -> Type -> Type)
            -> Parser Type -> Parser Type
infixParser s c p = do u <- p
                       (do symbol s
                           t <- infixParser s c p
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
unit1 = infixParser "->" Fun unit2

unit2 :: Parser Type
unit2 = infixParser or_text (\x y -> RenameTy or_text [x,y]) unit3

unit3 :: Parser Type
unit3 = do [_, _, p3, _] <- get
           infixParser and_text (\x y -> RenameTy and_text [x,y]) (runParser p3)

unit4 :: Parser Type
unit4 = do symbol not_text
           u <- unit4
           return $ RenameTy not_text [u]
        <|> do [_, p2, _, _] <- get
               runParser p2   -- OJO! El nombre de la operación que se parsea puede ser
                              -- tomada como una proposición.
                              -- Por eso, lo ponemos antes del caso "unit5"
        <|> unit5
        <|> quantifiers

unit5 :: Parser Type
unit5 = parens typeTerm
        <|> do v <- validIdent1
               return $ B v
        <|> do symbol "False"
               return $ RenameTy bottom_text []
        <|> do [p1, _, _, _] <- get
               runParser p1


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
unitTerm = do x <- validIdent1
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
typeDef :: Parser (String, Type, Operands, Bool)
typeDef = do symbol "Definition"
             (do op <- validIdent2
                 (do a <- validIdent1
                     (do b <- validIdent1
                         symbol ":="
                         t <- typeTerm
                         symbol "."
                         return (op, ForAll a $ ForAll b t, Binary, False))
                      <|> do symbol ":="
                             t <- typeTerm
                             symbol "."
                             return (op, ForAll a t, Unary, False))
                  <|> do symbol ":="
                         t <- typeTerm
                         symbol "."
                         return (op, t, Empty, False))
               <|> do a <- validIdent1
                      op <- validSymbol
                      b <- validIdent1
                      symbol ":="
                      t <- typeTerm
                      symbol "."
                      return (op, ForAll a $ ForAll b t, Binary, True)


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
applyP = tacticIdentArg "apply" Apply

elimP :: Parser Tactic
elimP = tacticIdentArg "elim" Elim

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
                 h <- identifier
                 symbol "."
                 return $ Unfold op $ Just h
              <|> do symbol "."
                     return $ Unfold op Nothing)

exactP :: Parser Tactic
exactP = do symbol "exact"
            (do ty <- typeTerm
                char '.'
                return $ Exact $ Left ty
             <|> do te <- lambTerm
                    char '.'
                    return $ Exact $ Right te)

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

--------------------------------------------------------------------------------------

-- Genera el parser de la operacion infija definida por el usuario, donde
-- NO hay "para todos" sin paréntesis.
-- Argumentos:
-- 1º La nueva operación infija.
-- 2º El parser de operaciones infijas (con más precedencia),
-- donde NO hay "para todos" sin paréntesis.
usrInfixParserNotP :: String -> Parser Type -> Parser Type
usrInfixParserNotP s p = infixParser s (\x y -> RenameTy s [x, y]) p

-- Genera el parser de la operación infijas definida por el usuario, donde
-- hay "para todos" sin paréntesis.
-- Argumentos:
-- 1º Identificador de la op.
-- 2º El parser de operaciones infijas (con más precedencia),
-- donde NO hay "para todos" sin paréntesis.
-- 3º El parser de operaciones infijas (con más precedencia),
-- con "para todos" sin paréntesis, previo.
usrInfixParserP :: String -> Parser Type -> Parser Type -> Parser Type
usrInfixParserP s p1 p2 = infixParser' s (\x y -> RenameTy s [x, y]) p1 p2              

usrConstParser :: String -> Parser Type -> Parser Type
usrConstParser s p =
  do symbol s
     return $ RenameTy s []
  <|> p

usrUnaryPrefixParser :: String -> Parser Type -> Parser Type
usrUnaryPrefixParser s p =
  do symbol s
     u <- unit5
     return $ RenameTy s [u]
  <|> p

usrBinaryPrefixParser :: String -> Parser Type -> Parser Type
usrBinaryPrefixParser s p =
  do symbol s
     u <- unit5
     u' <- unit5
     return $ RenameTy s [u, u']
  <|> p

basicInfixParser :: Parser Type
basicInfixParser = unit4

emptyParser :: Parser Type
emptyParser = empty
