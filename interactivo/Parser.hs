module Parser where

import Parsing
import Common
import Control.Applicative hiding (many)
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

reservedWords = ["Theorem", "Definition", "forall", "False", "exists", "let", "in", "as"]
reservedSymbols = [':', '.', '[', ']','{','}','(',')']
reservedWords2 = ["=", "\\", "->", and_text, or_text, bottom_text, not_text, iff_text]

-- Realiza el parseo.
-- Argumentos:
-- 1. La string a parsear.
-- 2. El parser de las operaciones definidas por el usuario.
getCommand :: String -> UsrOpsParsers -> ProofCommand
getCommand s op = case parse exprTy s op of
                    [(x,[],_)] -> return x
                    _ -> throw SyntaxE

--------------------------------------------------------------------------------------
-- Parser de los comandos.
exprTy :: Parser Command
exprTy = do symbol "Theorem"
            name <- validIdent1
            symbol ":"
            t <- typeTerm
            symbol "." -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return $ Ty name t
         <|> do symbol "Props" <|> symbol "Types"
                ps <- sepBy (validIdent1) space
                symbol "."
                return $ Types ps
         <|> do tac <- tactic
                return $ Ta tac
         <|> do (name, def) <- definition
                return $ Definition name def

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

prefixOps :: Parser Type
prefixOps = applications (\_ -> opArgs1 unit5) (validIdent1 <|> validIdent3) B addArgs

-- prefixOps :: Parser Type
-- prefixOps = do op <- parcialOp
--                (n, xs) <- opArgs1 unit5
--                return $ addArgs op n xs

-- parcialOp :: Parser Type
-- parcialOp = do v <- validIdent1 <|> validIdent3
--                return $ B v
--             <|> parens prefixOps

addArgs :: Type -> (Int, [Type]) -> Type
addArgs (B op) (n,xs) = RenameTy op n xs
addArgs (RenameTy op m ys) (n,xs) = RenameTy op (m + n) (ys ++ xs)

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
            r <- do xs <- ambiguousApp <|> parens ambiguousApp
                    return $ Appl xs
                 <|> do te <- lambTerm
                        return $ LamT te
                 <|> do ty <- typeTerm
                        return $ T ty
            symbol "."
            return $ Exact r

--------------------------------------------------------------------------------------
-- Parser de una definición.
definition :: Parser (String, BodyDef)
definition = do x <- validIdent1
                (do symbol "="
                    ap <- ambiguousApp
                    symbol "."
                    return (x, Ambiguous ap)
                 <|> do (n, xs) <- opArgs0 validIdent1
                        symbol "="
                        t <- typeTerm
                        symbol "."
                        return (x, Type (t, n, reverse xs, False))
                 <|> do symbol "="
                        lt <- lambTerm
                        symbol "."
                        return (x, LTerm lt)
                 <|> do y <- validIdent3
                        z <- validIdent1
                        symbol "="
                        t <- typeTerm
                        symbol "."
                        return (y, Type (t, 2, [z, x], True)))
             <|> do name <- validIdent3
                    (n, xs) <- opArgs1 validIdent1
                    symbol "="
                    t <- typeTerm
                    symbol "."
                    return (name, Type (t, n, reverse xs, False))


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
-- Parser de aplicaciones "ambiguas".                            
ambiguousApp :: Parser (GenTree String)
ambiguousApp = applications ambiguousArgs validIdent1 (\x -> Node x []) appendApp
  
-- apps :: Parser (GenTree String)
-- apps = do par <- parcialApp
--           xs <- apps'
--           return $ appendApp par xs

-- parcialApp :: Parser (GenTree String)
-- parcialApp = do v <- validIdent1
--                 return $ Node v []
--              <|> parens apps

appendApp :: (GenTree String) -> [GenTree String] -> (GenTree String)
appendApp (Node x xs) ys = Node x (xs ++ ys)

ambiguousArgs :: Parser (GenTree String) -> Parser [GenTree String]
ambiguousArgs p = do a <- p
                     as <- ambiguousArgs p
                     return $ a : as
                  <|> return []

--------------------------------------------------------------------------------------
-- Parser del nombre de una hipótesis.
getHypothesisValue :: String -> Maybe Int
getHypothesisValue s = case parse (char 'H' >> nat) s [] of
                         [(x,[],_)] -> return x
                         _ -> Nothing

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
-- Funciones auxiliares.

-- Parser de identificadores.
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

-- Añade el parser de una operación infija.
infixP :: String -> (Type -> Type -> Type)
       -> Parser Type -> Parser Type
infixP s c p = do u <- p
                  (do symbol s
                      t <- infixP s c p
                      return $ c u t
                   <|> return u)

-- Funciones auxiliares para el parser de las tácticas.
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
