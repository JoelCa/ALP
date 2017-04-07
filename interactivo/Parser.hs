module Parser where

import Parsing
import Common
import Control.Applicative
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

reservedWords = ["Theorem", "Definition", "forall", "False"]
reservedSymbols = [':', '.', '\\', '[', ']']

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
typeTerm = do u <- unit1
              (do symbol iff_text
                  t <- typeTerm
                  return $ RenameTy iff_text [u, t]
               <|> return u)
           <|> do symbol "forall"
                  v <- validIdent1
                  symbol ","
                  t <- typeTerm
                  return $ ForAll v t

unit1 :: Parser Type
unit1 = do u <- unit2
           (do symbol "->"
               t <- unit1
               return $ Fun u t
            <|> return u)

unit2 :: Parser Type
unit2 = do u <- unit3
           (do symbol or_text
               t <- unit2
               return $ RenameTy or_text [u, t]
            <|> return u)

unit3 :: Parser Type
unit3 = do [_,_,p3] <- get
           u <- runParser p3
           (do symbol and_text
               t <- unit3
               return $ RenameTy and_text [u, t]
            <|> return u)

unit4 :: Parser Type
unit4 = do symbol not_text
           u <- unit4
           return $ RenameTy not_text [u]
        <|> do [_, p2, _] <- get
               runParser p2   -- OJO! El nombre de la operación que se parsea puede ser
                              -- tomada como una proposición.
                              -- Por eso, lo ponemos antes del caso "unit5"
        <|> unit5

unit5 :: Parser Type
unit5 = parens typeTerm
        <|> do v <- validIdent1
               return $ B v
        <|> do symbol "False"
               return $ RenameTy bottom_text []
        <|> do [p1, _, _] <- get
               runParser p1

-- prefixConst :: FOperations -> Parser Type
-- prefixConst [] = empty
-- prefixConst ((s,_,Empty,False):xs) =
--   do symbol s
--      return $ RenameTy s []
--   <|> prefixConst xs
-- prefixConst (_:xs) = prefixConst xs

-- prefixOps :: FOperations -> Parser Type
-- prefixOps [] = empty
-- prefixOps ((s,_,Unary,False):xs) =
--   do symbol s
--      u <- unit5
--      return $ RenameTy s [u]
--   <|> prefixOps xs
-- prefixOps ((s,_,Binary,False): xs) =
--   do symbol s
--      u <- unit5
--      u' <- unit5
--      return $ RenameTy s [u, u']
--   <|> prefixOps xs
-- prefixOps (_:xs) =
--   prefixOps xs

-- Parser del lambda término con nombre.
lambTerm :: Parser LamTerm
lambTerm = abstraction
           <|> do t <- lterm
                  (do a <- abstraction
                      return $ App t a
                   <|> return t)

lterm :: Parser LamTerm
lterm = do x <- unitTerm
           f <- lterm'
           return $ f x

lterm' :: Parser (LamTerm -> LamTerm)
lterm' = do  x <- unitTerm
             f <- lterm'
             return $ \a -> f $ App a x
         <|> return id

unitTerm :: Parser LamTerm
unitTerm = do x <- unitT
              f <- unitTerm'
              return $ f x

unitTerm' :: Parser (LamTerm -> LamTerm)
unitTerm' = do symbol "["
               t <- typeTerm
               symbol "]"
               f <- unitTerm'
               return $ \a -> f $ BApp a t
            <|> return id

unitT :: Parser LamTerm
unitT = do x <- validIdent1
           return $ LVar x
        <|> parens lambTerm

abstraction :: Parser LamTerm
abstraction = do char '\\'
                 v <- validIdent1
                 symbol ":"
                 t <- typeTerm
                 symbol "."
                 e <- lambTerm
                 return $ Abs v t e
              <|> do char '\\'
                     v <- validIdent1
                     symbol "."
                     e <- lambTerm
                     return $ BAbs v e

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
          <|> inferP
          <|> unfoldP


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

tacticIdentArg :: String -> (String -> Tactic) -> Parser Tactic
tacticIdentArg s tac = do symbol s
                          x <- identifier
                          char '.'
                          return $ tac x                            

inferP :: Parser Tactic
inferP = do symbol "infer"
            l <- lambTerm
            char '.'
            return $ Infer l


--------------------------------------------------------------------------------------

getInfixParser :: String -> Parser Type -> Parser Type
getInfixParser s p =
  do u <- p
     (do symbol s
         t <- getInfixParser s p
         return $ RenameTy s [u, t]
      <|> return u)

getConstParser :: String -> Parser Type -> Parser Type
getConstParser s p =
  do symbol s
     return $ RenameTy s []
  <|> p

getUnaryPrefixParser :: String -> Parser Type -> Parser Type
getUnaryPrefixParser s p =
  do symbol s
     u <- unit5
     return $ RenameTy s [u]
  <|> p

getBinaryPrefixParser :: String -> Parser Type -> Parser Type
getBinaryPrefixParser s p =
  do symbol s
     u <- unit5
     u' <- unit5
     return $ RenameTy s [u, u']
  <|> p

basicInfixParser :: Parser Type
basicInfixParser = unit4

emptyParser :: Parser Type
emptyParser = empty
