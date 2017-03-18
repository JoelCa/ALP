module Parser where

import Parsing
import Common
import Control.Applicative
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

type Parser a = ParserState FOperations a

reservedWords = ["Theorem", "Definition", "forall", "False"]
reservedSymbols = [':', '.', '\\', '[', ']']

-- Identificadores alfa-numéricos, exceptuando las palabras reservados.
validIdent1 :: Parser String
validIdent1 = vIdent1 reservedWords

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
-- Tampoco puede ser una palabra reservada.
validIdent2 :: Parser String
validIdent2 = vIdent2 reservedSymbols reservedWords

-- Cualquier cadena de simbolos sin espacios ni simbolos reservados.
validSymbol :: Parser String
validSymbol = vSymbol reservedSymbols

getCommand :: String -> FOperations -> ProofCommand
getCommand s op = case parse exprTy s op of
                    [(x,[],y)] -> return x
                    _ -> throw SyntaxE

exprTy :: Parser Command
exprTy = do symbol "Theorem"
            name <- validIdent1
            symbol ":"
            t <- exprTy'
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
exprTy' :: Parser Type
exprTy' = do t <- termTy
             (do symbol "->"
                 e <- exprTy'
                 return (Fun t e)
              <|> do s <- get
                     infixBinaryOp s t
              <|> return t)
          <|> do symbol "forall"
                 t <- validIdent1
                 symbol ","
                 e <- exprTy'
                 return (ForAll t e)

termTy :: Parser Type
termTy = do t <- termTy'
            (do symbol and_text
                t' <- termTy
                return $ RenameTy and_text [t, t']
             <|> do symbol or_text
                    t' <- termTy
                    return $ RenameTy or_text [t, t']
             <|> return t)
  
termTy' :: Parser Type
termTy' = do char '('
             e <- exprTy'
             char ')'
             return e
          <|> do char '~'
                 t <- termTy'
                 return $ RenameTy not_text [t]
          <|> do s <- get
                 prefixOps s  -- OJO! El nombre de la operación que se parsea puede ser
                              -- tomada como una proposición.
                              -- Por eso, lo ponemos antes del caso (B v)
          <|> do v <- validIdent1
                 return $ B v
          <|> do symbol "False"
                 return $ RenameTy bottom_text []

infixBinaryOp :: FOperations -> Type -> Parser Type
infixBinaryOp [] t = empty
infixBinaryOp ((s,_,Binary,True):xs) t =
  do symbol s
     t' <- termTy
     return $ RenameTy s [t, t']
  <|> infixBinaryOp xs t
infixBinaryOp ((_,_,_,False):xs) t =
  infixBinaryOp xs t

prefixOps :: FOperations -> Parser Type
prefixOps [] = empty
prefixOps ((s,_,Empty,False):xs) =
  do symbol s
     return $ RenameTy s []
  <|> prefixOps xs
prefixOps ((s,_,Unary,False):xs) =
  do symbol s
     t <- termTy
     return $ RenameTy s [t]
  <|> prefixOps xs
prefixOps ((s,_,Binary,False): xs) =
  do symbol s
     t <- termTy
     t' <- termTy
     return $ RenameTy s [t, t']
  <|> prefixOps xs
prefixOps ((_,_,Binary,True):xs) =
  prefixOps xs

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
               t <- exprTy'
               symbol "]"
               f <- unitTerm'
               return $ \a -> f $ BApp a t
            <|> return id

unitT :: Parser LamTerm
unitT = parens (applyT <|> abstraction)
        <|> do x <- validIdent1
               return $ LVar x

applyT :: Parser LamTerm
applyT = do x <- unitTerm
            y <- unitTerm
            f <- applyT'
            return $ f $ App x y

applyT' :: Parser (LamTerm -> LamTerm)
applyT' = do x <- unitTerm
             f <- applyT'
             return $ \a -> f $ App a x
          <|> return id

abstraction :: Parser LamTerm
abstraction = do char '\\'
                 v <- validIdent1
                 symbol ":"
                 t <- exprTy'
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
                         t <- exprTy'
                         symbol "."
                         return (op, ForAll a $ ForAll b t, Binary, False))
                      <|> do symbol ":="
                             t <- exprTy'
                             symbol "."
                             return (op, ForAll a t, Unary, False))
                  <|> do symbol ":="
                         t <- exprTy'
                         symbol "."
                         return (op, t, Empty, False))
               <|> do a <- validIdent1
                      op <- validSymbol
                      b <- validIdent1
                      symbol ":="
                      t <- exprTy'
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
            (do ty <- exprTy'
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
