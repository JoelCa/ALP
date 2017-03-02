module Parser where

import Parsing
import Common
import Control.Applicative
import Control.Monad.State.Lazy (get)

type ProofCommand = Either ProofExceptions Command

type Parser a = ParserState FOperations a

lambda = [head "\\"]
reservedSymbols = ["Theorem","Definition","forall", "False",":",".",":="]

-- Identificadores alfa-numéricos, exceptuando las simbolos reservados.
validIdent1 :: Parser String
validIdent1 = vIdent1 reservedSymbols

-- Cualquier cadena de simbolos sin espacios, exceptuando las simbolos reservados.
validIdent2 :: Parser String
validIdent2 = vIdent2 reservedSymbols

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
expLam :: Parser LamTerm
expLam = do e <- expLam'
            f <- emptyLam
            return $ f e

emptyLam :: Parser (LamTerm -> LamTerm)
emptyLam = do symbol "["
              t <- exprTy'
              symbol "]"
              f <- emptyLam
              return $ \x -> f $ BApp x t
           <|> do e <- expLam
                  return $ \x -> App x e
           <|> return id

expLam' :: Parser LamTerm
expLam' = do v <- validIdent1
             return $ LVar v
          <|> do symbol lambda
                 v <- validIdent1
                 symbol ":"
                 t <- exprTy'
                 symbol "."
                 e <- expLam
                 return $ Abs v t e
          <|> do symbol lambda
                 v <- validIdent1
                 symbol "."
                 e <- expLam
                 return $ BAbs v e
          <|> do symbol "("
                 e <- expLam
                 symbol ")"
                 return e

-- Parser de definición de tipos.
typeDef :: Parser (String, Type, Operands, Bool)
typeDef = do symbol "Definition"
             op <- validIdent2
             (do a <- validIdent1
                 (do b <- validIdent1
                     symbol ":="
                     t <- exprTy'
                     inf <- isInfix
                     symbol "."
                     return (op, ForAll a $ ForAll b t, Binary, inf))
                  <|> do symbol ":="
                         t <- exprTy'
                         inf <- isInfix
                         symbol "."
                         return (op, ForAll a t, Unary, False))
              <|> do symbol ":="
                     t <- exprTy'
                     inf <- isInfix                     
                     symbol "."
                     return (op, t, Empty, False)


isInfix :: Parser Bool
isInfix = do symbol "("
             symbol "infix"
             symbol ")"
             return True
          <|> return False


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
             <|> do te <- expLam
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
            l <- expLam
            char '.'
            return $ Infer l
