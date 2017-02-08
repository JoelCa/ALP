module Parser where

import Parsing
import Common
import Control.Applicative

type ProofCommand = Either ProofExceptions Command

reservedWords = ["forall", "exists"]

getCommand :: String -> ProofCommand
getCommand s = case parse exprTy s of
  [(x,[])] -> return x
  _ -> Left SyntaxE


exprTy :: Parser Command
exprTy = do symbol "Theorem"
            name <- validIdent reservedWords
            symbol ":"
            t <- exprTy'
            symbol "." -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return $ Ty name t
         <|> do symbol "Props"
                ps <- sepBy (validIdent reservedWords) space
                char '.'
                return $ Props ps
         <|> do tac <- termTac
                return $ Ta tac
         
-- Parser de los tipos (o fórmulas lógicas).
exprTy' :: Parser Type
exprTy' = do t <- termTy
             (do symbol "->"
                 e <- exprTy'
                 return (Fun t e)              
              <|> return t)
          <|> do symbol "forall"
                 t <- validIdent reservedWords
                 symbol ","
                 e <- exprTy'
                 return (ForAll t e)
          <|> do symbol "exists"
                 t <- validIdent reservedWords
                 symbol ","
                 e <- exprTy'
                 return (Exists t e)


termTy :: Parser Type
termTy = do t <- termTy'
            (do symbol $ "/" ++ [head "\\"]
                t' <- termTy
                return (And t t')
             <|> do symbol $ [head "\\"] ++ "/"
                    t' <- termTy
                    return (Or t t')
             <|> return t)
            
termTy' :: Parser Type
termTy' = do char '('
             e <- exprTy'
             char ')'
             return e
          <|> do v <- validIdent reservedWords
                 return (B v)

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
expLam' = do symbol [head "\\"]
             v <- validIdent reservedWords
             symbol ":"
             t <- exprTy'
             symbol "."
             e <- expLam
             return $ Abs v t e
          <|> do symbol [head "\\"]
                 v <- validIdent reservedWords
                 symbol "."
                 e <- expLam
                 return $ BAbs v e
          <|> do v <- validIdent reservedWords
                 return $ LVar v
          <|> do symbol "("
                 e <- expLam
                 symbol ")"
                 return e

-- Parser de las tácticas.
termTac :: Parser Tactic
termTac = assumptionParser
          <|> applyParser
          <|> elimParser
          <|> introParser
          <|> introsParser
          <|> splitParser
          <|> leftParser
          <|> rightParser
          <|> existsParser
          <|> printParser
          <|> cutParser
          <|> exactParser
          <|> inferParser


assumptionParser :: Parser Tactic
assumptionParser = tacticZeroArg "assumption" Assumption

introParser :: Parser Tactic
introParser = tacticZeroArg "intro" Intro

introsParser :: Parser Tactic
introsParser = tacticZeroArg "intros" Intros

splitParser :: Parser Tactic
splitParser = tacticZeroArg "split" Split

leftParser :: Parser Tactic
leftParser = tacticZeroArg "left" CLeft

rightParser :: Parser Tactic
rightParser = tacticZeroArg "right" CRight

applyParser :: Parser Tactic
applyParser = tacticIdentArg "apply" Apply

elimParser :: Parser Tactic
elimParser = tacticIdentArg "elim" Elim

printParser :: Parser Tactic
printParser = tacticIdentArg "print" Print

existsParser :: Parser Tactic
existsParser = tacticTypeArg "exists" CExists

cutParser :: Parser Tactic
cutParser = tacticTypeArg "cut" Cut

exactParser :: Parser Tactic
exactParser = tacticTypeArg "exact" Exact


tacticZeroArg :: String -> Tactic -> Parser Tactic
tacticZeroArg s tac = do symbol s
                         char '.'
                         return tac

tacticIdentArg :: String -> (String -> Tactic) -> Parser Tactic
tacticIdentArg s tac = do symbol s
                          x <- identifier
                          char '.'
                          return $ tac x
          
tacticTypeArg :: String -> (Type -> Tactic) -> Parser Tactic
tacticTypeArg s tac = do symbol s
                         t <- exprTy'
                         char '.'
                         return $ tac t          

inferParser :: Parser Tactic
inferParser = do symbol "infer"
                 l <- expLam
                 char '.'
                 return $ Infer l
