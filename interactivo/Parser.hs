module Parser where

import Parsing
import Common
import Control.Applicative

type Proof = Either ProofExceptions Command

reservedWords = ["forall", "exists"]

getCommand :: String -> Proof
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
