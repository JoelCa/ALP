module Parser where

import Parsing
import Common

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
termTac = do symbol "assumption"
             char '.'
             return Assumption
          <|> do symbol "apply"
                 x <- identifier
                 char '.'
                 return $ Apply x
          <|> do symbol "elim"
                 x <- identifier
                 char '.'
                 return $ Elim x
          <|> do symbol "intro" --cambiar
                 char '.'
                 return Intro
          <|> do symbol "split"
                 char '.'
                 return Split
          <|> do symbol "left"
                 char '.'
                 return CLeft
          <|> do symbol "right"
                 char '.'
                 return CRight
          <|> do symbol "print"
                 x <- identifier
                 char '.'
                 return $ Print x