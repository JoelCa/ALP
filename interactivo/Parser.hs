module Parser where

import Parsing
import Common

type Proof = Either ProofExceptions Command

reservedWords = ["forall", "exists","and","or"]

getCommand :: String -> Proof
getCommand s = case parse exprTy s of
  [(x,[])] -> return $ Ty x
  [(_,_)] -> Left SyntaxE
  [] -> case parse termTac s of
    [(x,[])] -> return $ Ta x
    _ -> Left SyntaxE


exprTy :: Parser Type
exprTy = do symbol "Theorem"
            t <- exprTy'
            symbol "." -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return t
             
exprTy' :: Parser Type
exprTy' = do t <- termTy
             (do symbol "->"
                 e <- exprTy'
                 return (Fun t e)
              <|> do symbol "and"
                     e <- exprTy'
                     return (And t e)
              <|> do symbol "or"
                     e <- exprTy'
                     return (Or t e)
              <|> return t)
          <|> do symbol "forall"
                 t <- validIdent reservedWords
                 symbol ","
                 e <- exprTy'
                 return (ForAll t e)
                           
termTy :: Parser Type
termTy = do char '('
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
                 x <- validIdent reservedWords
                 char '.'
                 return (Apply x)
          <|> do symbol "intro" --cambiar
                 char '.'
                 return Intro
          <|> do symbol "split"
                 char '.'
                 return Split