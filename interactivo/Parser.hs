module Parser where

import Parsing
import Common

type Proof = Either ProofExceptions Command

reservedWords = ["forall", "exists"]

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
              <|> return t)
          <|> do symbol "forall"
                 t <- validIdentifier reservedWords --Algo está mal con la E de exists
                 symbol ","
                 e <- exprTy'
                 return (ForAll t e)
                           
termTy :: Parser Type
termTy = do char '('
            e <- exprTy'
            char ')'
            return e
         <|> do v <- validIdentifier reservedWords
                return (B v)
              
-- exprTac :: Parser [Tactics]
-- exprTac = do x <- termTac
--              xs <- many termTac
--              return (x:xs)
              
termTac :: Parser Tactic
termTac = do symbol "assumption"
             char '.'
             return Assumption
          <|> do symbol "apply"
                 x <- validIdentifier reservedWords
                 char '.'
                 return (Apply x)
          <|> do symbol "intro" --cambiar
                 char '.'
                 return Intro