module Parser where

import Parsing
import Common

type Proof = Either String Command

getCommand :: String -> Proof
getCommand s = case parse exprTy s of
  [(x,[])] -> return $ Ty x
  [(_,_)] -> fail "error sintaxis"
  [] -> case parse termTac s of
    [(x,[])] -> return $ Ta x
    _ -> fail "error sintaxis"


exprTy :: Parser Type
exprTy = do symbol "Theorem"
            t <- exprTy'
            char '.' -- NO puedo usar '\n' como fin del comando, por que symbol lo come
            return t
             
exprTy' :: Parser Type
exprTy' = do t <- termTy
             (do symbol "->"
                 e <- exprTy'
                 return (Fun t e)
              <|> return t)

termTy :: Parser Type
termTy = do char '('
            e <- exprTy'
            char ')'
            return e
         <|> do v <- identifier
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
                 x <- natural --cambiar
                 char '.'
                 return (Apply x)
          <|> do symbol "intro" --cambiar
                 char '.'
                 return Intro