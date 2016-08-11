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
                 t <- validIdent reservedWords
                 symbol ","
                 e <- exprTy'
                 return (ForAll t e)

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