module Parser_archivo where

import Parsing
import Common

type Proof = (Type, [Tactics])

getCommand :: String -> Maybe Proof
getCommand s =  do (ty,r) <- getType s
                   ts <- getTactics r
                   return (ty,ts)


getType :: String -> Maybe (Type,String)
getType s = case parse exprTy s of
  [x] -> return x
  [] -> Nothing

             
getTactics :: String -> Maybe [Tactics]
getTactics s = case parse exprTac s of
  [(x,r)] -> case parse space r of -- quito los espacios
                  [(_,[])] -> return x
                  [] -> return x
                  _ -> fail s
  _ -> fail s



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
              
exprTac :: Parser [Tactics]
exprTac = do x <- termTac
             xs <- many termTac
             return (x:xs)
              
termTac :: Parser Tactics
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