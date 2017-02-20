module Parser where

import Parsing
import Common
import Control.Applicative

type ProofCommand = Either ProofExceptions Command

type Parser a = ParserState [(String, Bool)] a

lambda = [head "\\"]
reservedWords = ["forall", "exists"]
initState = [(and_op, True), (or_op, False)]

getCommand :: String -> ProofCommand
getCommand s = case parse exprTy s initState of
  [(x,[],s)] -> return x
  _ -> throw SyntaxE


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
         <|> do def <- typeDef
                return $ TypeDef def
         
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
          -- <|> do symbol "exists"
          --        t <- validIdent reservedWords
          --        symbol ","
          --        e <- exprTy'
          --        return (Exists t e)


termTy :: Parser Type
termTy = do t <- termTy'
            (do symbol and_op
                t' <- termTy
                return $ RenameTy and_op [t, t']
             <|> do symbol or_op
                    t' <- termTy
                    return $ RenameTy or_op [t, t']
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
expLam' = do v <- validIdent reservedWords
             return $ LVar v
          <|> do symbol lambda
                 v <- validIdent reservedWords
                 symbol ":"
                 t <- exprTy'
                 symbol "."
                 e <- expLam
                 return $ Abs v t e
          <|> do symbol lambda
                 v <- validIdent reservedWords
                 symbol "."
                 e <- expLam
                 return $ BAbs v e
          <|> do symbol "("
                 e <- expLam
                 symbol ")"
                 return e

-- Parser de definición de tipos.
typeDef :: Parser (String, Bool, Type)
typeDef = do symbol "Notation"
             op <- itemWithoutSpace
             a <- validIdent reservedWords
             b <- validIdent reservedWords
             symbol ":="
             t <- exprTy'
             (do symbol "("
                 symbol "infix"
                 symbol ")"
                 return (op, True, t)
              <|> return (op, False, t))


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

-- existsP :: Parser Tactic
-- existsP = undefined

-- cutP :: Parser Tactic
-- cutP = undefined

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
