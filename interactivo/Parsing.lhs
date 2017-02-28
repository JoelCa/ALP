Basado en:
Functional parsing library from chapter 8 of Programming in Haskell,
Graham Hutton, Cambridge University Press, 2007.

Modificado por Mauro Jaskelioff

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}

> module Parsing where
>
> import Data.Char
> import Control.Monad
> import Control.Applicative hiding (many)
> import Control.Monad.State.Lazy

The monad of parsers
--------------------

> newtype ParserState s a       =  P ((String, s) -> [(a,String,s)])
>
> instance Monad (ParserState s) where
>    return v                   =  P (\(x,st) -> [(v,x,st)])
>    p >>= f                    =  P (\(x,st) -> [ w | (v,out,st') <- parse p x st, w <- parse (f v) out st'])
> 
> instance MonadPlus (ParserState s) where
>    mzero                      =  P (\_	 -> [])
>    p `mplus` q                =  P (\(x,st) -> case parse p x st of
>                                                  []        -> parse q x st
>                                                  x         -> x)
> 
> instance Functor (ParserState s) where
>   fmap = liftM
>   
> instance Applicative (ParserState s) where
>   pure                        = return
>   (<*>)                       = ap

> instance MonadState s (ParserState s) where
>   get = P (\(x,st) -> [(st,x,st)])
>   put s = P (\(x,st) -> [((),x,s)])
>   state f = P (\(x,st) -> let (y,st') = f st in [(y,x,st')])


Choice
------

> instance Alternative (ParserState s) where
>   empty                       = mzero
>   (<|>)                       = mplus


Basic parsers
-------------

> failure                       :: ParserState s a
> failure                       =  mzero
>
> item                          :: ParserState s Char
> item                          =  P (\(x,st) -> case x of
>                                                  []     -> []
>                                                  (y:ys) -> [(y,ys,st)])
> 
> parse                         :: ParserState s a -> String -> s -> [(a,String,s)]
> parse (P p) x st               =  p (x,st)
                                   

Derived primitives
------------------

> sat                           :: (Char -> Bool) -> ParserState s Char
> sat p                         =  do x <- item
>                                     if p x then return x else failure
> 
> digit                         :: ParserState s Char
> digit                         =  sat isDigit
> 
> lower                         :: ParserState s Char
> lower                         =  sat isLower
> 
> upper                         :: ParserState s Char
> upper                         =  sat isUpper
> 
> letter                        :: ParserState s Char
> letter                        =  sat isAlpha
> 
> alphanum                      :: ParserState s Char
> alphanum                      =  sat (\x-> isAlphaNum x || (x == '_')) -- Modifiqué esta parte
> 
> char                          :: Char -> ParserState s Char
> char x                        =  sat (== x)
> 
> string                        :: String -> ParserState s String
> string []                     =  return []
> string (x:xs)                 =  do char x
>                                     string xs
>                                     return (x:xs)
> 
> many                          :: ParserState s a -> ParserState s [a]
> many p                        =  many1 p <|> return []
> 
> many1                         :: ParserState s a -> ParserState s [a]
> many1 p                       =  do v  <- p
>                                     vs <- many p
>                                     return (v:vs)
> 
> ident                         :: ParserState s String
> ident                         =  do x  <- alphanum        -- Modifiqué esta parte
>                                     xs <- many alphanum
>                                     return (x:xs)
> 
> nat                           :: ParserState s Int
> nat                           =  do xs <- many1 digit
>                                     return (read xs)
>
> int                           :: ParserState s Int
> int                           =  do char '-'
>                                     n <- nat
>                                     return (-n)
>                                  <|> nat
> 
> space                         :: ParserState s ()
> space                         =  do many (sat isSpace)
>                                     return ()
>	
> sepBy                         :: ParserState s a -> ParserState s sep -> ParserState s [a]
> sepBy p sep                   =  sepBy1 p sep <|> return []
>
> sepBy1                        :: ParserState s a -> ParserState s sep -> ParserState s [a]
> sepBy1 p sep        		= do{ x <- p
>                         	    ; xs <- many (sep >> p)
>                         	    ; return (x:xs) }	
>
> endBy1                        :: ParserState s a -> ParserState s sep -> ParserState s [a]
> endBy1 p sep                  = many1 (do { x <- p; sep; return x })
>
> endBy                         :: ParserState s a -> ParserState s sep -> ParserState s [a]
> endBy p sep                   	= many (do{ x <- p; sep; return x })
>

Ignoring spacing
----------------

> token                         :: ParserState s a -> ParserState s a
> token p                       =  do space
>                                     v <- p
>                                     space
>                                     return v
> 
> identifier                    :: ParserState s String
> identifier                    =  token ident
> 
> natural                       :: ParserState s Int
> natural                       =  token nat
> 
> integer                       :: ParserState s Int
> integer                       =  token int
>
> symbol                        :: String -> ParserState s String
> symbol xs                     =  token (string xs)

> validSToken :: ParserState s String -> [String] -> ParserState s String
> validSToken p xs = do y <- p
>                       when (foldl (\w x ->  (y == x) || w) False xs) failure    
>                       return y
>
> vIdent1 :: [String] -> ParserState s String
> vIdent1 = validSToken identifier
>
> vIdent2 :: [String] -> ParserState s String
> vIdent2 = validSToken $ token $ many $ sat (\c -> (c /= ' ') && (c /= '.')) -- Al punto lo tomamos como fin de comando.
>                                                                             -- Por ello, ningún identificador puede contenerlo.



-- usar: string-insert-rectangle, para insertar ">"
