module Asistente_PP where

import Common
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Data.List


-----------------------
--- pretty printer
-----------------------

-- lista de posibles nombres para variables
vars :: [String]
vars = [ c : n | n <- "" : map show nats, c <- ['x','y','z'] ++ ['a'..'w'] ]
        where nats :: [Integer]
              nats = [1..]

fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (Global n)) = [n]
fv (Free (Quote _))  = []
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u

-- pretty-printer de términos
printTerm :: Term -> Doc 
printTerm t = printTerm' 1 [] (vars \\ fv t) t

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = PP.parens d

printTerm' :: Int -> [String] -> [String] -> Term -> Doc
printTerm' _ bs _  (Bound j)             = text $ bs !! j
printTerm' _ _  _  (Free (Global n))     = text n
printTerm' _ _  _  (Free (Quote n))      = text "quoted"<>text (show n)
printTerm' i bs fs (t :@: u)             = parenIf (i < 1) $ 
                                            printTerm' 2 bs fs t <+> 
                                            printTerm' 0 bs fs u
printTerm' i bs (f:fs) (Lam t u)         = parenIf (i > 1) $ 
                                            text "\\" <> 
                                            text f <> 
                                            text ":" <> 
                                            printType t <> 
                                            text "." <> 
                                            printTerm' 1 (f:bs) fs u
printTerm' _ _  [] (Lam _ _)         = error "prinTerm': no hay nombres para elegir"

-- pretty-printer de tipos
printType :: Type -> Doc
printType = printType' False

printType' :: Bool -> Type -> Doc
printType' _ (B v)           = text v
printType' False (Fun t1 t2) = printType' True t1 <+> 
                               text "->"          <+> 
                               printType' False t2
printType' True t            = PP.parens $ printType' False t
