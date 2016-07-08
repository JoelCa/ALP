module PrettyPrinter where

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
fv (t :!: _)         = fv t
fv (BLam _ u)        = fv u


fvType :: TType -> [String]
fvType (TBound  _) = []
fvType (TFree n) = [n]
fvType (TFun t u) = fvType t ++ fvType u
fvType (TForAll t) = fvType t


-- pretty-printer de términos
printTerm :: Term -> Doc 
printTerm t = printTerm' 1 [] (vars \\ fv t) t

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = PP.parens d

printTerm' :: Int -> [String] -> [String] -> Term -> Doc
printTerm' _ bs _  (Bound j)         = text $ bs !! j
printTerm' _ _  _  (Free (Global n)) = text n
printTerm' _ _  _  (Free (Quote n))  = text "quoted"<>text (show n)
printTerm' i bs fs (t :@: u)         = parenIf (i < 1) $ 
                                       printTerm' 2 bs fs t <+> 
                                       printTerm' 0 bs fs u
printTerm' i bs (f:fs) (Lam t u)     = parenIf (i > 1) $ 
                                       text "\\" <> 
                                       text f <> 
                                       text ":" <> 
                                       printType t <> 
                                       text "." <> 
                                       printTerm' 1 (f:bs) fs u
printTerm' i bs fs (BLam t u)        = parenIf (i > 1) $  -- Chequear "parenIf"
                                       text "\\" <> 
                                       text t <> 
                                       text "." <> 
                                       printTerm' 1 bs fs u
printTerm' i bs fs (t :!: ty)        = printTerm' 2 bs fs t <+> -- Chequear valores de "i"
                                       printTType ty
printTerm' _ _  [] (Lam _ _)         = error "prinTerm': no hay nombres para elegir"


-- pretty-printer de tipos
printTType :: TType -> Doc
printTType t = printTType' 1 [] (vars \\ fvType t) t

-- Chequear si es necesario usar parenIf
printTType' :: Int -> [String] -> [String] -> TType -> Doc
printTType' _ bs _ (TBound n) = text $ bs !! n
printTType' _ bs _ (TFree n) = text n
printTType' i bs fs (TFun t u) = parenIf (i < 1) $ 
                                 printTType' 2 bs fs t <+>
                                 text "->" <+>
                                 printTType' 0 bs fs u
printTType' i bs (f:fs) (TForAll t) =  parenIf (i > 1) $ 
                                       text "\\" <> 
                                       text f <> 
                                       text "." <> 
                                       printTType' 1 (f:bs) fs t

printType :: Type -> Doc
printType = printType' False

printType' :: Bool -> Type -> Doc
printType' _ (B v)           = text v
printType' False (Fun t1 t2) = printType' True t1 <+> 
                               text "->"          <+> 
                               printType' False t2
printType' False (ForAll v t) = text "forall" <+>
                                text v <>
                                text "," <+>
                                printType' False t
printType' True t            = PP.parens $ printType' False t

printProof :: Int -> Context -> Type -> Doc
printProof n c ty = printHypothesis n c $$
                    text "-----------------" $$
                    printType ty

printHypothesis :: Int -> Context -> Doc
printHypothesis 0 [] = empty
printHypothesis 1 [x] = text "H0: " <>
                        printType x
printHypothesis n (x:xs) 
  | n > 0 = printHypothesis (n-1) xs $$
            text "H" <> text (show (n-1)) <>  text ": " <> printType x
  | otherwise = error "error: printHypothesis, no debería pasar"
printHypothesis _ _ = error "error: printHypothesis, no debería pasar"
