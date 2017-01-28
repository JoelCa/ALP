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
vars = [ c : n | n <- "" : map show nats, c <- ['x','y','z'] ++ ['p'..'w'] ]
  where nats :: [Integer]
        nats = [1..]

--NO se usa
typeVars :: [String]
typeVars = [ c : n | n <- "" : map show nats, c <- ['a' .. 'o']]
  where nats :: [Integer]
        nats = [1..]


fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (Global n)) = [n]
fv (Free (Quote _))  = []
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u
fv (t :!: _)         = fv t
fv (BLam _ t)        = fv t

-- variables de tipo libre
ftv :: Term -> [String]
ftv (Bound _) = []
ftv (Free _)  = []
ftv (x :@: y) = ftv x ++ ftv y
ftv (Lam (_,t) x) = fType t ++ fv x
ftv (x :!: (_,t)) = ftv x ++ fType t
ftv (BLam b x)  = ftv x \\ [b]


fType :: TType -> [String]
fType (TBound  _) = []
fType (TFree n) = [n]
fType (TFun t u) = fType t ++ fType u
fType (TForAll t) = fType t
fType (TExists t) = fType t
fType (TAnd t u) = fType t ++ fType u
fType (TOr t u) = fType t ++ fType u

-- pretty-printer de términos
printTerm :: Term -> Doc 
printTerm t = printTerm' 1 [] (vars \\ fv t)  t

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = PP.parens d


--Arreglar paréntesis de :@:
printTerm' :: Int -> [String] -> [String] -> Term -> Doc
printTerm' _ bs _  (Bound j)         = text $ bs !! j
printTerm' _ _  _  (Free (Global n)) = text n
printTerm' _ _  _  (Free (Quote n))  = text "quoted" <> text (show n)
printTerm' i bs fs (t :@: u)         = parenIf (i < 1) $ 
                                       printTerm' 2 bs fs t <+> 
                                       printTerm' 0 bs fs u
printTerm' i bs (f:fs) (Lam (t,_) u) = parenIf (i > 1) $ 
                                       text "\\" <> 
                                       text f <> 
                                       text ":" <> 
                                       parenIf True (printType t) <>
                                       text "." <>
                                       printTerm' 1 (f:bs) fs u
printTerm' i bs fs (BLam x u)        = parenIf (i > 1) $  -- Chequear "parenIf"
                                       text "\\" <> 
                                       text x <> 
                                       text "." <> 
                                       printTerm' 1 bs fs u
printTerm' i bs fs (t :!: (ty,_))    = parenIf (i < 1) $
                                       printTerm' 2 bs fs t <+> -- Chequear valores de "i"
                                       (parenIf True $ printType ty)  -- Arreglar
printTerm' _ _ [] (Lam _ _)          = error "prinTerm': no hay nombres para elegir"



-- pretty-printer de tipos
printTypeTerm :: [String] -> TType -> Doc
printTypeTerm bs t = printTType' 2 bs (typeVars \\ fType t) t

printTType :: TType -> Doc
printTType t = printTType' 1 [] (typeVars \\ fType t) t

-- Chequear si es necesario usar parenIf
printTType' :: Int -> [String] -> [String] -> TType -> Doc
printTType' _ bs _ (TBound n) = text $ bs !! n
printTType' _ bs _ (TFree n) = text n
printTType' i bs fs (TFun t u) = parenIf (i < 1) $ 
                                 printTType' 2 bs fs t <+>
                                 text "->" <+>
                                 printTType' 0 bs fs u
printTType' i bs (f:fs) (TForAll t) =  parenIf (i > 1) $ 
                                       text "forall" <+> 
                                       text f <> 
                                       text "." <> 
                                       printTType' 1 (f:bs) fs t
printTType' i bs (f:fs) (TExists t) =  parenIf (i > 1) $
                                       text "exists" <+>
                                       text f <>
                                       text "." <>
                                       printTType' 1 (f:bs) fs t
printTType' i bs fs (TAnd t u) = parenIf (i < 1) $ 
                                 printTType' 2 bs fs t <+>
                                 text "/\\" <+>
                                 printTType' 0 bs fs u
printTType' i bs fs (TOr t u) = parenIf (i < 1) $ 
                                 printTType' 2 bs fs t <+>
                                 text "\\/" <+>
                                 printTType' 0 bs fs u


printTypeFromMaybe :: Maybe Type -> Doc
printTypeFromMaybe (Just ty) = printType' False ty
printTypeFromMaybe Nothing = text "Prop"

printType :: Type -> Doc
printType = printType' False

printType' :: Bool -> Type -> Doc
printType' _ (B v)            = text v
printType' False (Fun t1 t2)  = printType' True t1 <+> 
                                text "->"          <+> 
                                printType' False t2
printType' False (ForAll v t) = text "forall" <+>
                                text v <>
                                text "," <+>
                                printType' False t
printType' False (Exists v t) = text "exists" <+>
                                text v <>
                                text "," <+>
                                printType' False t
printType' True t             = PP.parens $ printType' False t
printType' False (And t1 t2)  = printType' True t1 <+> 
                                text "/\\"         <+> 
                                printType' False t2
printType' False (Or t1 t2)   = printType' True t1 <+> 
                                text "\\/"         <+> 
                                printType' False t2


printProof :: Int -> [Int] -> [TypeContext] -> [Context] -> [Maybe Type] -> Doc
printProof = printSubProofs 1

printSubProofs :: Int -> Int -> [Int] ->  [TypeContext] -> [Context] -> [Maybe Type] -> Doc
printSubProofs _ _ [] [] [] [] =  empty
printSubProofs i tp (n:ns) (tc:tcs) (c:cs) (ty:tys) = printSubProofs' i tp n tc c ty $$
                                                      printSubProofs (i+1) tp ns tcs cs tys
                                    
printSubProofs' :: Int -> Int -> Int -> TypeContext -> Context -> Maybe Type -> Doc
printSubProofs' 1 tp n tc c ty = (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
                                 printContext n tc c $$
                                 (text $ "___________________[1/"++ show tp ++"]") $$
                                 printTypeFromMaybe ty
printSubProofs' i tp n _ _ ty = (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
                                printTypeFromMaybe ty


printContext :: Int -> TypeContext -> Context -> Doc
printContext n tc c = printQuantifiers tc $$
                      printHypothesis n c

printQuantifiers :: TypeContext -> Doc
printQuantifiers [] = empty
printQuantifiers (q:tc) = text q <+>
                          text ":" <+>
                          text "Prop" $$
                          printQuantifiers tc

printHypothesis :: Int -> Context -> Doc
printHypothesis 0 [] = empty
printHypothesis 1 [(x,y)] = text "H0" <+>
                            text ":" <+>
                            printType x
printHypothesis n ((x,y):xs) 
  | n > 0 = printHypothesis (n-1) xs $$
            text "H" <>
            text (show (n-1)) <+> 
            text ":" <+>
            printType x
  | otherwise = error "error: printHypothesis, no debería pasar"
printHypothesis _ _ = error "error: printHypothesis, no debería pasar"
