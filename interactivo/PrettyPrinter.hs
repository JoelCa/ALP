module PrettyPrinter where

import Common
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Data.List
import qualified Data.Sequence as S

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
fType (RenameTTy _ ts) = foldr (\x r -> fType x ++ r) [] ts
-- fType (TExists t) = fType t

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = PP.parens d


-- pretty-printer de términos, con tipos sin nombres.
printTermTType :: [String] -> Term -> Doc 
printTermTType op t = printTermTType' op 1 [] [] (vars \\ fv t) (typeVars \\ ftv t) t

printTermTType' :: [String] -> Int -> [String] -> [String] -> [String] -> [String] -> Term -> Doc
printTermTType' _ _ bs _  _ _ (Bound j)             = text $ bs !! j
printTermTType' _ _ _  _  _ _ (Free (Global n))     = text n
printTermTType' _ _ _  _  _ _ (Free (Quote n))      = text "quoted" <> text (show n)
printTermTType' op i bs bts fs fts (t :@: u)         = parenIf (i < 1) $ 
                                                       printTermTType' op 2 bs bts fs fts t <+> 
                                                       printTermTType' op 0 bs bts fs fts u
printTermTType' op i bs bts (f:fs) fts (Lam (_,t) u) = parenIf (i > 1) $ 
                                                       text "\\" <> 
                                                       text f <> 
                                                       text ":" <> 
                                                       printTypeTermTType op bts t <>
                                                       text "." <> 
                                                       printTermTType' op 1 (f:bs) bts fs fts u
printTermTType' op i bs bts fs (f':fts) (BLam _ u)   = parenIf (i > 1) $  -- Chequear "parenIf"
                                                       text "\\" <> 
                                                       text f' <> 
                                                       text "." <> 
                                                       printTermTType' op 1 bs (f':bts) fs fts u
printTermTType' op i bs bts fs fts (u :!: (_,t))     = printTermTType' op 2 bs bts fs fts u <+> -- Chequear valores de "i"
                                                       text "[" <>
                                                       printTypeTermTType op bts t <>
                                                       text "]"
printTermTType' _ _ _ _ [] _ (Lam _ _)              = error "prinTerm': no hay nombres para elegir"
printTermTType' _ _ _ _ _ [] (BLam _ _)             = error "prinTerm': no hay nombres para elegir"


printTypeTermTType :: [String] -> [String] -> TType -> Doc
printTypeTermTType op bs t = printTType' op 2 bs ((typeVars \\ fType t) \\ bs) t


-- pretty-printer de términos, con los tipos dados por el usuario.
printTerm :: Term -> Doc 
printTerm t = printTerm' 1 [] (vars \\ fv t)  t


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
                                       text "[" <>
                                       printType ty <>  -- Arreglar
                                       text "]"
printTerm' _ _ [] (Lam _ _)          = error "prinTerm': no hay nombres para elegir"



-- pretty-printer de tipos sin nombres
printTType :: [String] -> TType -> Doc
printTType op t = printTType' op 1 [] (typeVars \\ fType t) t

-- Chequear si es necesario usar parenIf
printTType' :: [String] -> Int -> [String] -> [String] -> TType -> Doc
printTType' op _ bs _ (TBound n) = text $ bs !! n
printTType' op _ bs _ (TFree n) = text n
printTType' op i bs fs (TFun t u) = parenIf (i > 1) $ 
                                    printTType' op 2 bs fs t <+>
                                    text "->" <+>
                                    printTType' op 0 bs fs u
printTType' op i bs (f:fs) (TForAll t) =  parenIf (i > 1) $ 
                                          text "forall" <+> 
                                          text f <> 
                                          text "," <+> 
                                          printTType' op 1 (f:bs) fs t
printTType' op i bs fs (RenameTTy n ts) = parenIf (i > 1) $ 
                                          text (op !! n) <+>
                                          foldl (\r x -> r <+> printTType' op 1 bs fs x) empty ts
-- printTType' i bs (f:fs) (TExists t) =  parenIf (i > 1) $
--                                        text "exists" <+>
--                                        text f <>
--                                        text "," <+>
--                                        printTType' 1 (f:bs) fs t

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
printType' False (RenameTy s ts) = text s <+>
                                   foldl (\r x -> r <+> printType' False x) empty ts
printType' True t             = PP.parens $ printType' False t
-- printType' False (Exists v t) = text "exists" <+>
--                                 text v <>
--                                 text "," <+>
--                                 printType' False t
                                    
printProof :: Int -> FTypeContext -> BTypeContext -> TermContext -> [Maybe (Type, TType)] -> Doc
printProof tp ftc btc c tys =
  (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
  printContext ftc btc c $$
  printGoals tp tys


printGoals :: Int -> [Maybe (Type, TType)] -> Doc
printGoals = printGoals' 1

printGoals' :: Int -> Int -> [Maybe (Type, TType)] -> Doc
printGoals' _ _ [] = empty
printGoals' i tp (ty:tys)
  | i <= tp = (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
              printGoal ty $$
              printGoals' (i+1) tp tys
  | otherwise = empty

printGoal :: Maybe (Type, TType) -> Doc
printGoal (Just (ty,_)) = printType' False ty
printGoal Nothing = text "Prop"


printContext :: FTypeContext -> BTypeContext -> TermContext -> Doc
printContext ftc btc c = printFTypeContext ftc $$
                         printRestContext btc c


printFTypeContext :: FTypeContext -> Doc
printFTypeContext [] = empty
printFTypeContext (x:ftc) = printFTypeVar x $$
                            printFTypeContext ftc

printFTypeVar :: FTypeVar -> Doc
printFTypeVar x = text x <+>
                  text ":" <+>
                  text "Prop"

printRestContext :: BTypeContext -> TermContext -> Doc
printRestContext btc c
  | S.null btc = printRestTermC c
  | S.null c = printRestBTypeC btc
  | otherwise = let x = S.index btc 0
                    y = S.index c 0
                in if fst x > fst4 y
                   then printRestContext (S.drop 1 btc) c $$
                        printBTypeVar x
                   else printRestContext btc (S.drop 1 c) $$
                        printTermVar (S.length c) y

printRestTermC :: TermContext -> Doc
printRestTermC c
  | S.null c = empty
  | otherwise = printRestTermC (S.drop 1 c) $$
                printTermVar (S.length c) (S.index c 0)

printRestBTypeC :: BTypeContext -> Doc
printRestBTypeC btc
  | S.null btc = empty
  | otherwise = printRestBTypeC (S.drop 1 btc) $$
                printBTypeVar (S.index btc 0)

printTermVar :: Int -> TermVar -> Doc
printTermVar n (_,_,t,_) = text "H" <>
                           text (show (n-1)) <+> 
                           text ":" <+>
                           printType t

printBTypeVar :: BTypeVar -> Doc
printBTypeVar (_,x) = text x <+>
                      text ":" <+>
                      text "Prop"

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

-- printQuantifiers :: TypeContext -> Doc
-- printQuantifiers [] = empty
-- printQuantifiers (q:tc) = text q <+>
--                           text ":" <+>
--                           text "Prop" $$
--                           printQuantifiers tc

-- printHypothesis :: Int -> TermContext -> Doc
-- printHypothesis 0 [] = empty
-- printHypothesis 1 [(_,x,_)] = text "H0" <+>
--                             text ":" <+>
--                             printType x
-- printHypothesis n ((_,x,_):xs) 
--   | n > 0 = printHypothesis (n-1) xs $$
--             text "H" <>
--             text (show (n-1)) <+> 
--             text ":" <+>
--             printType x
--   | otherwise = error "error: printHypothesis, no debería pasar"
-- printHypothesis _ _ = error "error: printHypothesis, no debería pasar"
