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


-- Pretty-printer de términos, con tipos sin nombres.
printTermTType :: [UserOperation] -> Term -> Doc 
printTermTType op t = printTermTType' op 1 [] [] (vars \\ fv t) (typeVars \\ ftv t) t

printTermTType' :: [UserOperation] -> Int -> [String] -> [String] -> [String] -> [String] -> Term -> Doc
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


printTypeTermTType :: [UserOperation] -> [String] -> TType -> Doc
printTypeTermTType op bs t = printTType' op 2 bs ((typeVars \\ fType t) \\ bs) t


-- Pretty-printer de términos, con tipos con nombres.
printTerm :: [UserOperation] -> Term -> Doc 
printTerm op t = printTerm' op 1 [] (vars \\ fv t)  t


--Arreglar paréntesis de :@:
printTerm' :: [UserOperation] -> Int -> [String] -> [String] -> Term -> Doc
printTerm' _ _ bs _  (Bound j)         = text $ bs !! j
printTerm' _ _ _  _  (Free (Global n)) = text n
printTerm' _ _ _  _  (Free (Quote n))  = text "quoted" <> text (show n)
printTerm' op i bs fs (t :@: u)         = parenIf (i < 1) $ 
                                          printTerm' op 2 bs fs t <+> 
                                          printTerm' op 0 bs fs u
printTerm' op i bs (f:fs) (Lam (t,_) u) = parenIf (i > 1) $ 
                                          text "\\" <> 
                                          text f <> 
                                          text ":" <> 
                                          parenIf True (printType op t) <>
                                          text "." <>
                                          printTerm' op 1 (f:bs) fs u
printTerm' op i bs fs (BLam x u)        = parenIf (i > 1) $  -- Chequear "parenIf"
                                          text "\\" <> 
                                          text x <> 
                                          text "." <> 
                                          printTerm' op 1 bs fs u
printTerm' op i bs fs (t :!: (ty,_))    = parenIf (i < 1) $
                                          printTerm' op 2 bs fs t <+> -- Chequear valores de "i"
                                          text "[" <>
                                          printType op ty <>  -- Arreglar
                                          text "]"
printTerm' _ _ _ [] (Lam _ _)           = error "prinTerm': no hay nombres para elegir"



-- Pretty-printer de tipos sin nombres.
printTType :: [UserOperation] -> TType -> Doc
printTType op t = printTType' op 1 [] (typeVars \\ fType t) t

-- Chequear si es necesario usar parenIf
printTType' :: [UserOperation] -> Int -> [String] -> [String] -> TType -> Doc
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
printTType' op i bs fs (RenameTTy n [t1,t2])
  | n < 0 = parenIf (i > 1) $
            printBinOpInfix (getTextFromDefaultOp n)
            (printTType' op 2 bs fs t1)
            (printTType' op 0 bs fs t2)
  | otherwise = let (s,inf,_) = op !! n
                in if inf
                   then parenIf (i > 1) $
                        printBinOpInfix s
                        (printTType' op 2 bs fs t1)
                        (printTType' op 0 bs fs t2)
                   else parenIf (i > 1) $
                        printBinOpPrefix s
                        (printTType' op 2 bs fs t1)
                        (printTType' op 0 bs fs t2)
printTType' op i bs fs (RenameTTy n [t])
  | n < 0 = parenIf (i > 1) $
            printUnaryOpPrefix (getTextFromDefaultOp n)
            (printTType' op 2 bs fs t)
  | otherwise = let (s,_,_) = op !! n
                in parenIf (i > 1) $
                   printUnaryOpPrefix s
                   (printTType' op 2 bs fs t)
printTType' _ _ _ _ (RenameTTy _ _) = error "error: printTType', no debería pasar."

getTextFromDefaultOp :: Int -> String
getTextFromDefaultOp n = fst $ defaults_op !! (n + num_defaults_op)

-- Pretty-printer de tipos con nombres.
-- Consideramos que las operaciones "custom", son a lo suma binaria.
-- Además, que las operaciones unaria solo se imprimen de forma prefija.
printType :: [UserOperation] -> Type -> Doc
printType = printType' False

printType' :: Bool -> [UserOperation] -> Type -> Doc
printType' _ _ (B v)             = text v
printType' False op (Fun t1 t2)  = printType' True op t1 <+> 
                                   text "->"          <+> 
                                   printType' False op t2
printType' False op (ForAll v t) = text "forall" <+>
                                   text v <>
                                   text "," <+>
                                   printType' False op t
printType' False op (RenameTy s [t1, t2])
  | (s == and_text) || (s == or_text) = printBinOpInfix s
                                        (printType' True op t1)
                                        (printType' False op t2)
  | otherwise = case find (\(x,_,_) -> x == s) op of
                  Just (_,False,_) -> printBinOpPrefix s
                                      (printType' True op t1)
                                      (printType' False op t2)
                  Just (_, True, _) -> printBinOpInfix s
                                      (printType' True op t1)
                                      (printType' False op t2)                  
                  Nothing -> error "error: printType' no debería pasar."
printType' False op (RenameTy s [t]) =
  case find (\(x,_,_) -> x == s) op of
    Just _ -> printUnaryOpPrefix s
              (printType' True op t)
    Nothing -> error "error: printType' no debería pasar."
printType' False op (RenameTy _ _) = error "error: printType' no debería pasar."
printType' True op t               = PP.parens $ printType' False op t


printBinOpInfix :: String -> Doc -> Doc -> Doc
printBinOpInfix s d1 d2 = d1 <+> 
                          text s <+>
                          d2

printBinOpPrefix :: String -> Doc -> Doc -> Doc
printBinOpPrefix s d1 d2 = text s <+>
                           d1 <+>
                           d2

printUnaryOpPrefix :: String -> Doc -> Doc
printUnaryOpPrefix s d = text s <+>
                         d
                          
printProof :: Int -> [UserOperation] -> (FTypeContext, BTypeContext) -> TermContext -> [Maybe (Type, TType)] -> Doc
printProof tp op tc c tys =
  (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
  printContext op tc c $$
  printGoals tp op tys


printGoals :: Int -> [UserOperation] -> [Maybe (Type, TType)] -> Doc
printGoals = printGoals' 1

printGoals' :: Int -> Int -> [UserOperation] -> [Maybe (Type, TType)] -> Doc
printGoals' _ _ _ [] = empty
printGoals' i tp op (ty:tys)
  | i <= tp = (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
              printGoal op ty $$
              printGoals' (i+1) tp op tys
  | otherwise = empty

printGoal :: [UserOperation] -> Maybe (Type, TType) -> Doc
printGoal op (Just (ty,_)) = printType' False op ty
printGoal op Nothing = text "Prop"


printContext :: [UserOperation] -> (FTypeContext, BTypeContext) -> TermContext -> Doc
printContext op (ftc,btc) c = printFTypeContext ftc $$
                              printRestContext op btc c


printFTypeContext :: FTypeContext -> Doc
printFTypeContext [] = empty
printFTypeContext (x:ftc) = printFTypeVar x $$
                            printFTypeContext ftc

printFTypeVar :: FTypeVar -> Doc
printFTypeVar x = text x <+>
                  text ":" <+>
                  text "Prop"

printRestContext :: [UserOperation] -> BTypeContext -> TermContext -> Doc
printRestContext op btc c
  | S.null btc = printRestTermC op c
  | S.null c = printRestBTypeC btc
  | otherwise = let x = S.index btc 0
                    y = S.index c 0
                in if fst x > fst4 y
                   then printRestContext op (S.drop 1 btc) c $$
                        printBTypeVar x
                   else printRestContext op btc (S.drop 1 c) $$
                        printTermVar (S.length c) op y

printRestTermC :: [UserOperation] -> TermContext -> Doc
printRestTermC op c
  | S.null c = empty
  | otherwise = printRestTermC op (S.drop 1 c) $$
                printTermVar (S.length c) op (S.index c 0)

printRestBTypeC :: BTypeContext -> Doc
printRestBTypeC btc
  | S.null btc = empty
  | otherwise = printRestBTypeC (S.drop 1 btc) $$
                printBTypeVar (S.index btc 0)

printTermVar :: Int -> [UserOperation] -> TermVar -> Doc
printTermVar n op (_,_,t,_) = text "H" <>
                              text (show (n-1)) <+> 
                              text ":" <+>
                              printType op t

printBTypeVar :: BTypeVar -> Doc
printBTypeVar (_,x) = text x <+>
                      text ":" <+>
                      text "Prop"

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x
