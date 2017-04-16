module PrettyPrinter where

import Common
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP 
import Data.List
import qualified Data.Sequence as S
import qualified Data.Vector as V

-----------------------
--- pretty printer
-----------------------

-- Lista de posibles nombres para variables de términos.
vars :: [String]
vars = [ c : n | n <- "" : map show nats, c <- ['x','y','z'] ++ ['p'..'w'] ]
  where nats :: [Integer]
        nats = [1..]

-- Lista de posibles nombres para variables de tipos.
typeVars :: [String]
typeVars = [ c : n | n <- "" : map show nats, c <- ['a' .. 'o']]
  where nats :: [Integer]
        nats = [1..]

-- Variables de términos libres del 1º arg.
fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (Global n)) = [n]
fv (Free (Quote _))  = []
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u
fv (t :!: _)         = fv t
fv (BLam _ t)        = fv t

-- Variables de tipo libres del 1º arg.
ftv :: Term -> [String]
ftv (Bound _) = []
ftv (Free _)  = []
ftv (x :@: y) = ftv x ++ ftv y
ftv (Lam (_,t) x) = fType t ++ fv x
ftv (x :!: (_,t)) = ftv x ++ fType t
ftv (BLam b x)  = ftv x \\ [b]

-- Variables de tipos libres del tipo (sin nombre) dado por el 1º arg.
fType :: TType -> [String]
fType (TBound  _) = []
fType (TFree n) = [n]
fType (TFun t u) = fType t ++ fType u
fType (TForAll t) = fType t
fType (RenameTTy _ ts) = foldr (\x r -> fType x ++ r) [] ts

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = PP.parens d

-- Pretty-printer de términos, con tipos sin nombres.
printTermTType :: FOperations -> Term -> Doc 
printTermTType op t = printTermTType' op 1 [] [] (vars \\ fv t) (typeVars \\ ftv t) t

printTermTType' :: FOperations -> Int -> [String] -> [String] -> [String] -> [String] -> Term -> Doc
printTermTType' _ _ bs _  _ _ (Bound j)             = text $ bs !! j
printTermTType' _ _ _  _  _ _ (Free (Global n))     = text n
printTermTType' _ _ _  _  _ _ (Free (Quote n))      = text "quoted" <> text (show n)
printTermTType' op i bs bts fs fts (t :@: u@(Lam _ _)) = parenIf (i < 1) $ 
                                                         printTermTType' op 2 bs bts fs fts t <+> 
                                                         printTermTType' op (if i == 2 then 2 else 0) bs bts fs fts u
printTermTType' op i bs bts fs fts (t :@: u@(BLam _ _)) = parenIf (i < 1) $ 
                                                          printTermTType' op 2 bs bts fs fts t <+> 
                                                          printTermTType' op (if i == 2 then 2 else 0) bs bts fs fts u
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
printTermTType' op i bs bts fs (f':fts) (BLam _ u)   = parenIf (i > 1) $
                                                       text "\\" <> 
                                                       text f' <> 
                                                       text "." <> 
                                                       printTermTType' op 1 bs (f':bts) fs fts u
printTermTType' op i bs bts fs fts (u :!: (_,t))     = printTermTType' op 0 bs bts fs fts u <+>
                                                       text "[" <>
                                                       printTypeTermTType op bts t <>
                                                       text "]"
printTermTType' _ _ _ _ [] _ (Lam _ _)              = error "prinTerm': no hay nombres para elegir"
printTermTType' _ _ _ _ _ [] (BLam _ _)             = error "prinTerm': no hay nombres para elegir"


printTypeTermTType :: FOperations -> [String] -> TType -> Doc
printTypeTermTType op bs t = printTType' op (7,7,False) bs ((typeVars \\ fType t) \\ bs) t


-- Pretty-printer de términos, con tipos con nombres.
printTerm :: FOperations -> Term -> Doc 
printTerm op t = printTerm' op 1 [] (vars \\ fv t)  t


--Arreglar paréntesis de :@:
printTerm' :: FOperations -> Int -> [String] -> [String] -> Term -> Doc
printTerm' _ _ bs _  (Bound j)         = text $ bs !! j
printTerm' _ _ _  _  (Free (Global n)) = text n
printTerm' _ _ _  _  (Free (Quote n))  = text "quoted" <> text (show n)
printTerm' op i bs fs (t :@: u@(Lam _ _)) = parenIf (i < 1) $ 
                                            printTerm' op 2 bs fs t <+> 
                                            printTerm' op (if i == 2 then 2 else 0) bs fs u
printTerm' op i bs fs (t :@: u@(BLam _ _)) = parenIf (i < 1) $ 
                                            printTerm' op 2 bs fs t <+> 
                                            printTerm' op (if i == 2 then 2 else 0) bs fs u                                            
printTerm' op i bs fs (t :@: u)         = parenIf (i < 1) $ 
                                          printTerm' op 2 bs fs t <+> 
                                          printTerm' op 0 bs fs u
printTerm' op i bs (f:fs) (Lam (t,_) u) = parenIf (i > 1) $ 
                                          text "\\" <> 
                                          text f <> 
                                          text ":" <> 
                                          parenIf False (printType op t) <>
                                          text "." <>
                                          printTerm' op 1 (f:bs) fs u
printTerm' op i bs fs (BLam x u)        = parenIf (i > 1) $
                                          text "\\" <> 
                                          text x <> 
                                          text "." <>
                                          printTerm' op 1 bs fs u
printTerm' op i bs fs (t :!: (ty,_))    = printTerm' op 0 bs fs t <+>
                                          text "[" <>
                                          printType op ty <>
                                          text "]"
printTerm' _ _ _ [] (Lam _ _)           = error "prinTerm': no hay nombres para elegir"



-- Pretty-printer de tipos sin nombres.
printTType :: FOperations -> TType -> Doc
printTType op t = printTType' op (7,7,False) [] (typeVars \\ fType t) t

-- Chequear si es necesario usar parenIf
printTType' :: FOperations -> (Int, Int, Bool) -> [String] -> [String] -> TType -> Doc
printTType' op _ bs _ (TBound n) = text $ bs !! n
printTType' op _ bs _ (TFree n) = text n
printTType' op prec bs fs (TFun t1 t2) =
  printBinInfix (\x t -> printTType' op x bs fs t) "->" prec 5 t1 t2
printTType' op (i,j,k) bs (f:fs) (TForAll t) =
  parenIf (i < 7) $ 
  text "forall" <+> 
  text f <> 
  text "," <+> 
  printTType' op (7,j,k) (f:bs) fs t
printTType' op (i,j,k) bs (f:fs) (TExists t) =
  parenIf (i < 7) $ 
  text "exists" <+> 
  text f <> 
  text "," <+> 
  printTType' op (7,j,k) (f:bs) fs t
printTType' op prec@(i,j,k) bs fs (RenameTTy n [t1,t2])
  | n == and_code = printBinInfix (\x t -> printTType' op x bs fs t)
                    (getTextFromDefaultOp n) prec 3 t1 t2
  | n == or_code = printBinInfix (\x t -> printTType' op x bs fs t)
                   (getTextFromDefaultOp n) prec 4 t1 t2
  | n == iff_code = printBinInfix (\x t -> printTType' op x bs fs t)
                    (fst4 $ op V.! n) prec 6 t1 t2
  | otherwise = let (s,_,_,inf) = op V.! n
                in if inf
                   then parenIf ( i < 2 || ( i == 2 && ( j < n || ( j == n && k )))) $
                        printTType' op (2, n, True) bs fs t1 <+>
                        text s <+> 
                        printTType' op (2, n, False) bs fs t2
                   else printBinPrefix (\x t -> printTType' op x bs fs t) s prec t1 t2
printTType' op prec bs fs (RenameTTy n [t]) =
  printUnaryPrefix (\x t -> printTType' op x bs fs t) (fst4 $ op V.! n) prec t
printTType' op i bs fs (RenameTTy n [])
  | n == bottom_code = text $ bottom_text
  | otherwise = text (fst4 $ op V.! n)
printTType' _ _ _ _ (RenameTTy _ _) =
  error "error: printTType', no debería pasar."

getTextFromDefaultOp :: Int -> String
getTextFromDefaultOp n = case find (\(_,x,_) -> x == n) notFoldeableOps of
                           Just (a,_,_) -> a
                           Nothing -> error "error: getTextFromDefaultOp, no debería pasar."

-- Pretty-printer de tipos con nombres.
-- Consideramos que las operaciones "custom", son a lo suma binaria.
-- Además, que las operaciones unaria solo se imprimen de forma prefija.
-- Obs: Basta con que la primera componente de la tripleta, que se pasa como argumento a
-- printType', sea mayor o igual a 7, para asegurar que no aparescan paréntesis "externos".
printType :: FOperations -> Type -> Doc
printType = printType' (7,7,False)

printType' :: (Int, Int, Bool) -> FOperations -> Type -> Doc
printType' _ _ (B v) =
  text v
printType' prec op (Fun t1 t2) =
  printBinInfix (\x t -> printType' x op t) "->" prec 5 t1 t2
printType' (i,j,k) op (ForAll v t) =
  parenIf (i < 7) $
  text "forall" <+>
  text v <>
  text "," <+>
  printType' (7,j,k) op t
printType' (i,j,k) op (Exists v t) =
  parenIf (i < 7) $
  text "exists" <+>
  text v <>
  text "," <+>
  printType' (7,j,k) op t
printType' prec@(i,j,k) op (RenameTy s [t1, t2])
  | s == and_text = printBinInfix (\x t -> printType' x op t) s prec 3 t1 t2
  | s == or_text = printBinInfix (\x t -> printType' x op t) s prec 4 t1 t2
  | s == iff_text = printBinInfix (\x t -> printType' x op t) s prec 6 t1 t2
  | otherwise = case getElemIndex (\(x,_,_,_) -> x == s) op of
          Just (_, (_,_,_,False)) ->
            printBinPrefix (\x t -> printType' x op t) s prec t1 t2
          Just (n, (_,_,_,True)) ->
            parenIf ( i < 2 || ( i == 2 && ( j < n || ( j == n && k )))) $
            printType' (2, n, True) op t1 <+>
            text s <+> 
            printType' (2, n, False) op t2
          _ -> error "error: printType' no debería pasar."
printType' prec op (RenameTy s [t]) =
  printUnaryPrefix (\x t -> printType' x op t) s prec t
printType' _ _ (RenameTy s []) =
  text s
printType' _ _ (RenameTy _ _) =
  error "error: printType' no debería pasar."

printBinPrefix :: ((Int, Int, Bool) -> a -> Doc) -> String
               -> (Int, Int, Bool) -> a -> a -> Doc
printBinPrefix f s (i, j, k) t1 t2 =
  parenIf (i == 0) $
  text s <+>
  f (0, j, k) t1 <+>
  f (0, j, k) t2

printUnaryPrefix :: ((Int, Int, Bool) -> a -> Doc) -> String
                 -> (Int, Int, Bool) -> a -> Doc
printUnaryPrefix f s (i, j, k) t
  | s == not_text = parenIf (i < 1) $
                    text s <+>
                    f (1, j, k) t
  | otherwise = parenIf (i == 0) $
                text s <+>
                f (0, j, k) t

printBinInfix :: ((Int, Int, Bool) -> a -> Doc) -> String
              -> (Int, Int, Bool) -> Int -> a -> a -> Doc              
printBinInfix f s (i,j,k) n t1 t2 =
  parenIf (i < n || ( (i == n) && k)) $
  f (n, j, True) t1 <+>
  text s <+> 
  f (n, j, False) t2

-- Pretty-printer de la prueba.
printProof :: Int -> FOperations -> FTypeContext -> [SubProof] -> Doc
printProof tp op ftc sb =
  (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
  printContext op (ftc, bTypeContext s) (termContext s) $$
  printGoals tp op sb
  where s = head sb

-- Imprime el tipo objetivo de cada subprueba.
printGoals :: Int -> FOperations -> [SubProof] -> Doc
printGoals = printGoals' 1

printGoals' :: Int -> Int -> FOperations -> [SubProof] -> Doc
printGoals' _ _ _ [] = empty
printGoals' i tp op (s:sb) =
  printLevelGoals i tp op (ty s) $$
  printGoals' (i+(lsubp s)) tp op sb

-- Imprime los tipos objetivos de cada nivel.
printLevelGoals :: Int -> Int -> FOperations -> [Maybe (Type, TType)] -> Doc
printLevelGoals _ _ _ [] =
  empty
printLevelGoals i tp op (t:ts) =
  (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
  printGoal op t $$
  printLevelGoals (i+1) tp op ts

printGoal :: FOperations -> Maybe (Type, TType) -> Doc
printGoal op (Just (ty,_)) = printType op ty
printGoal op Nothing = text "Prop"

printContext :: FOperations -> (FTypeContext, BTypeContext) -> TermContext -> Doc
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

printRestContext :: FOperations -> BTypeContext -> TermContext -> Doc
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

printRestTermC :: FOperations -> TermContext -> Doc
printRestTermC op c
  | S.null c = empty
  | otherwise = printRestTermC op (S.drop 1 c) $$
                printTermVar (S.length c) op (S.index c 0)

printRestBTypeC :: BTypeContext -> Doc
printRestBTypeC btc
  | S.null btc = empty
  | otherwise = printRestBTypeC (S.drop 1 btc) $$
                printBTypeVar (S.index btc 0)

printTermVar :: Int -> FOperations -> TermVar -> Doc
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
