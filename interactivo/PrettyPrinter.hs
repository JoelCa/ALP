module PrettyPrinter where

import Common
import Proof
import DefaultOperators
import Text.PrettyPrint
import Data.List
import qualified Data.Sequence as S
import Hypothesis (printHypothesis)
import qualified Data.IntSet as IS

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

-- Variables de términos libres.
fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (NGlobal n)) = [n]
fv (Free (Quote _))  = []
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u
fv (t :!: _)         = fv t
fv (BLam _ t)        = fv t
fv (Pack _ t _)      = fv t
fv (Unpack _ t u)    = fv t ++ fv u
fv (t ::: _)         = fv t

-- Variables de tipo libres.
ftv :: Term -> [String]
ftv (Bound _) = []
ftv (Free _)  = []
ftv (x :@: y) = ftv x ++ ftv y
ftv (Lam (_,t) x) = fType t ++ ftv x
ftv (x :!: (_,t)) = ftv x ++ fType t
ftv (BLam b x)  = ftv x \\ [b]
ftv (Pack (_,t) x (_,t')) = ftv x ++ fType t ++ fType t'
ftv (Unpack a x y) = (ftv x ++ ftv y) \\ [a]
ftv (x ::: (_, t)) = ftv x ++ fType t

-- Variables de tipos libres del tipo (sin nombre) dado por el 1º arg.
fType :: TType -> [String]
fType (TBound  _) = []
fType (TFree n) = [n]
fType (TFun t u) = fType t ++ fType u
fType (TForAll t) = fType t
fType (TExists t) = fType t
fType (RenameTTy _ ts) = foldr (\x r -> fType x ++ r) [] ts

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = parens d

-- Precedencias
pAs :: Int
pAs = 0

pApp :: Int
pApp = 1

pBApp :: Int
pBApp = 1

pLam :: Int
pLam = 2

pBLam :: Int
pBLam = 2

pEPack :: Int
pEPack = 2

pEUnpack :: Int
pEUnpack = 2

-- Pretty-printer de lambda término sin nombre, y tipos sin nombres.
printTermTType :: FOperations -> Term -> Doc 
printTermTType op t = printTermTType' op (1, False) [] [] (vars \\ fv t) (typeVars \\ ftv t) t

printTermTType' :: FOperations -> (Int, Bool) -> [String] -> [String] -> [String] -> [String]
                -> Term -> Doc
printTermTType' _ _ bs _  _ _ (Bound x)=
  text $ bs !! x
printTermTType' _ _ _  _  _ _ (Free (NGlobal n)) =
  text n
printTermTType' op (i, j) bs bts fs fts (t :@: u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $ 
  printTermTType' op (pApp, False) bs bts fs fts t <+> 
  printTermTType' op (pApp, True) bs bts fs fts u
printTermTType' op (i, j) bs bts (f:fs) fts (Lam (_,t) u) =
  parenIf (i < pLam) $ 
  text "\\" <> 
  text f <> 
  text ":" <> 
  printTypeTermTType op bts t <>
  text "." <>
  printTermTType' op (pLam, j) (f:bs) bts fs fts u
printTermTType' op (i, j) bs bts fs (f':fts) (BLam _ u) =
  parenIf (i < pBLam) $
  text "\\" <> 
  text f' <> 
  text "." <> 
  printTermTType' op (pBLam, j) bs (f':bts) fs fts u
printTermTType' op (i, j) bs bts fs fts (u :!: (_,t)) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $ 
  printTermTType' op (pBApp, False) bs bts fs fts u <+>
  text "[" <>
  printTypeTermTType op bts t <>
  text "]"
printTermTType' op (i, j) bs bts fs fts (Pack (_,ty) t (_,tty)) =
  parenIf (i < pEPack) $
  text "{*" <>
  printTypeTermTType op bts ty <>
  text "," <+>
  printTermTType' op (pEPack, j) bs bts fs fts t <>
  text "}" <+>
  text "as" <+>
  printTypeTermTType op bts tty
printTermTType' op (i, j) bs bts (f:fs) (f':fts) (Unpack _ t u) =
  parenIf (i < pEUnpack) $
  text "let" <+>
  text "{" <>
  text f' <>
  text "," <+>
  text f <>
  text "}" <+>
  text "=" <+>
  printTermTType' op (pEUnpack, j) bs bts fs fts t <+>
  text "in" <+>
  printTermTType' op (pEUnpack, j) (f:bs) (f':bts) fs fts u
printTermTType' op (i, j) bs bts fs fts (t ::: (_,ty)) =
  parenIf (i == pAs) $
  printTermTType' op (pAs, j) bs bts fs fts t <+>
  text "as" <+>
  printTypeTermTType op bts ty  
printTermTType' _ _ _ _ [] _ (Lam _ _) =
  error "prinTerm': no hay nombres para elegir"
printTermTType' _ _ _ _ _ [] (BLam _ _) =
  error "prinTerm': no hay nombres para elegir"

printTypeTermTType :: FOperations -> [String] -> TType -> Doc
printTypeTermTType op bs t = printTType' op (7,7,False) bs ((typeVars \\ fType t) \\ bs) t


-- Pretty-printer de lambda término sin nombre, y tipos con nombres.
printTerm :: FOperations -> Term -> Doc 
printTerm op t = printTerm' op (1, False) [] (vars \\ fv t)  t

printTerm' :: FOperations -> (Int, Bool) -> [String] -> [String] -> Term -> Doc
printTerm' _ _ bs _  (Bound x) =
  text $ bs !! x
printTerm' _ _ _  _  (Free (NGlobal n)) =
  text n
printTerm' op (i, j) bs fs (t :@: u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $   
  sep $
  printTerm' op (pApp, False) bs fs t :
  [printTerm' op (pApp, True) bs fs u]
printTerm' op (i, j) bs (f:fs) (Lam (t,_) u) =
  parenIf (i < pLam) $ 
  sep $
  text "\\" <> 
  text f <> 
  text ":" <> 
  printType op t <>
  text "." :
  [nest 2  $ printTerm' op (pLam, j) (f:bs) fs u]
printTerm' op (i,j) bs fs (BLam x u) =
  parenIf (i < pBLam) $
  sep $
  text "\\" <> 
  text x <> 
  text "." :
  [nest 2 $ printTerm' op (pBLam, j) bs fs u]
printTerm' op (i,j) bs fs (t :!: (ty,_)) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $ 
  sep $
  printTerm' op (pBApp, False) bs fs t :
  [ nest 2 $
    text "[" <>
    printType op ty <>
    text "]" ]
printTerm' op (i,j) bs fs (Pack (ty,_) t (tty,_)) =
  parenIf (i < pEPack) $
  sep $
  text "{*" <>
  printType op ty <>
  text "," :
  printTerm' op (pEPack, j) bs fs t <>
  text "}" :
  [ nest 2 $
    text "as" <+>
    printType op tty ]
printTerm' op (i,j) bs (f:fs) (Unpack x t u) =
  parenIf (i < pEUnpack) $
  sep $
  text "let" :
  text "{" <>
  text x <>
  text "," :
  text f <>
  text "}" <+>
  text "=" :
  [ nest 2 $
    printTerm' op (pEUnpack, j) bs fs t <+>
    text "in" <+>
    printTerm' op (pEUnpack, j) (f:bs) fs u ]
printTerm' op (i,j) bs fs (t ::: (ty, _)) =
  parenIf (i == pAs) $
  sep $
  printTerm' op (pAs, j) bs fs t :
  [ nest 2 $
    text "as" <+>
    parens (printType op ty) ]
printTerm' _ _ _ [] (Lam _ _) =
  error "prinTerm': no hay nombres para elegir"


-- Pretty-printer de lambda término con nombre, y tipos con nombres.
printLamTerm :: FOperations -> LamTerm -> Doc
printLamTerm op = printLamTerm' op (1, False)

printLamTerm' :: FOperations -> (Int, Bool) -> LamTerm -> Doc
printLamTerm' _ _ (LVar x ) =
  text x
printLamTerm' op (i,j) (Abs x t e) =
  parenIf (i < pLam) $
  sep $
  text "\\" <> 
  text x <> 
  text ":" <> 
  printType op t <>
  text "." :
  [nest 2 $ printLamTerm' op (pLam,j) e]
printLamTerm' op (i, j) (App t u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $  
  sep $
  printLamTerm' op (pApp, False) t :
  [printLamTerm' op (pApp, True) u]
printLamTerm' op (i, j) (BAbs x u) =
  parenIf (i < pBLam) $
  sep $
  text "\\" <> 
  text x <> 
  text "." :
  [nest 2 $ printLamTerm' op (pBLam,j) u]
printLamTerm' op (i, j) (BApp x ty) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $
  sep $
  printLamTerm' op (pBApp, False) x :
  [ nest 2 $
    text "[" <>
    printType op ty <>
    text "]" ]
printLamTerm' op (i, j) (EPack ty e tty) =
  parenIf (i < pEPack) $
  sep $
  text "{*" <>
  printType op ty <>
  text "," :
  printLamTerm' op (pEPack, j) e <>
  text "}" :
  [ nest 2 $
    text "as" <+>
    printType op tty ]
printLamTerm' op (i, j) (EUnpack x y e u) =
  parenIf (i < pEUnpack) $
  sep $
  text "let" :
  text "{" <>
  text x <>
  text "," :
  text y <>
  text "}" <+>
  text "=" :
  [ nest 2 $
    printLamTerm' op (pEUnpack, j) e <+>
    text "in" <+>
    printLamTerm' op (pEUnpack, j) u ]
printLamTerm' op (i, j) (As t ty) =
  parenIf (i == pAs) $
  sep $
  printLamTerm' op (pAs, j) t :
  [ nest 2 $
    text "as" <+>
    parens (printType op ty) ]


-- Pretty-printer de tipos sin nombres.
printTType :: FOperations -> TType -> Doc
printTType op t = printTType' op (7,7,False) [] (typeVars \\ fType t) t

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
                    (fst4 $ S.index op n) prec 6 t1 t2
  | otherwise = let (s,_,_,inf) = S.index op n
                in if inf
                   then parenIf ( i < 2 || ( i == 2 && ( j < n || ( j == n && k )))) $
                        printTType' op (2, n, True) bs fs t1 <+>
                        text s <+> 
                        printTType' op (2, n, False) bs fs t2
                   else printPrefix (\x t -> printTType' op x bs fs t) s prec [t1,t2]
printTType' op prec bs fs (RenameTTy n ts) =
  printPrefix (\x t -> printTType' op x bs fs t) (if n < 0 then getTextFromDefaultOp n else fst4 $ S.index op n) prec ts


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
  sep $
  text "forall" <+>
  text v <>
  text "," :
  [nest 2 $ printType' (7,j,k) op t]
printType' (i,j,k) op (Exists v t) =
  parenIf (i < 7) $
  sep $
  text "exists" <+>
  text v <>
  text "," :
  [nest 2 $ printType' (7,j,k) op t]
printType' prec@(i,j,k) op (RenameTy s _ [t1, t2])
  | s == and_text = printBinInfix (\x t -> printType' x op t) s prec 3 t1 t2
  | s == or_text = printBinInfix (\x t -> printType' x op t) s prec 4 t1 t2
  | s == iff_text = printBinInfix (\x t -> printType' x op t) s prec 6 t1 t2
  | otherwise = case getElemIndex (\(x,_,_,_) -> x == s) op of
          Just (_, (_,_,_,False)) ->
            printPrefix (\x t -> printType' x op t) s prec [t1,t2]
          Just (n, (_,_,_,True)) ->
            parenIf ( i < 2 || ( i == 2 && ( j < n || ( j == n && k )))) $
            sep $
            printType' (2, n, True) op t1 :
            [ text s <+>
              printType' (2, n, False) op t2 ]
          _ -> error "error: printType' no debería pasar."
printType' prec op (RenameTy s _ ts) =
  printPrefix (\x t -> printType' x op t) s prec ts


printBinInfix :: ((Int, Int, Bool) -> a -> Doc) -> String
              -> (Int, Int, Bool) -> Int -> a -> a -> Doc              
printBinInfix f s (i,j,k) n t1 t2 =
  parenIf (i < n || ( (i == n) && k)) $
  sep $
  f (n, j, True) t1 :
  [ text s <+>
    f (n, j, False) t2 ]


printPrefix :: ((Int, Int, Bool) -> a -> Doc) -> String
            -> (Int, Int, Bool) -> [a] -> Doc
printPrefix f s _ [] 
  | s == bottom_text = text $ bottom_text
  | otherwise = text s
printPrefix f s (i, j, k) [t]
  | s == not_text = parenIf (i < 1) $
                    text s <+>
                    f (1, j, k) t
  | otherwise = parenIf (i == 0) $
                text s <+>
                f (0, j, k) t
printPrefix f s (i, j, k) ts =
  parenIf (i == 0) $
  text s <+>
  foldl (\r t -> r <+> f (0,j,k) t) empty ts
  
-- Pretty-printer de la prueba.
printProof :: Int -> IS.IntSet -> FOperations -> FTypeContext -> [SubProof] -> Doc
printProof tp cn op ftc sb =
  (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
  printContext cn op (ftc, bTypeContext s) (termContext s) $$
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
printGoal op Nothing = text "*"

printContext :: IS.IntSet -> FOperations -> (FTypeContext, BTypeContext) -> TermContext -> Doc
printContext cn op (ftc,btc) c = printFTypeContext ftc $$
                                 printRestContext cn (IS.size cn + S.length c - 1) op btc c

printFTypeContext :: FTypeContext -> Doc
printFTypeContext = foldr (\x r -> printFTypeVar x $$ r) empty

printFTypeVar :: FTypeVar -> Doc
printFTypeVar x = text x

printRestContext :: IS.IntSet -> Int -> FOperations -> BTypeContext -> TermContext -> Doc
printRestContext cn n op btc c
  | S.null btc = printRestTermC cn n op c
  | S.null c = printRestBTypeC btc
  | otherwise = let x = S.index btc 0
                    y = S.index c 0
                in if fst x > fst4 y
                   then printRestContext cn n op (S.drop 1 btc) c $$
                        printBTypeVar x
                   else printRestContext cn' (n'-1) op btc (S.drop 1 c) $$
                        printTermVar n' op y
                        where (n', cn') = getValidName cn n

-- Obtiene el nombre una hipótesis.
-- Argumentos:
-- 1. Nombres conflictivos.
-- 2. Nombre "candidato" (mayor a los nombres conflictivos).
-- Resultado:
-- Tupla donde la 1º componente es el nombre para una hipótesis,
-- y la 2º componente es el 1º argumento, al que le extrajeron los
-- nombres conflictivos "visitados".
getValidName :: IS.IntSet -> Int -> (Int, IS.IntSet)
getValidName cn n = let (cn', isMember, _) = IS.splitMember n cn
                        n' = if isMember then n-1 else n
                    in (n', cn')

printRestTermC :: IS.IntSet -> Int -> FOperations -> TermContext -> Doc
printRestTermC cn n op c
  | S.null c = empty
  | otherwise = printRestTermC cn' (n'-1) op (S.drop 1 c) $$
                printTermVar n' op (S.index c 0)
                where (n', cn') = getValidName cn n

printRestBTypeC :: BTypeContext -> Doc
printRestBTypeC btc
  | null btc = empty
  | otherwise = printRestBTypeC (S.drop 1 btc) $$
                printBTypeVar (S.index btc 0)

printTermVar :: Int -> FOperations -> TermVarWithType -> Doc
printTermVar n op (_,_,t,_) =
  text (printHypothesis n) <+>
  text ":" <+>
  printType op t

printBTypeVar :: BTypeVar -> Doc
printBTypeVar (_,x) = text x
