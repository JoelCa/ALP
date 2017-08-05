module PrettyPrinter where

import Common
import Proof
import DefaultOperators
import Text.PrettyPrint
import Data.List
import qualified Data.Sequence as S
import Hypothesis (printHypothesis)
import qualified Data.IntSet as IS
import Data.Set (Set)
import qualified Data.Set as Set

-----------------------
--- pretty printer
-----------------------

-- Lista de posibles nombres para variables de términos.
vars :: [String]
vars = [ c : n | n <- "" : map show nats, c <- ['x','y','z'] ++ ['p'..'w'] ]
  where nats :: [Integer]
        nats = [1..]


varsAndOps :: DoubleType -> Set String
varsAndOps (TVar (x,_)) = Set.singleton x
varsAndOps (Fun t u) = Set.union (varsAndOps t) (varsAndOps u)
varsAndOps (ForAll x t) = Set.insert x $ varsAndOps t 
varsAndOps (Exists x t) = Set.insert x $ varsAndOps t
varsAndOps (RenamedType x ts) =
  foldr (\t r -> Set.insert x $ Set.union (varsAndOps t) r) Set.empty ts
 

-- Obtiene las siguientes variables:
-- a. Variables de términos libres.
-- b. Variables de tipo ligadas.
-- c. Variables de tipo libres.
-- d. Nombre de operadores.
varsInTerm :: LTerm2 -> Set String
varsInTerm (LVar (Free n)) =
  Set.singleton n
varsInTerm (w :@: u)          =
  Set.union (varsInTerm w) (varsInTerm u)
varsInTerm (BAbs x u)         =
  Set.insert x $ varsInTerm u
varsInTerm (w :!: t)      =
  Set.union (varsInTerm w) (varsAndOps t)
varsInTerm (Abs () t w)      =
  Set.union (varsInTerm w) (varsAndOps t)
varsInTerm (EPack t w t') =
  Set.union (varsInTerm w) (Set.union (varsAndOps t) (varsAndOps t'))
varsInTerm (EUnpack x () t u)     =
  Set.insert x $ Set.union (varsInTerm t) (varsInTerm u)
varsInTerm (w ::: t)      =
  Set.union (varsInTerm w) (varsAndOps t)
varsInTerm _              =
  Set.empty

--------------------------------------------------------------------------------------------  
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

-- Pretty-printer de lambda término con nombre, y tipos con nombres.
printLTerm :: FOperations -> DoubleLTerm -> Doc
printLTerm op = printLTerm' op (1, False)

printLTerm' :: FOperations -> (Int, Bool) -> DoubleLTerm -> Doc
printLTerm' _ _ (LVar (x,_)) =
  text x
printLTerm' op (i,j) (Abs x t e) =
  parenIf (i < pLam) $
  sep $
  text "\\" <> 
  text x <> 
  text ":" <> 
  printType op t <>
  text "." :
  [nest 2 $ printLTerm' op (pLam,j) e]
printLTerm' op (i, j) (t :@: u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $  
  sep $
  printLTerm' op (pApp, False) t :
  [printLTerm' op (pApp, True) u]
printLTerm' op (i, j) (BAbs x u) =
  parenIf (i < pBLam) $
  sep $
  text "\\" <> 
  text x <> 
  text "." :
  [nest 2 $ printLTerm' op (pBLam,j) u]
printLTerm' op (i, j) (x :!: ty) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $
  sep $
  printLTerm' op (pBApp, False) x :
  [ nest 2 $
    text "[" <>
    printType op ty <>
    text "]" ]
printLTerm' op (i, j) (EPack ty e tty) =
  parenIf (i < pEPack) $
  sep $
  text "{*" <>
  printType op ty <>
  text "," :
  printLTerm' op (pEPack, j) e <>
  text "}" :
  [ nest 2 $
    text "as" <+>
    printType op tty ]
printLTerm' op (i, j) (EUnpack x y e u) =
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
    printLTerm' op (pEUnpack, j) e <+>
    text "in" <+>
    printLTerm' op (pEUnpack, j) u ]
printLTerm' op (i, j) (t ::: ty) =
  parenIf (i == pAs) $
  sep $
  printLTerm' op (pAs, j) t :
  [ nest 2 $
    text "as" <+>
    parens (printType op ty) ]


-- Pretty-printer de lambda término sin nombre, y tipos con nombres.
printLTermNoName :: FOperations -> LTerm2 -> Doc 
printLTermNoName op t = printLTermNoName' op (1, False) [] (vars \\ (Set.toList $ varsInTerm t))  t

printLTermNoName' :: FOperations -> (Int, Bool) -> [String] -> [String] -> LTerm2 -> Doc
printLTermNoName' _ _ bs _  (LVar (Bound x)) =
  text $ bs !! x
printLTermNoName' _ _ _  _  (LVar (Free n)) =
  text n
printLTermNoName' op (i, j) bs fs (t :@: u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $   
  sep $
  printLTermNoName' op (pApp, False) bs fs t :
  [printLTermNoName' op (pApp, True) bs fs u]
printLTermNoName' op (i, j) bs (f:fs) (Abs () t u) =
  parenIf (i < pLam) $ 
  sep $
  text "\\" <> 
  text f <> 
  text ":" <> 
  printType op t <>
  text "." :
  [nest 2  $ printLTermNoName' op (pLam, j) (f:bs) fs u]
printLTermNoName' op (i,j) bs fs (BAbs x u) =
  parenIf (i < pBLam) $
  sep $
  text "\\" <> 
  text x <> 
  text "." :
  [nest 2 $ printLTermNoName' op (pBLam, j) bs fs u]
printLTermNoName' op (i,j) bs fs (t :!: ty) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $ 
  sep $
  printLTermNoName' op (pBApp, False) bs fs t :
  [ nest 2 $
    text "[" <>
    printType op ty <>
    text "]" ]
printLTermNoName' op (i,j) bs fs (EPack ty t tty) =
  parenIf (i < pEPack) $
  sep $
  text "{*" <>
  printType op ty <>
  text "," :
  printLTermNoName' op (pEPack, j) bs fs t <>
  text "}" :
  [ nest 2 $
    text "as" <+>
    printType op tty ]
printLTermNoName' op (i,j) bs (f:fs) (EUnpack x () t u) =
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
    printLTermNoName' op (pEUnpack, j) bs fs t <+>
    text "in" <+>
    printLTermNoName' op (pEUnpack, j) (f:bs) fs u ]
printLTermNoName' op (i,j) bs fs (t ::: ty) =
  parenIf (i == pAs) $
  sep $
  printLTermNoName' op (pAs, j) bs fs t :
  [ nest 2 $
    text "as" <+>
    parens (printType op ty) ]
printLTermNoName' _ _ _ [] (Abs _ _ _) =
  error "prinTerm': no hay nombres para elegir"
  
--------------------------------------------------------------------------------------------  
-- Pretty-printer de tipos con nombres.
-- Consideramos que las operaciones "custom", son a lo suma binaria.
-- Además, que las operaciones unaria solo se imprimen de forma prefija.
-- Obs: Basta con que la primera componente de la tripleta, que se pasa como argumento a
-- printType', sea mayor o igual a 7, para asegurar que no aparescan paréntesis "externos".
printType :: FOperations -> DoubleType -> Doc
printType = printType' (7,7,False)


printType' :: (Int, Int, Bool) -> FOperations -> DoubleType -> Doc
printType' _ _ (TVar (v, _)) =
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
printType' prec@(i,j,k) op (RenamedType s [t1, t2])
  | s == and_id = printBinInfix (\x t -> printType' x op t) s prec 3 t1 t2
  | s == or_id = printBinInfix (\x t -> printType' x op t) s prec 4 t1 t2
  | s == iff_id = printBinInfix (\x t -> printType' x op t) s prec 6 t1 t2
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
printType' prec op (RenamedType s ts) =
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
  | s == bottom_id = text $ bottom_id
  | otherwise = text s
printPrefix f s (i, j, k) [t]
  | s == not_id = parenIf (i < 1) $
                  text s <+>
                  f (1, j, k) t
  | otherwise = parenIf (i == 0) $
                text s <+>
                f (0, j, k) t
printPrefix f s (i, j, k) ts =
  parenIf (i == 0) $
  text s <+>
  foldl (\r t -> r <+> f (0,j,k) t) empty ts
  
--------------------------------------------------------------------------------------------  
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
printLevelGoals :: Int -> Int -> FOperations -> [Maybe DoubleType] -> Doc
printLevelGoals _ _ _ [] =
  empty
printLevelGoals i tp op (t:ts) =
  (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
  printGoal op t $$
  printLevelGoals (i+1) tp op ts

printGoal :: FOperations -> Maybe DoubleType -> Doc
printGoal op (Just ty) = printType op ty
printGoal op Nothing = text "*"

printContext :: IS.IntSet -> FOperations -> (FTypeContext, BTypeContext) -> TermContext -> Doc
printContext cn op (ftc,btc) c =
  printFTypeContext ftc $$
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
                in if fst x > fst3 y
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
printTermVar n op (_,_,t) =
  text (printHypothesis n) <+>
  text ":" <+>
  printType op t

printBTypeVar :: BTypeVar -> Doc
printBTypeVar (_,x) = text x

getElemIndex :: (a -> Bool) -> S.Seq a -> Maybe (Int, a)
getElemIndex f xs = S.foldlWithIndex (\r i x -> if f x then Just (i, x) else r) Nothing xs

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

--------------------------------------------------------------------------------------------  
-- Pretty-printer de los errores.
