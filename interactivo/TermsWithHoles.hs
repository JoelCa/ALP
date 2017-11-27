module TermsWithHoles where

import Common

  -- Termino con a lo sumo dos aujeros de tipo "a", o un término de tipo "b".
data Term2Holes a b = Hole (a -> a) | DoubleHole (a -> a -> a)
                    | Term1 a | Term2 b

  -- Término con aujeros de tipo "a" sobre un tipo "b".
data TermHoles a b = OneHole (a -> b) | Holes (a -> TermHoles a b)

type T2Holes a b = Term2Holes a (TermHoles b a)

type THoles a b = [T2Holes a b]

type LTerm2Holes = T2Holes DoubleLTerm DoubleType

  -- Lamda término con aujeros de términos y tipos.
type LTermHoles = THoles DoubleLTerm DoubleType

-- Funciones que operan sobre los lambda términos con aujeros.

simplify1 :: a -> THoles a b -> THoles a b
simplify1 t [Hole et] = [Term1 $ et t]
simplify1 t ((DoubleHole et):ts) = (Hole $ et t):ts
simplify1 t ((Hole et):(DoubleHole et'):ts) = (Hole $ (et' . et) t):ts

simplify2 :: b -> THoles a b -> THoles a b
simplify2 ty (Term2 (OneHole h) : ts) = simplify1 (h ty) ts
simplify2 ty (Term2 (Holes h) : ts) = (Term2 $ h ty) : ts

addHole1 :: (a -> a) -> THoles a b -> THoles a b
addHole1 et ((Hole et'):ts) = (Hole $ et' . et):ts
addHole1 et ((DoubleHole et'):ts) = (DoubleHole $ et' . et):ts

addHole2 :: (a -> a -> a) -> THoles a b -> THoles a b
addHole2 et ((Hole et'):ts) = (DoubleHole $ (\f -> et' . f) . et):ts
addHole2 et ((DoubleHole et'):ts) = (DoubleHole et):(DoubleHole et'):ts

addT2H :: T2Holes a b -> THoles a b -> THoles a b
addT2H (Term1 x) ts = simplify1 x ts
addT2H (Term2 x) ts = Term2 x : ts


simplifyType :: DoubleType -> LTermHoles -> LTermHoles
simplifyType = simplify2

simplifyLTerm :: DoubleLTerm -> LTermHoles -> LTermHoles
simplifyLTerm = simplify1

addHT :: (DoubleLTerm -> DoubleLTerm) -> LTermHoles -> LTermHoles
addHT = addHole1

addDHT :: (DoubleLTerm -> DoubleLTerm -> DoubleLTerm) -> LTermHoles -> LTermHoles
addDHT = addHole2

addTypeHoleInTerm :: LTerm2Holes -> LTermHoles -> LTermHoles
addTypeHoleInTerm = addT2H

---------------------------------------------------------------------

addHole3 :: (a -> b -> a) -> T2Holes a b -> T2Holes a b
addHole3 f (Term1 te) = Term2 $ OneHole $ \y -> f te y
addHole3 f (Term2 hte) = Term2 $ Holes $ \y -> addTerm2 f y hte
addHole3 _ _ = error "error: addHole3, no debería pasar."

addTerm1 :: (a -> b -> a) -> b -> T2Holes a b -> T2Holes a b
addTerm1 f x (Term1 te) = Term1 $ f te x
addTerm1 f x (Term2 hte) = Term2 $ addTerm2 f x hte
addTerm1 _ _ _ = error "error: addTerm, no debería pasar."

addTerm2 :: (a -> b -> a) -> b -> TermHoles b a -> TermHoles b a
addTerm2 f x (OneHole h) = OneHole $ \y -> f (h y) x
addTerm2 f x (Holes h) = Holes $ \y -> addTerm2 f x (h y)

-- addTypeHole añade al lambda término (1° arg.), un aujero de tipo;
-- es decir una instancia de tipo "vacia".
addTypeHole :: LTerm2Holes -> LTerm2Holes
addTypeHole = addHole3 (:!:)

-- addTypeTerm añade al lambda término (1° arg.), el tipo dado por su 2° arg.
addTypeTerm :: DoubleType -> LTerm2Holes -> LTerm2Holes
addTypeTerm = addTerm1 (:!:)

---------------------------------------------------------------------

empty :: THoles a b
empty = [Hole id]

noHolesTerm1 :: THoles a b -> Bool
noHolesTerm1 [Term1 _] = True
noHolesTerm1 _ = False

getTerm1 :: THoles a b -> Maybe a
getTerm1 [Term1 t] = Just t
getTerm1 _ = Nothing

emptyLTerm :: LTermHoles
emptyLTerm = empty
  
withoutHoles :: LTermHoles -> Bool
withoutHoles = noHolesTerm1

getLTermNoHoles :: LTermHoles -> Maybe DoubleLTerm
getLTermNoHoles = getTerm1
