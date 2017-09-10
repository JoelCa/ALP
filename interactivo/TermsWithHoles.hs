module TermsWithHoles where

import Common

  -- Termino con a lo sumo dos aujeros de tipo "a", o un término de tipo "b".
data Term2Holes a b = Hole (a -> a) | DoubleHole (a -> a -> a)
                    | Term1 a | Term2 b

  -- Término con aujeros de tipo "a" sobre un tipo "b".
data TermHoles a b = OneHole (a -> b) | Holes (a -> TermHoles a b)

type TypeHoles = TermHoles DoubleType LTerm2

type LTerm2Holes = Term2Holes LTerm2 TypeHoles 

type LTermHoles = [LTerm2Holes] 

-- instance Show (LTermHoles) where
--   show (Term1 t) = show t
--   show _ = "término con aujeros"

-- Funciones que operan sobre los lambda términos con aujeros.

simplifyTypeInTerm :: DoubleType -> LTermHoles -> LTermHoles
simplifyTypeInTerm ty (Term2 (OneHole h) : ts) = simplify (h ty) ts
simplifyTypeInTerm ty (Term2 (Holes h) : ts) = (Term2 $ h ty) : ts

simplify :: LTerm2 -> LTermHoles -> LTermHoles
simplify t [Hole et] = [Term1 $ et t]
simplify t ((DoubleHole et):ts) = (Hole $ et t):ts
simplify t ((Hole et):(DoubleHole et'):ts) = (Hole $ (et' . et) t):ts

addHT :: (LTerm2 -> LTerm2) -> LTermHoles -> LTermHoles
addHT et ((Hole et'):ts) = (Hole $ et' . et):ts
addHT et ((DoubleHole et'):ts) = (DoubleHole $ et' . et):ts

addDHT :: (LTerm2 -> LTerm2 -> LTerm2) -> LTermHoles -> LTermHoles
addDHT et ((Hole et'):ts) = (DoubleHole $ (\f -> et' . f) . et):ts
addDHT et ((DoubleHole et'):ts) = (DoubleHole et):(DoubleHole et'):ts

addTypeHoleInTerm :: LTerm2Holes -> LTermHoles -> LTermHoles
addTypeHoleInTerm (Term1 x) ts = simplify x ts
addTypeHoleInTerm (Term2 x) ts = Term2 x : ts


-- addTypeHole añade al lambda término (1° arg.), un aujero de tipo;
-- es decir una instancia de tipo "vacia".
addTypeHole :: LTerm2Holes -> LTerm2Holes
addTypeHole (Term1 te) = Term2 $ OneHole $ \y -> te :!: y
addTypeHole (Term2 hte) = Term2 $ Holes $ \y -> addType hte y
addTypeHole _ = error "error: addTypeHole, no debería pasar."

-- addTypeTerm añade al lambda término (1° arg.), el tipo dado por su 2° arg.
addTypeTerm :: LTerm2Holes -> DoubleType -> LTerm2Holes
addTypeTerm (Term1 te) x = Term1 $ te :!: x
addTypeTerm (Term2 hte) x = Term2 $ addType hte x
addTypeTerm _ _ = error "error: addTypeTermST, no debería pasar."

-- addType añade al lambda término con aujeros de tipos (1° arg.),
-- el tipo dado por su 2° arg.
addType :: TypeHoles -> DoubleType -> TypeHoles
addType (OneHole h) x = OneHole $ \y -> h y :!: x
addType (Holes h) x = Holes $ \y -> addType (h y) x

withoutHoles :: LTermHoles -> Bool
withoutHoles [Term1 _] = True
withoutHoles _ = False

getLTermNoHoles :: LTermHoles -> Maybe LTerm2
getLTermNoHoles [Term1 t] = Just t
getLTermNoHoles _ = Nothing

emptyLTerm :: LTermHoles
emptyLTerm = [Hole id]
