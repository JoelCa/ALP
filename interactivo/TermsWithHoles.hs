module TermsWithHoles where

import Common


  -- Lamda término con aujeros de términos y tipos.
data LTermHoles = Hole (LTerm2 -> LTerm2) | DoubleHole (LTerm2 -> LTerm2 -> LTerm2)
                | LamTe LTerm2 | TypeHo TypeHole

  -- Lamda término con aujeros de tipos.
data TypeHole = HTe (DoubleType -> LTerm2) | HTy (DoubleType -> TypeHole)


instance Show (LTermHoles) where
  show (LamTe t) = show t
  show _ = "término con aujeros"

-- Funciones que operan sobre los lambda términos con aujeros.

simplifyTypeInTerm :: DoubleType -> [LTermHoles] -> [LTermHoles]
simplifyTypeInTerm ty (TypeHo (HTe h) : ts) = simplify (h ty) ts
simplifyTypeInTerm ty (TypeHo (HTy h) : ts) = (TypeHo $ h ty) : ts

simplify :: LTerm2 -> [LTermHoles] -> [LTermHoles]
simplify t [Hole et] = [LamTe $ et t]
simplify t ((DoubleHole et):ts) = (Hole $ et t):ts
simplify t ((Hole et):(DoubleHole et'):ts) = (Hole $ (et' . et) t):ts

addHT :: (LTerm2 -> LTerm2) -> [LTermHoles] -> [LTermHoles]
addHT et ((Hole et'):ts) = (Hole $ et' . et):ts
addHT et ((DoubleHole et'):ts) = (DoubleHole $ et' . et):ts

addDHT :: (LTerm2 -> LTerm2 -> LTerm2) -> [LTermHoles] -> [LTermHoles]
addDHT et ((Hole et'):ts) = (DoubleHole $ (\f -> et' . f) . et):ts
addDHT et ((DoubleHole et'):ts) = (DoubleHole et):(DoubleHole et'):ts

-- addTypeHole añade al lambda término de su primer arg., una instancia de tipo "vacia".
-- Retorna el TypeHole con la instacia "vacia".
addTypeHole :: LTermHoles -> TypeHole
addTypeHole (LamTe te) = HTe $ \y -> te :!: y
addTypeHole (TypeHo hte) = HTy $ \y -> addTypeTerm hte y
addTypeHole _ = error "error: newTypeHole, no debería pasar."

-- addTypeTermST añade al lambda término de su primer arg., una instancia de tipo "vacia".
-- Retorna el LTermHoles con la instacia "vacia".
addTypeTermST :: LTermHoles -> DoubleType -> LTermHoles
addTypeTermST (LamTe te) x = LamTe $ te :!: x
addTypeTermST (TypeHo hte) x = TypeHo $ addTypeTerm hte x
addTypeTermST _ _ = error "error: addTypeTerm, no debería pasar."

-- addTypeTerm añade al lambda término de su primer arg. (desempaquetando el TypeHole), una instancia de tipo,
-- con el tipo de su segundo argumento. Retorna el TypeHole con esta nueva instancia de tipo, respetando la misma
-- estructura del TypeHole de su primer arg.
addTypeTerm :: TypeHole -> DoubleType -> TypeHole
addTypeTerm (HTe h) x = HTe $ \y -> h y :!: x
addTypeTerm (HTy h) x = HTy $ \y -> addTypeTerm (h y) x
