module Rules where

import Common
import DefaultOperators

-- Reglas de eliminación e introducción del "and","or", y "bottom".

intro_and :: LTerm2
intro_and =
  (
    ( BAbs "a" $ BAbs "b" $ Abs () (TVar ("a", Bound 1)) $ Abs () (TVar ("b", Bound 0)) $ BAbs "c" $
      Abs () (Fun (TVar ("a", Bound 2)) $ Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $
      ((LVar $ Bound 0) :@: (LVar $ Bound 2)) :@: (LVar $ Bound 1)
    ) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (TVar ("a", Bound 1)) $ Fun (TVar ("b", Bound 0)) $
      RenamedType and_id [TVar ("a", Bound 1), TVar ("b", Bound 0)]
    )
  )

-- Teorema de eliminación del and "general": forall a b c, a /\ b -> (a -> b -> c) -> c
elim_and :: LTerm2
elim_and =
  (
    ( BAbs "a" $ BAbs "b" $ BAbs "c" $ Abs ()
      (RenamedType and_id [TVar ("a", Bound 2) , TVar ("b", Bound 1)]) $
      Abs () (Fun (TVar ("a", Bound 2)) (Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0)))) $
      (LVar $ Bound 1) :!: (TVar ("c", Bound 0)) :@: (LVar $ Bound 0)
    ) :::
    (
      ForAll "a" $ ForAll "b" $ ForAll "c" $
      Fun (RenamedType and_id [TVar ("a", Bound 2), TVar ("b", Bound 1)]) $
      Fun (Fun (TVar ("a", Bound 2)) $ Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $
      TVar ("c", Bound 0)
    )
  )

intro_or1 :: LTerm2
intro_or1 =
  (
    ( BAbs "a" $ BAbs "b" $ Abs () (TVar ("a", Bound 1)) $ BAbs "c" $
      Abs () (Fun (TVar ("a", Bound 2)) (TVar ("c", Bound 0))) $
      Abs () (Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $
      (LVar $ Bound 1) :@: (LVar $ Bound 2)
    ) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (TVar ("a", Bound 1)) $
      RenamedType or_id [TVar ("a", Bound 1), TVar ("b", Bound 0)]
    )
  )

intro_or2 :: LTerm2
intro_or2 =
  (
    ( BAbs "a" $ BAbs "b" $ Abs () (TVar ("b", Bound 0)) $ BAbs "c" $
      Abs () (Fun (TVar ("a", Bound 2)) (TVar ("c", Bound 0))) $
      Abs () (Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $
      (LVar $ Bound 0) :@: (LVar $ Bound 2)
    ) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (TVar ("b", Bound 0)) $
      RenamedType or_id [TVar ("a", Bound 1), TVar ("b", Bound 0)]
    )
  )

elim_or :: LTerm2
elim_or =
  (
    ( BAbs "a" $ BAbs "b" $ BAbs "c" $ Abs ()
      (RenamedType or_id [TVar ("a", Bound 2), TVar ("b", Bound 1)]) $
      Abs () (Fun (TVar ("a", Bound 2)) (TVar ("c", Bound 0))) $
      Abs () (Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $
      ((LVar $ Bound 2) :!: (TVar ("c", Bound 0)) :@: (LVar $ Bound 1)) :@: (LVar $ Bound 0)
    ) :::
    (
      ForAll "a" $ ForAll "b" $ ForAll "c" $
      Fun (RenamedType or_id [TVar ("a", Bound 2), TVar ("b", Bound 1)]) $
      Fun (Fun (TVar ("a", Bound 2)) (TVar ("c", Bound 0))) $
      Fun (Fun (TVar ("b", Bound 1)) (TVar ("c", Bound 0))) $ TVar ("c", Bound 0)
    )
  )

intro_bottom :: LTerm2
intro_bottom =
  (
    ( BAbs "a" $ Abs () (TVar ("a", Bound 0)) $ Abs () (RenamedType not_id [TVar ("a", Bound 0)]) $
      (LVar $ Bound 0) :@: (LVar $ Bound 1)
    ) :::
    (
      ForAll "a" $ Fun (TVar ("a", Bound 0)) $ Fun (RenamedType not_id [TVar ("a", Bound 0)]) $
      RenamedType bottom_id []
    )
  )
  
elim_bottom :: LTerm2
elim_bottom =
  (
    ( BAbs "a" $ Abs () (RenamedType bottom_id []) $ (LVar $ Bound 0) :!: (TVar ("a", Bound 0))
    ) :::
    (
      ForAll "a" $ Fun (RenamedType bottom_id []) $ TVar ("a", Bound 0)
    )
  )
