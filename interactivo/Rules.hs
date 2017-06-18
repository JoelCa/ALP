module Rules where

import Common
import DefaultOperators

-- Reglas de eliminación e introducción del "and","or", y "bottom".

intro_and :: Term
intro_and =
  (
    (BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ BLam "c" $
     Lam (Fun (B "a") $ Fun (B "b") (B "c"), TFun (TBound 2) $ TFun (TBound 1) (TBound 0)) $
     (Bound 0 :@: Bound 2) :@: Bound 1) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (B "a") $ Fun (B "b") $ RenameTy and_text 2 [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 1) $ TFun (TBound 0) $ RenameTTy and_code [TBound 1, TBound 0]
    )
  )

-- Teorema de eliminación del and "general": forall a b c, a /\ b -> (a -> b -> c) -> c
elim_and :: Term
elim_and =
  (
    (BLam "a" $ BLam "b" $ BLam "c" $ Lam (RenameTy and_text 2 [B "a", B "b"], RenameTTy and_code [TBound 2, TBound 1]) $
     Lam (Fun (B "a") (Fun (B "b") (B "c")), TFun (TBound 2) (TFun (TBound 1) (TBound 0))) $
     (Bound 1) :!: (B "c", TBound 0) :@: (Bound 0)) :::
    (
      ForAll "a" $ ForAll "b" $ ForAll "c" $ Fun (RenameTy and_text 2 [B "a", B "b"]) $
      Fun (Fun (B "a") $ Fun (B "b") (B "c")) $ B "c"
    , TForAll $ TForAll $ TForAll $ TFun (RenameTTy and_code [TBound 2, TBound 1]) $
      TFun (TFun (TBound 2) (TFun (TBound 1) (TBound 0))) $ TBound 0
    )
  )

intro_or1 :: Term
intro_or1 =
  (
    (BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ BLam "c" $
     Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
     Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 1 :@: Bound 2) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (B "a") $ RenameTy or_text 2 [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 1) $ RenameTTy or_code [TBound 1, TBound 0]
    )
  )

intro_or2 :: Term
intro_or2 =
  (
    (BLam "a" $ BLam "b" $ Lam (B "b", TBound 0) $ BLam "c" $
     Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
     Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 0 :@: Bound 2) :::
    (
      ForAll "a" $ ForAll "b" $ Fun (B "b") $ RenameTy or_text 2 [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 0) $ RenameTTy or_code [TBound 1, TBound 0]
    )
  )

elim_or :: Term
elim_or =
  (
    (BLam "a" $ BLam "b" $ BLam "c" $ Lam (RenameTy or_text 2 [B "a",B "b"], RenameTTy or_code [TBound 2, TBound 1]) $
     Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
     Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $
     ((Bound 2 :!: (B "c", TBound 0)) :@: Bound 1) :@: Bound 0) :::
    (
      ForAll "a" $ ForAll "b" $ ForAll "c" $ Fun (RenameTy or_text 2 [B "a", B "b"]) $
      Fun (Fun (B "a") (B "c")) $ Fun (Fun (B "b") (B "c")) $ B "c"
    , TForAll $ TForAll $ TForAll $ TFun (RenameTTy or_code [TBound 2, TBound 1]) $
      TFun (TFun (TBound 2) (TBound 0)) $ TFun (TFun (TBound 1) (TBound 0)) $ TBound 0
    )
  )

intro_bottom :: Term
intro_bottom =
  (
    (BLam "a" $ Lam (B "a", TBound 0) $ Lam (RenameTy not_text 1 [B "a"], RenameTTy not_code [TBound 0]) $
     Bound 0 :@: Bound 1) :::
    (
      ForAll "a" $ Fun (B "a") $ Fun (RenameTy not_text 1 [B "a"]) $ RenameTy bottom_text 0 []
    , TForAll $ TFun (TBound 0) $ TFun (RenameTTy not_code [TBound 0]) $ RenameTTy bottom_code []
    )
  )
  
elim_bottom :: Term
elim_bottom =
  (
    (BLam "a" $ Lam (RenameTy bottom_text 0 [], RenameTTy bottom_code []) $ Bound 0 :!: (B "a", TBound 0)) :::
    (
      ForAll "a" $ Fun (RenameTy bottom_text 0 []) $ B "a"
    , TForAll $ TFun (RenameTTy bottom_code []) $ TBound 0
    )
  )
