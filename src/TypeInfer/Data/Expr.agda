module TypeInfer.Data.Expr where

open import Data.Nat
open import Data.Fin
open import TypeInfer.Data.Type

data Expr n m : Set where
  varE : (x : Fin m) → Expr n m
  annE : (e : Expr n m) (t : Type n) → Expr n m
  lamE : (b : Expr n (suc m)) → Expr n m
  uE   : Expr n m
  _∙_  : (f e : Expr n m) → Expr n m
