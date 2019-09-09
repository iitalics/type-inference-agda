module TypeInfer.Data.Context where

--open import Function
open import Data.Nat as Nat
open import Data.Fin as Fin
--open import Relation.Nullary using (yes; no)

open import TypeInfer.Data.Type as Type using (Type)

private
  variable
    n m k : ℕ

--
-- Contexts
--

data Context : ℕ → ℕ → Set where
  []  : Context 0 0
  _,* : (Γ : Context n m) → Context (suc n) m
  _,_ : (Γ : Context n m) (t : Type n) → Context n (suc m)

--
-- Looking up variables in a context
--

_!_ : Context n m → Fin m → Type n
(Γ ,*)  ! x     = Type.↑ (Γ ! x)
(Γ , t) ! 0F    = t
(Γ , _) ! suc x = Γ ! x
