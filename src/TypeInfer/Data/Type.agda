module TypeInfer.Data.Type where

open import Function
open import Data.Nat as Nat
open import Data.Fin as Fin
open import Relation.Nullary using (yes; no)

private
  variable
    n m k : ℕ

infixr 6 _=>_

--
-- Types, subtitutions
--

data Type n : Set where
  1T   : Type n
  varT : (x : Fin n) → Type n
  ∀T   : (t : Type (suc n)) → Type n
  _=>_ : (t1 t2 : Type n) → Type n

data Sub : ℕ → ℕ → Set where
  [_:=_] : (x : Fin (suc n)) (t : Type n) → Sub (suc n) n

pattern 0V = varT 0F
pattern 1V = varT 1F
pattern 2V = varT 2F

--
-- Weakening
--

weaken : Fin (suc n) → Type n → Type (suc n)
weaken x 1T       = 1T
weaken x (varT y) = varT (punchIn x y)
weaken x (∀T t)   = ∀T (weaken (suc x) t)
weaken x (t => u) = weaken x t => weaken x u

↑ : Type n → Type (suc n)
↑ = weaken 0F

sub↑ : Sub n m → Sub (suc n) (suc m)
sub↑ [ x := t ] = [ suc x := ↑ t ]

--
-- Applying substitutions
--

_!_ : Sub n m → Fin n → Type m
[ x := t ] ! y with x Fin.≟ y
... | yes eq = t
... | no neq = varT (punchOut neq)

_/_ : Type n → Sub n m → Type m
1T       / σ = 1T
varT x   / σ = σ ! x
∀T t     / σ = ∀T (t / sub↑ σ)
(t => u) / σ = (t / σ) => (u / σ)

inst : Type (suc n) → Type n → Type n
inst t v = t / [ 0F := v ]
