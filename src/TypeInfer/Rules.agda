module TypeInfer.Rules where

open import Data.Nat
open import Data.Fin

open import TypeInfer.Data.Context as Cx
open import TypeInfer.Data.Type as Ty hiding (_!_)
open import TypeInfer.Data.Expr as Ex


data _⊢_≤_ {n m} (Γ : Context n m) : Type n → Type n → Set where
  ≤-1 : Γ ⊢ 1T ≤ 1T
  ≤-var : ∀ x → Γ ⊢ varT x ≤ varT x

  ≤-=> : ∀ {t s u v} →
    Γ ⊢ t ≤ s →
    Γ ⊢ u ≤ v →
    ------------
    Γ ⊢ (s => u) ≤ (t => v)

  ≤-∀ˡ : ∀ {t s} y →
    Γ ⊢ inst t y ≤ s →
    ------------
    Γ ⊢ ∀T t ≤ s

  ≤-∀ʳ : ∀ {t s} →
    (Γ ,*) ⊢ (↑ t) ≤ s →
    ------------
    Γ ⊢ t ≤ ∀T s



-- a ⊢ t(b)[b/a] ≤ t(a)
-- ---------------
-- a ⊢ ∀b.t(b) ≤ t(a)
-- ---------------
-- ⊢ ∀b.t(b) ≤ ∀a.t(a)

-- ⊢ (∀a. a) ≤ (∀b. (b => b))
≤-eg₁ : [] ⊢ ∀T 0V ≤ ∀T (0V => 0V)
≤-eg₁ = ≤-∀ʳ (≤-∀ˡ (0V => 0V) (≤-=> (≤-var 0F) (≤-var 0F)))

≤-refl : ∀ {n m} {Γ : Context n m} {t : Type n} → Γ ⊢ t ≤ t
≤-refl {t = 1T}     = ≤-1
≤-refl {t = varT x} = ≤-var x
≤-refl {t = t => u} = ≤-=> ≤-refl ≤-refl
≤-refl {t = ∀T t}   = ≤-∀ʳ (≤-∀ˡ 0V {!!})


data _⊢_⇒_ {n m} (Γ : Context n m) : Expr n m → Type n → Set
data _⊢_⇐_ {n m} (Γ : Context n m) : Expr n m → Type n → Set

data _⊢_⇒_ Γ where
  ⊢⇒1 : Γ ⊢ uE ⇒ 1T
  ⊢⇒var : ∀ x → Γ ⊢ varE x ⇒ (Γ ! x)

data _⊢_⇐_ Γ where
  ⊢⇐≤ : ∀ {e t s} →
    Γ ⊢ e ⇒ t →
    Γ ⊢ t ≤ s →
    ------------
    Γ ⊢ e ⇐ s

⊢⇐1 : ∀ {n m} {Γ : Context n m} → Γ ⊢ uE ⇐ 1T
⊢⇐1 = ⊢⇐≤ ⊢⇒1 ≤-1
