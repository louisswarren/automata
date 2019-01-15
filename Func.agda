module Func where

open import Agda.Builtin.Sigma public

open import Decidable

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

record SingPoint {A B : Set} (f : A → B) (x : A) : Set where
  constructor singpoint
  field
    y    : A
    sep  : x ≢ y
    sing : f x ≡ f y

Singular : {A B : Set} → (f : A → B) → Set
Singular f = Σ _ (SingPoint f)
