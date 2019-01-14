module Fin where

open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable

data Fin : ℕ → Set where
  zero : ∀{n} → Fin n
  suc  : ∀{n} → Fin n → Fin (suc n)

_≟_ : ∀{n} → Decidable≡ (Fin n)
zero  ≟ zero  = yes refl
zero  ≟ suc y = no (λ ())
suc x ≟ zero  = no (λ ())
suc x ≟ suc y with x ≟ y
...             | yes refl = yes refl
...             | no x≢y   = no sx≢sy
  where
    sx≢sy : suc x ≢ suc y
    sx≢sy refl = x≢y refl
