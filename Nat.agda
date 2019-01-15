open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_) public

data _≤_ : ℕ → ℕ → Set where
  0≤n    : ∀{n} → zero ≤ n
  sn≤sm : ∀{n m} → n ≤ m → (suc n) ≤ (suc m)

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

weaken< : ∀{n m} → n < m → n ≤ m
weaken< (sn≤sm 0≤n)       = 0≤n
weaken< (sn≤sm (sn≤sm x)) = sn≤sm (weaken< (sn≤sm x))
