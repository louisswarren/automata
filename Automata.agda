module Automata where

open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable
open import Fin
open import List

record Dfa (Σ : Set) : Set where
  field
    n : ℕ
    δ : Fin n → Σ → Fin n
    F : List (Fin n)

  δ* : Fin n → List Σ → Fin n
  δ* q [] = q
  δ* q (x ∷ xs) = δ* (δ q x) xs

  Accepts : List Σ → Set
  Accepts xs = δ* zero xs ∈ F

  accepts : (xs : List Σ) → Dec (Accepts xs)
  accepts xs = decide∈ _≟_ (δ* zero xs) F
