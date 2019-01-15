module Fin where

open import Decidable
open import Func
open import Nat

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (suc n)
  suc  : ∀{n} → Fin n       → Fin (suc n)

¬FinZero : ¬(Fin zero)
¬FinZero ()

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

data _≼_ : ∀{n m} → Fin n → Fin m → Set where
  0≼x   : ∀{n m} {x : Fin m}                     → zero {n} ≼ x
  sx≼sy : ∀{n m} {x : Fin n} {y : Fin m} → x ≼ y → suc x    ≼ suc y

_≺_ : ∀{n m} → Fin n → Fin m → Set
x ≺ y = suc x ≼ y

_≈_ : ∀{n m} → Fin n → Fin m → Set
x ≈ y = (x ≼ y) × (y ≼ x)

toℕ : ∀{n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)

toℕ< : ∀{n} → (x : Fin n) → toℕ x < n
toℕ< {zero} ()
toℕ< {suc n} zero = sn≤sm 0≤n
toℕ< {suc n} (suc x) = sn≤sm (toℕ< x)

proj : ∀{k n} → (x : Fin n) → toℕ x < k → Fin k
proj zero    (sn≤sm lt) = zero
proj (suc x) (sn≤sm lt) = suc (proj x lt)

proj≈ : ∀{k n} → (x : Fin n) → (lt : toℕ x < k) → x ≈ proj x lt
proj≈ {zero} x ()
proj≈ {suc k} zero    (sn≤sm lt) = 0≼x , 0≼x
proj≈ {suc k} (suc x) (sn≤sm lt) with proj≈ x lt
proj≈ {suc k} (suc x) (sn≤sm lt) | x≼y , y≼x = sx≼sy x≼y , sx≼sy y≼x

prec : ∀{n m} → (x : Fin (suc n)) → zero {m} ≺ x → Fin n
prec (suc y) (sx≼sy _) = y

precinv : ∀{n m} → (x : Fin (suc n)) → (nz : zero {m} ≺ x) → suc (prec x nz) ≡ x
precinv (suc x) (sx≼sy nz) = refl


data Compare : ∀{n m} → Fin n → Fin m → Set where
  less : ∀{n m} {x : Fin n} {y : Fin m} → x ≺ y → Compare x y
  same : ∀{n m} {x : Fin n} {y : Fin m} → x ≈ y → Compare x y
  more : ∀{n m} {x : Fin n} {y : Fin m} → y ≺ x → Compare x y

compare : ∀{n m} → (x : Fin n) → (y : Fin m) → Compare x y
compare zero    zero    = same (0≼x , 0≼x)
compare zero    (suc y) = less (sx≼sy 0≼x)
compare (suc x) zero    = more (sx≼sy 0≼x)
compare (suc x) (suc y) with compare x y
compare (suc x) (suc y) | less x≺y         = less (sx≼sy x≺y)
compare (suc x) (suc y) | same (x≼y , y≼x) = same (sx≼sy x≼y , sx≼sy y≼x)
compare (suc x) (suc y) | more y≺x         = more (sx≼sy y≺x)


searchFin : ∀{n} {A : Set} {P : A → Set} → Decidable P → (f : Fin n → A) → Dec (Σ _ λ x → P (f x))
searchFin {zero}  p f = no λ x → ¬FinZero (fst x)
searchFin {suc n} p f with p (f zero)
searchFin {suc n} p f | yes Pf0 = yes (zero , Pf0)
searchFin {suc n} p f | no ¬Pf0 with searchFin p (λ x → f (suc x))
searchFin {suc n} p f | no ¬Pf0 | yes (x , Pfx) = yes (suc x , Pfx)
searchFin {suc n} p f | no ¬Pf0 | no ¬Pfs       = no ¬Pf
  where
    ¬Pf : _
    ¬Pf (zero  , Pf0) = ¬Pf0 Pf0
    ¬Pf (suc x , Pfs) = ¬Pfs (x , Pfs)
