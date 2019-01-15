module Pigeon where

open import Decidable
open import Fin
open import Func
open import Nat

isZeroSingular : ∀{n m} → (f : Fin (suc n) → Fin m) → Dec (SingPoint f zero)
isZeroSingular {zero} f = no ¬trivSing
  where
    ¬trivSing : ¬(SingPoint f zero)
    ¬trivSing (singpoint zero sep sing) = sep refl
    ¬trivSing (singpoint (suc ()) sep sing)
isZeroSingular {suc n} f with searchFin (f zero ≟_) λ x → f (suc x)
isZeroSingular {suc n} f | yes (y , f0≡fy) = yes (singpoint (suc y) (λ ()) f0≡fy)
isZeroSingular {suc n} f | no  notFound    = no ¬zeroSing
  where
    ¬zeroSing : ¬(SingPoint f zero)
    ¬zeroSing (singpoint zero sep sing)    = sep refl
    ¬zeroSing (singpoint (suc y) sep sing) = notFound (y , sing)

pigeon : ∀{n m} → m < n → (f : Fin n → Fin m) → Singular f
pigeon {zero} {m} () f
pigeon {suc n} {zero} m<n f with f zero
pigeon {suc n} {zero} m<n f | ()
pigeon {suc n} {suc m} m<n f with isZeroSingular f
...                          | yes zeroSing = zero , zeroSing
...                          | no ¬zeroSing = {!   !}
