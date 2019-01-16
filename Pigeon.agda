module Pigeon where

open import Decidable
open import Fin
open import Func
open import Nat

slice : ∀{n m} → (f : Fin (suc n) → Fin (suc m)) → ¬(SingPoint f zero) → Fin n → Fin m
slice f ¬zeroSing x with compare (f (suc x)) (f zero)
slice f ¬zeroSing x | less fsx≺f0 = proj (f (suc x)) (projdrop fsx≺f0)
slice f ¬zeroSing x | more f0≺fsx = prec (f (suc x)) (≼trans (sx≼sy (0≼x′)) f0≺fsx)
slice f ¬zeroSing x | same fsx≈f0 = ⊥-elim (¬zeroSing zeroSing)
  where
    zeroSing : SingPoint f zero
    zeroSing = singpoint (suc x) (λ ()) (≈to≡ (≈sym fsx≈f0))


liftSliceSing : ∀{n m} {f : Fin (suc n) → Fin (suc m)}
                → (¬zeroSing : ¬(SingPoint f zero))
                → Singular (slice f ¬zeroSing) → Singular f
liftSliceSing = ?


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
pigeon {suc n} {zero}  (sn≤sm m<n) f = ⊥-elim (¬FinZero (f zero))
pigeon {suc n} {suc m} (sn≤sm m<n) f with isZeroSingular f
... | yes zeroSing = zero , zeroSing
... | no ¬zeroSing = liftSliceSing ¬zeroSing (pigeon m<n (slice f ¬zeroSing))
