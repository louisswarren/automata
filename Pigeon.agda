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
... | no ¬zeroSing with pigeon m<n (slice f ¬zeroSing)
...                | x , singpoint y x≢y gx≡gy = sing
  where
    g : Fin n → Fin m
    g = slice f ¬zeroSing
    X : Fin (suc n)
    X = suc x
    Y : Fin (suc n)
    Y = suc y
    sucproj : ∀{k n} → (x : Fin n) → (lt : toℕ x < k) → suc (proj x lt) ≈ suc x
    sucproj x lt = ≈sym (≈suc (proj≈ x lt))
    sing : Singular f
    sing with compare (f X) (f zero) | compare (f Y) (f zero)
    ...  | less fX≺f0 | less fY≺f0 = X , singpoint Y (λ eq → x≢y (suc≡ eq)) (projinv≡ gx≡gy)
    ...  | more f0≺fX | more f0≺fY = X , singpoint Y (λ eq → x≢y (suc≡ eq)) (precinv≡ a b gx≡gy)
      where
        a : suc zero ≼ f (suc x)
        a = ≼trans (sx≼sy 0≼x′) f0≺fX
        b : suc zero ≼ f (suc y)
        b = ≼trans (sx≼sy 0≼x′) f0≺fY
    ...  | same fX≈f0 | _          = ⊥-elim (¬zeroSing (singpoint X (λ ()) (≈to≡ (≈sym fX≈f0))))
    ...  | _          | same fY≈f0 = ⊥-elim (¬zeroSing (singpoint Y (λ ()) (≈to≡ (≈sym fY≈f0))))
    ...  | less fX≺f0 | more f0≺fY = ⊥-elim (≺to≢ sprojfX≺fY sprojfX≡fY)
      where
        sprojfX≡fY : suc (proj (f (suc x)) (projdrop fX≺f0)) ≡ f (suc y)
        sprojfX≡fY = ≡trans (≡suc gx≡gy) (precinv (f Y) (≼trans (sx≼sy 0≼x′) f0≺fY))
        sprojfX≺fY : suc (proj (f (suc x)) (projdrop fX≺f0)) ≺ f (suc y)
        sprojfX≺fY = ≼trans (sx≼sy (fst (sucproj (f X) (projdrop fX≺f0)))) (≼trans (sx≼sy fX≺f0) f0≺fY)
    ...  | more f0≺fX | less fY≺f0 = ⊥-elim (≺to≢ sprojfY≺fX sprojfY≡fX)
      where
        sprojfY≡fX : suc (proj (f (suc y)) (projdrop fY≺f0)) ≡ f (suc x)
        sprojfY≡fX = ≡trans (≡suc (≡sym gx≡gy)) (precinv (f X) (≼trans (sx≼sy 0≼x′) f0≺fX))
        sprojfY≺fX : suc (proj (f (suc y)) (projdrop fY≺f0)) ≺ f (suc x)
        sprojfY≺fX = ≼trans (sx≼sy (fst (sucproj (f Y) (projdrop fY≺f0)))) (≼trans (sx≼sy fY≺f0) f0≺fX)
