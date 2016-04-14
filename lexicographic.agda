module lexicographic where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

record well-order : Set1 where
  field
    S    : Set
    _≺_  : S → S → Set
    w-refl : (x : S) → x ≺ x
    w-antisym : (x y : S) → x ≺ y → y ≺ x → x ≡ y
    w-trans : (x y z : S) → x ≺ y → y ≺ z → x ≺ z

open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Bool

data _<=_ : List ℕ → List ℕ → Set where
  0≤0  : [] <= []
  0≤xs : {x : ℕ} {xs : List ℕ} → [] <= (x ∷ xs)
  xs≤ys : {x y : ℕ}{xs ys : List ℕ} → xs <= ys → x ≤′ y → (x ∷ xs) <= (y ∷ ys) -- ≤′ is useful 

ℕList-refl : (xs : List ℕ) → xs <= xs
ℕList-refl [] = 0≤0
ℕList-refl (x ∷ xs)  = xs≤ys (ℕList-refl xs) ≤′-refl
-- using ≤′, this proof is EXTREMELY easy!

ℕList-antisym : (x y : List ℕ) → x <= y → y <= x → x ≡ y
ℕList-antisym .[] .[] 0≤0 0≤0 = refl
ℕList-antisym .[] ._ 0≤xs ()
ℕList-antisym (x ∷ xs) (y ∷ ys) (xs≤ys prf1 x≤'y) (xs≤ys prf2 y≤'x) = 
  cong₂ _∷_ (antisym-≤ (≤′-is-≤ x y x≤'y) (≤′-is-≤ y x y≤'x)) 
            (ℕList-antisym xs ys prf1 prf2) 
  where
    antisym-≤ : {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
    antisym-≤ z≤n z≤n = refl
    antisym-≤ (s≤s n≤m) (s≤s m≤n) rewrite antisym-≤ n≤m m≤n = refl
    
    ≤′-is-≤ : (x y : ℕ) → x ≤′ y → x ≤ y
    ≤′-is-≤ zero zero ≤′-refl = z≤n
    ≤′-is-≤ zero (suc n) _    = z≤n
    ≤′-is-≤ (suc x) zero ()
    ≤′-is-≤ (suc x) (suc .x) ≤′-refl      = s≤s (≤′-is-≤ x x ≤′-refl)
    ≤′-is-≤ (suc x) (suc y) (≤′-step prf) = s≤s (≤′-is-≤ x y (lemma prf))
     where
       lemma : {x y : ℕ} → suc x ≤′ y → x ≤′ y
       lemma ≤′-refl        = ≤′-step ≤′-refl
       lemma (≤′-step prf2) = ≤′-step (lemma prf2)

    -- omake
    {-
    antisym-≤′ : (x y : ℕ) → x ≤′ y → y ≤′ x → x ≡ y
    antisym-≤′ x .x ≤′-refl ≤′-refl = refl
    antisym-≤′ ._ ._ ≤′-refl (≤′-step _) = refl
    antisym-≤′ ._ ._ (≤′-step _) ≤′-refl = refl
    antisym-≤′ ._ ._ (≤′-step {y} sucx≤y) (≤′-step {x} sucy≤x) = {!!}
    -}

ℕList-trans : (xs ys zs : List ℕ) → xs <= ys → ys <= zs → xs <= zs
ℕList-trans [] [] [] 0≤0 0≤0 = 0≤0
ℕList-trans [] [] (z ∷ zs) 0≤0 0≤xs = 0≤xs
ℕList-trans [] (y ∷ ys) [] 0≤xs ()
ℕList-trans [] (y ∷ ys) (z ∷ zs) 0≤xs (xs≤ys _ _) = 0≤xs
ℕList-trans (x ∷ xs) [] [] () prf2
ℕList-trans (x ∷ xs) [] (x₁ ∷ zs) () prf2
ℕList-trans (x ∷ xs) (x₁ ∷ ys) [] (xs≤ys prf1 x₂) ()
ℕList-trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (xs≤ys xs<ys x≤y) (xs≤ys ys<zs y≤z) 
  = xs≤ys (ℕList-trans xs ys zs xs<ys ys<zs) 
          (trans-≤′ x y z x≤y y≤z)
  where
    trans-≤′ : (x y z : ℕ) → x ≤′ y → y ≤′ z → x ≤′ z
    trans-≤′ zero     zero     zero     ≤′-refl ≤′-refl       = ≤′-refl
    trans-≤′ zero     zero    (suc z)   ≤′-refl (≤′-step 0≤z) = ≤′-step 0≤z
    trans-≤′ zero    (suc y)   zero    (≤′-step _) ()
    trans-≤′ zero    (suc y)  (suc .y) (≤′-step 0≤y)  ≤′-refl         = ≤′-step 0≤y
    trans-≤′ zero    (suc y)  (suc z)  (≤′-step 0≤y) (≤′-step sucy≤z) 
      = ≤′-step (trans-≤′ zero (suc y) z (≤′-step 0≤y) sucy≤z)
    trans-≤′ (suc x)  zero     zero    () _
    trans-≤′ (suc x)  zero    (suc z)  () _
    trans-≤′ (suc x) (suc .x)  zero     ≤′-refl    ()
    trans-≤′ (suc x) (suc y)   zero    (≤′-step _) ()
    trans-≤′ (suc x) (suc .x) (suc .x)  ≤′-refl          ≤′-refl         = ≤′-refl
    trans-≤′ (suc x) (suc .x) (suc z)   ≤′-refl         (≤′-step sucx≤z) = ≤′-step sucx≤z
    trans-≤′ (suc x) (suc y)  (suc .y) (≤′-step sucx≤y)  ≤′-refl         = ≤′-step sucx≤y
    trans-≤′ (suc x) (suc y)  (suc z)  (≤′-step sucx≤y) (≤′-step sucy≤z) 
      = ≤′-step (trans-≤′ (suc x) (suc y) z (≤′-step sucx≤y) sucy≤z)

--lexicographicℕ : ℕ → well-order
lexicographicℕ : well-order
lexicographicℕ = 
  record { S = List ℕ ; 
           _≺_ = _<=_ ; 
           w-refl    = ℕList-refl ; 
           w-antisym = ℕList-antisym ; 
           w-trans   = ℕList-trans }

-- Ctr-u Ctr-c Ctr-,
