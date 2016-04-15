module lexicographic where

open import Data.Nat

open import Data.List
open import Relation.Binary.PropositionalEquality --using (_≡_ ; refl ; inspect)

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

-- changed following definition from function to data-type.
data _<=_ : List ℕ → List ℕ → Set where
  0≤0   : [] <= []
  0≤xs  : {x : ℕ} {xs : List ℕ} → [] <= (x ∷ xs)
  xs≤ys : {x y : ℕ} {xs ys : List ℕ} → xs <= ys → x ≤′ y → (x ∷ xs) <= (y ∷ ys) -- ≤′ is useful 

lemma1 : (xs : List ℕ) → xs <= xs
lemma1 [] = 0≤0
lemma1 (x ∷ xs)  = xs≤ys (lemma1 xs) ≤′-refl
-- using ≤′, this proof is EXTREMELY easy!

lemma2 : (x y : List ℕ) → x <= y → y <= x → x ≡ y
lemma2 [] [] 0≤0 0≤0 = refl
lemma2 [] ._ 0≤xs ()
lemma2 (x ∷ xs) (y ∷ ys) (xs≤ys prf1 t) (xs≤ys prf2 u) = {!!}

lemma3 : (x y z : List ℕ) → x <= y → y <= z → x <= z
lemma3 []       _        []       prf1 prf2 = 0≤0
lemma3 []       _        (z ∷ zs) prf1 prf2 = 0≤xs
lemma3 (x ∷ xs) []       []       prf1 prf2 = {!!}
lemma3 (x ∷ xs) []       (z ∷ zs) prf1 prf2 = {!!}
lemma3 (x ∷ xs) (y ∷ ys) []       prf1 prf2 = {!!}
lemma3 (x ∷ xs) (y ∷ ys) (z ∷ zs) prf1 prf2 = {!!}

--lexicographicℕ : ℕ → well-order
lexicographicℕ : well-order
lexicographicℕ = record { S = List ℕ ; _≺_ = _<=_ ; w-refl = lemma1 ; w-antisym = lemma2 ; w-trans = lemma3 }

-- Ctr-u Ctr-c Ctr-,
