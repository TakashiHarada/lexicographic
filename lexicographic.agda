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

_<=B_ : ℕ → ℕ → Bool
zero  <=B _     = true
suc x <=B zero  = false
suc x <=B suc y = x <=B y

-- changed following definition from function to data-type.
data _<=_ : List ℕ → List ℕ → Set where
  0≤0  : [] <= []
  0≤xs : {x : ℕ} {xs : List ℕ} → [] <= (x ∷ xs)
  xs≤ys : {x y : ℕ}{xs ys : List ℕ} → xs <= ys → x ≤′ y → (x ∷ xs) <= (y ∷ ys) -- ≤′ is useful 
{-
[] <= [] = ⊤
[] <= (x ∷ xs) = ⊤
(x ∷ xs) <= [] = ⊥
(x ∷ xs) <= (y ∷ ys) with x <=B y
(x ∷ xs) <= (y ∷ ys) | true = xs <= ys
(x ∷ xs) <= (y ∷ ys) | false = ⊥
-}
lemma1 : (xs : List ℕ) → xs <= xs
lemma1 [] = 0≤0
lemma1 (x ∷ xs)  = xs≤ys (lemma1 xs) ≤′-refl
-- using ≤′, this proof is EXTREMELY easy!

{-
lemma1 (x ∷ xs) with x <=B x | inspect (_<=B_ x) x
lemma1 (x ∷ xs) | true | _ = lemma1 xs
lemma1 (zero ∷ xs) | false | Reveal_·_is_.[ () ]
lemma1 (suc x ∷ xs) | false | Reveal_·_is_.[ eq ] = {!!}
-}

lemma2 : (x y : List ℕ) → x <= y → y <= x → x ≡ y
lemma2 x y prf1 prf2 = {!!}


--lexicographicℕ : ℕ → well-order
lexicographicℕ : well-order
lexicographicℕ = record { S = List ℕ ; _≺_ = _<=_ ; w-refl = lemma1 ; w-antisym = lemma2 ; w-trans = {!!} }

-- Ctr-u Ctr-c Ctr-,
