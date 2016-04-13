module lexicographic where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; inspect)

record well-order : Set1 where
  field
    S    : Set
    _≺_  : S → S → Set
    reflx : (x : S) → x ≺ x
    ansym : (x y : S) → x ≺ y → y ≺ x → x ≡ y
    trans : (x y z : S) → x ≺ y → y ≺ z → x ≺ z

open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Bool

_<=B_ : ℕ → ℕ → Bool
zero  <=B _     = true
suc x <=B zero  = false
suc x <=B suc y = x <=B y

_<=_ : List ℕ → List ℕ → Set
[] <= [] = ⊤
[] <= (x ∷ xs) = ⊤
(x ∷ xs) <= [] = ⊥
(x ∷ xs) <= (y ∷ ys) with x <=B y
(x ∷ xs) <= (y ∷ ys) | true = xs <= ys
(x ∷ xs) <= (y ∷ ys) | false = ⊥

lemma1 : (x : List ℕ) → x <= x
lemma1 [] = tt
lemma1 (x ∷ xs) with x <=B x
lemma1 (x ∷ xs) | true  = lemma1 xs
lemma1 (x ∷ xs) | false = {!!}

lemma2 : (x y : List ℕ) → x <= y → y <= x → x ≡ y
lemma2 x y prf1 prf2 = {!!}


--lexicographicℕ : ℕ → well-order
lexicographicℕ : well-order
lexicographicℕ = record { S = List ℕ ; _≺_ = _<=_ ; reflx = lemma1 ; ansym = lemma2 ; trans = {!!} }

-- Ctr-u Ctr-c Ctr-,
