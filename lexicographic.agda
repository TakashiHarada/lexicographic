module lexicographic where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

record well-order : Set1 where
  field
    S    : Set
    _≺_  : S → S → Set
    reflx : (x : S) → x ≺ x
    ansym : (x y : S) → x ≺ y → y ≺ x → x ≡ y
    trans : (x y z : S) → x ≺ y → y ≺ z → x ≺ z

open import Data.Unit using (⊤ ; tt)
open import Data.Empty

_<=_ : List ℕ → List ℕ → Set
[] <= y = ⊤
(x ∷ xs) <= [] = ⊥
(x ∷ xs) <= (y ∷ ys) with compare x y
(x ∷ xs) <= (.(suc (x + k)) ∷ ys) | less .x k = ⊤
(x ∷ xs) <= (.x ∷ ys) | equal .x = xs <= ys
(.(suc (y + k)) ∷ xs) <= (y ∷ ys) | greater .y k = ⊥

lemma1 : (x : List ℕ) → x <= x
lemma1 [] = tt
lemma1 (x ∷ xs) = lemma1 {!!}


lemma2 : (x y : List ℕ) → x <= y → y <= x → x ≡ y
lemma2 [] [] prf1 prf2 = refl
lemma2 [] (y ∷ ys) prf1 ()
lemma2 (x ∷ xs) [] () prf2
lemma2 (x ∷ []) (y ∷ []) prf1 prf2 = {!!}
lemma2 (x ∷ []) (y ∷ x₁ ∷ ys) prf1 prf2 = {!!}
lemma2 (x ∷ x₁ ∷ xs) (y ∷ []) prf1 prf2 = {!!}
lemma2 (x ∷ x₁ ∷ xs) (y ∷ x₂ ∷ ys) prf1 prf2 = {!!}
-- Ctr-u Ctr-c Ctr-,

--lexicographicℕ : ℕ → well-order
lexicographicℕ : well-order
lexicographicℕ = record { S = List ℕ ; _≺_ = _<=_ ; reflx = lemma1 ; ansym = lemma2 ; trans = {!!} }
