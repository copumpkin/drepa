module REPA.Shape where

open import Data.Nat
open import Data.Vec using (Vec; lookup; allFin; zipWith; []; _∷_; map; tabulate)

open import Relation.Binary.PropositionalEquality

infixl 5 _∷_

data Shape : ℕ → Set where
  Z   : Shape 1
  _∷_ : ∀ {n} → (ss : Shape n) → (s : ℕ) → Shape (s * n)

-- Convert a shape to a type of nested vectors
NestVec : ∀ {n} → Shape n → Set → Set
NestVec Z A = A
NestVec (ss ∷ s) A = Vec (NestVec ss A) s

data ¬Empty : ∀ {n} → Shape n → Set where
  Z   : ¬Empty Z
  _∷_[_] : ∀ {n} {sh : Shape n} → (¬E : ¬Empty sh) → ∀ m → (m≢0 : m ≢ 0) → ¬Empty (sh ∷ m)

¬Empty→n≢0 : ∀ {n} {sh : Shape n} → ¬Empty sh → n ≢ 0
¬Empty→n≢0 Z ()
¬Empty→n≢0 (_∷_[_] {n} ¬E m m≢0) m*n≡0 = lemma m n m≢0 (¬Empty→n≢0 ¬E) m*n≡0
  where
  lemma : ∀ x y → x ≢ 0 → y ≢ 0 → x * y ≢ 0
  lemma zero y x≢0 y≢0 x*y≡0 = x≢0 refl
  lemma (suc x) zero x≢0 y≢0 x*y≡0 = y≢0 refl
  lemma (suc x) (suc y) x≢0 y≢0 ()

n≢0→¬Empty : ∀ {n} (sh : Shape n) → n ≢ 0 → ¬Empty sh
n≢0→¬Empty Z _ = Z
n≢0→¬Empty (_∷_ {n} ss s) n≢0 = n≢0→¬Empty ss (lemma₁ s n n≢0) ∷ s [ lemma₂ s n n≢0 ]
  where
  lemma₁ : ∀ x y → x * y ≢ 0 → y ≢ 0
  lemma₁ zero y x*y≢0 y≡0 = x*y≢0 refl
  lemma₁ (suc x) zero x*y≢0 y≡0 = lemma₁ x zero x*y≢0 refl
  lemma₁ (suc x) (suc y) x*y≢0 ()

  lemma₂ : ∀ x y → x * y ≢ 0 → x ≢ 0
  lemma₂ zero y x*y≢0 x≡0 = x*y≢0 refl
  lemma₂ (suc x) y x*y≢0 ()
