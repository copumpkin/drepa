{-# OPTIONS --universe-polymorphism #-}
module REPA where

import Level

open import REPA.Shape
open import REPA.Index
open import REPA.Selector

open import Function
open import Function.Bijection using (Bijection)

open import Data.Empty
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; zero; suc)
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Props using (bounded; toℕ-fromℕ≤)
open import Data.Vec using (Vec; foldl; foldl₁; lookup; allFin; zipWith; []; _∷_; map; tabulate)

open import Relation.Nullary
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
import Relation.Binary.EqReasoning as EqReasoning

open import Algebra.Structures
open import Algebra

record Array {n} (sh : Shape n) {a} (A : Set a) : Set a where
  constructor arr
  field
    vec : Vec A n

index : ∀ {n} {sh : Shape n} {a} {A : Set a} → Array sh A → Index sh → A
index (arr xs) i = lookup (flatten i) xs

open IsCommutativeSemiring isCommutativeSemiring hiding (sym; zero; refl)

product≡1-lemma : ∀ x y → x * y ≡ 1 → x ≡ 1 × y ≡ 1
product≡1-lemma zero y ()
product≡1-lemma (suc zero) y x*y≡1 rewrite proj₂ +-identity y = refl , x*y≡1
product≡1-lemma x zero x*y≡1 rewrite *-comm x 0 with x*y≡1
...                                             | ()
product≡1-lemma x (suc zero) x*y≡1 rewrite proj₂ *-identity x = x*y≡1 , refl
product≡1-lemma (suc (suc x)) (suc (suc y)) ()

singleton : ∀ {sh : Shape 1} {a} {A : Set a} → A → Array sh A
singleton = singleton-helper refl
  where
  singleton-helper : ∀ {n} {sh : Shape n} {a} {A : Set a} → n ≡ 1 → A → Array sh A
  singleton-helper {sh = Z} n≡1 x = arr (x ∷ [])
  singleton-helper {sh = _∷_ {n} ss s} n≡1 x with product≡1-lemma s n n≡1 
  singleton-helper {sh = _∷_ {.1} ss .1} n≡1 x | refl , refl = arr (x ∷ [])

toScalar : ∀ {sh : Shape 1} {a} {A : Set a} → Array sh A → A
toScalar = toScalar-helper refl
  where
  toScalar-helper : ∀ {n} {sh : Shape n} {a} {A : Set a} → n ≡ 1 → Array sh A → A
  toScalar-helper {sh = Z} n≡1 xs = index xs Z
  toScalar-helper {sh = _∷_ {n} ss s} n≡1 xs with product≡1-lemma s n n≡1 
  toScalar-helper {.(1 * 1)} {ss ∷ .1} n≡1 (arr (x ∷ xs)) | refl , refl = x

fromFunction : ∀ {n} {sh : Shape n} {a} {A : Set a} → (Index sh → A) → Array sh A
fromFunction f = arr (tabulate (f ∘ unflatten))

-- TODO: generalize to n-ary
traverse : ∀ {n m} {sh : Shape n} {sh' : Shape m} {a b} {A : Set a} {B : Set b} → Array sh A → ((Index sh → A) → Index sh' → B) → Array sh' B
traverse xs if = fromFunction (if (index xs))

backpermute : ∀ {n m} {sh : Shape n} {a} {A : Set a} {sh' : Shape m} → (Index sh' → Index sh) → Array sh A → Array sh' A
backpermute f xs = traverse xs (λ if i → if (f i))

reshape : ∀ {n} {sh sh' : Shape n} {a} {A : Set a} → Array sh A → Array sh' A
reshape xs = fromFunction (index xs ∘ unflatten ∘ flatten)

-- extend : ∀ {n m} {sh : Shape n} {sh' : Shape m} {A} → Selector sh' sh → Array sh A → Array sh' A
-- extend sel xs = {!!}

select : ∀ {n m} {sh : Shape n} {sh' : Shape m} {a} {A : Set a} → Selector sh sh' → Array sh A → Array sh' A
select sel xs = backpermute (apply sel) xs 

slice : ∀ {n x} {sh : Shape n} {a} {A : Set a} → Array (sh ∷ x) A → Fin x → Array sh A
slice xs i = select (all ∷′ i) xs

-- append : ∀ {n x y} {sh : Shape n} {A} → Array (sh ∷ x) A → Array (sh ∷ y) A → Array (sh ∷ x + y) A
-- append xs ys = {!!}

transpose : ∀ {n x y} {sh : Shape n} {a} {A : Set a} → Array (sh ∷ x ∷ y) A → Array (sh ∷ y ∷ x) A
transpose {_} {x} {y} {sh} {_} {A} xs = traverse xs helper
  where
  helper : (Index (sh ∷ x ∷ y) → A) → Index (sh ∷ y ∷ x) → A
  helper f (is ∷ i ∷ i') = f (is ∷ i' ∷ i)

toNestVec : ∀ {n} {sh : Shape n} {a} {A : Set a} → Array sh A → NestVec sh A
toNestVec {sh = Z} xs = index xs Z
toNestVec {sh = ss ∷ s} xs = map (toNestVec ∘ slice xs) (allFin _)

fold₁ : ∀ {a b} (S : Semigroup a b) → ∀ {m n} {sh : Shape n} → Array (sh ∷ suc m) (Semigroup.Carrier S) → Array sh (Semigroup.Carrier S)
fold₁ S {m} xs = fromFunction (λ ix → foldl₁ _∙_ (map (λ i → index xs (ix ∷ i)) (allFin (suc m))))
  where open Semigroup S

fold : ∀ {a b} (M : Monoid a b) → ∀ {m n} {sh : Shape n} → Array (sh ∷ m) (Monoid.Carrier M) → Array sh (Monoid.Carrier M)
fold M {m} xs = fromFunction (λ ix → foldl (const Carrier) _∙_ ε (map (λ i → index xs (ix ∷ i)) (allFin m)))
  where open Monoid M

foldAll : ∀ {a b} (M : CommutativeMonoid a b) → ∀ {n} {sh : Shape n} → Array sh (CommutativeMonoid.Carrier M) → CommutativeMonoid.Carrier M
foldAll M {n} xs = foldl (const Carrier) _∙_ ε (map (λ i → index xs (unflatten i)) (allFin n))
  where open CommutativeMonoid M
