{-# OPTIONS --universe-polymorphism #-}
module REPA.Properties where

open import REPA
open import REPA.Shape
open import REPA.Index
open import REPA.Selector

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties

tabulate-lemma : ∀ {n} {a} {A : Set a} → (f g : Fin n → A) → (∀ i → f i ≡ g i) → tabulate f ≡ tabulate g
tabulate-lemma {zero} f g pf = refl
tabulate-lemma {suc n} f g pf = cong₂ _∷_ (pf zero) (tabulate-lemma (f ∘ suc) (g ∘ suc) (pf ∘ suc))

fromFunction-lemma : ∀ {n} {sh : Shape n} {a} {A : Set a} → (f g : Index sh → A) → (∀ i → f i ≡ g i) → fromFunction f ≡ fromFunction g
fromFunction-lemma f g pf = cong arr (tabulate-lemma (f ∘ unflatten ) (g ∘ unflatten) (pf ∘ unflatten))

tabulate-lookup′ : ∀ {n} {a} {A : Set a} (f : Fin n → A) (xs : Vec A n) (f-id : ∀ i → f i ≡ lookup i xs) → tabulate f ≡ xs
tabulate-lookup′ f [] f-id = refl
tabulate-lookup′ f (x ∷ xs) f-id rewrite f-id zero = cong (_∷_ x) (tabulate-lookup′ (f ∘ suc) xs (f-id ∘ suc))

tabulate-lookup : ∀ {n} {a} {A : Set a} {f : Fin n → Fin n} (f-id : ∀ x → f x ≡ x) (xs : Vec A n) → tabulate (λ i → lookup (f i) xs) ≡ xs
tabulate-lookup {f = f} f-id xs = tabulate-lookup′ (λ z → lookup (f z) xs) xs (cong (λ q → lookup q xs) ∘ f-id)

index-fromFunction : ∀ {n} {sh : Shape n} {a} {A : Set a} → (f : Index sh → A) → (i : Index sh) → index (fromFunction f) i ≡ f i
index-fromFunction f i with lookup∘tabulate (f ∘ unflatten) (flatten i)
index-fromFunction f i | q rewrite unflatten∘flatten≡id i = q

fromFunction-index : ∀ {n} {sh : Shape n} {a} {A : Set a} {f : Index sh → Index sh} (f-id : ∀ x → f x ≡ x) (xs : Array sh A) → fromFunction (index xs ∘ f) ≡ xs
fromFunction-index {n} {f = f} f-id (arr xs) = cong arr (tabulate-lookup {f = flatten ∘ f ∘ unflatten} lemma xs)
  where
  lemma : (x : Fin n) → fromℕ≤ (flatten′-fits (f (unflatten x))) ≡ x
  lemma x rewrite f-id (unflatten x) = flatten∘unflatten≡id x

traverse-id : ∀ {n} {sh : Shape n} {a} {A : Set a} (xs : Array sh A) → traverse xs id ≡ xs
traverse-id xs = fromFunction-index (λ _ → refl) xs

traverse-prefusion : ∀ {x y z} {sh₁ : Shape x} {sh₂ : Shape y} {sh₃ : Shape z}
                → (f : Index sh₁ → Index sh₂) (g : Index sh₂ → Index sh₃)
                → ∀ {a} {A : Set a} (xs : Array sh₃ A) 
                → traverse (traverse xs (pre g)) (pre f) ≡ traverse xs (pre (g ∘ f))
traverse-prefusion f g xs = fromFunction-lemma (index (traverse xs (pre g)) ∘ f) (index xs ∘ g ∘ f) lemma
  where
  lemma : ∀ i → index (backpermute g xs) (f i) ≡ index xs (g (f i))
  lemma i = trans (index-fromFunction (index xs ∘ g) (f i)) refl

backpermute-id : ∀ {n} {sh : Shape n} {a} {A : Set a} (xs : Array sh A) → backpermute id xs ≡ xs
backpermute-id = traverse-id

backpermute-fusion : ∀ {x y z} {sh₁ : Shape x} {sh₂ : Shape y} {sh₃ : Shape z}
                   → (f : Index sh₁ → Index sh₂) (g : Index sh₂ → Index sh₃)
                   → ∀ {a} {A : Set a} (xs : Array sh₃ A) 
                   → backpermute f (backpermute g xs) ≡ backpermute (g ∘ f) xs
backpermute-fusion = traverse-prefusion


backpermute-inverse : ∀ {n m} {sh₁ : Shape n} {sh₂ : Shape m} 
                    → (f : Index sh₁ → Index sh₂) (g : Index sh₂ → Index sh₁)
                    → (pf₁ : ∀ i → g (f i) ≡ i)
                    → ∀ {a} {A : Set a} (xs : Array sh₁ A) 
                    → backpermute f (backpermute g xs) ≡ xs
backpermute-inverse f g pf₁ xs = trans (backpermute-fusion f g xs) (fromFunction-index pf₁ xs)
