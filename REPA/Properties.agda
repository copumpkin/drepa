module REPA.Properties where

open import REPA
open import REPA.Shape
open import REPA.Index
open import REPA.Selector

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties

backpermute-fusion : ∀ {x y z} {sh₁ : Shape x} {sh₂ : Shape y} {sh₃ : Shape z}
                   → (f : Index sh₁ → Index sh₂) (g : Index sh₂ → Index sh₃)
                   → ∀ {A} (xs : Array sh₃ A) 
                   → backpermute f (backpermute g xs) ≡ backpermute (g ∘ f) xs
backpermute-fusion f g xs = {!!}

backpermute-inverse : ∀ {n m} {sh₁ : Shape n} {sh₂ : Shape m} 
                    → (f : Index sh₁ → Index sh₂) (g : Index sh₂ → Index sh₁)
                    → (pf₁ : ∀ i → g (f i) ≡ i) (pf₂ : ∀ i → f (g i) ≡ i)
                    → ∀ {A} (xs : Array sh₁ A) 
                    → backpermute f (backpermute g xs) ≡ xs
backpermute-inverse = {!!}
