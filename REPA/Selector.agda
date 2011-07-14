module REPA.Selector where

open import REPA.Shape
open import REPA.Index

open import Data.Nat
open import Data.Fin
open import Data.Vec

-- Still undecided
data Selector : ∀ {n m} → Shape n → Shape m → Set where
  Z    : Selector Z Z
  _∷′_ : ∀ {p q n} {sh : Shape p} {sh' : Shape q} → (ss : Selector sh sh') → (i : Fin n) → Selector (sh ∷ n) sh'
  _∷_  : ∀ {p q m n} {sh : Shape p} {sh' : Shape q} → (ss : Selector sh sh') → (s : Vec (Fin n) m) → Selector (sh ∷ n) (sh' ∷ m)
  

all : ∀ {n} {sh : Shape n} → Selector sh sh
all {sh = Z} = Z
all {sh = ss ∷ s} = all ∷ allFin s

apply : ∀ {n m} {sh : Shape n} {sh' : Shape m} → Selector sh sh' → Index sh' → Index sh
apply Z Z = Z
apply (ss ∷′ x) is = apply ss is ∷ x
apply (ss ∷ s) (is ∷ i) = apply ss is ∷ lookup i s
