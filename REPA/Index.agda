module REPA.Index where

open import REPA.Shape

open import Function
open import Function.Bijection using (Bijection)

open import Data.Empty
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.Fin.Props using (bounded; toℕ-fromℕ≤)
open import Data.Vec using (Vec; lookup; allFin; zipWith; []; _∷_; map; tabulate)

open import Relation.Nullary
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
import Relation.Binary.EqReasoning as EqReasoning

open import Algebra.Structures

data Index : ∀ {n} → Shape n → Set where
  Z   : Index Z
  _∷_ : ∀ {m} {sh : Shape m} {n} → (is : Index sh) → (i : Fin n) → Index (sh ∷ n)

Index→¬Empty : ∀ {n} {sh : Shape n} → Index sh → ¬Empty sh
Index→¬Empty Z = Z
Index→¬Empty {sh = ss ∷ zero} (is ∷ ())
Index→¬Empty {sh = ss ∷ suc s} (is ∷ i) = Index→¬Empty is ∷ suc s [ absurd ]
  module Index→¬Empty where
  absurd : suc s ≢ 0
  absurd ()

flatten′ : ∀ {n} {sh : Shape n} → Index sh → ℕ
flatten′ Z = zero
flatten′ {sh = ss ∷ s} (is ∷ i) = flatten′ is * s + toℕ i

flatten′-fits : ∀ {n} {sh : Shape n} → (i : Index sh) → flatten′ i < n
flatten′-fits Z = s≤s z≤n
flatten′-fits (is ∷ i) = lemma (flatten′-fits is) (bounded i)
  where
  open ≤-Reasoning
  open IsCommutativeSemiring isCommutativeSemiring hiding (sym)
  open DecTotalOrder decTotalOrder renaming (refl to ≤-refl)

  lemma : ∀ {a b c d} → a < b → d < c → a * c + d < c * b
  lemma (s≤s {a} {b} a<b) (s≤s {d} {c} d<c) = s≤s (
    begin
      a * suc c + d
    ≡⟨ cong (λ q → q + d) (*-comm a (suc c)) ⟩
      a + c * a + d
    ≡⟨ +-assoc a (c * a) d ⟩
      a + (c * a + d)
    ≡⟨ cong (λ q → a + q) (+-comm (c * a) d) ⟩
      a + (d + c * a)
    ≡⟨ cong (λ q → a + (d + q)) (*-comm c a) ⟩
      a + (d + a * c)
    ≤⟨ a<b +-mono (d<c +-mono (a<b *-mono ≤-refl)) ⟩
      b + (c + b * c)
    ≡⟨ sym (cong (λ q → b + q) (*-comm c (suc b))) ⟩
     b + c * suc b
    ∎
    )


flatten : ∀ {n} {sh : Shape n} → Index sh → Fin n
flatten i = fromℕ≤ (flatten′-fits i)

unflatten′ : ∀ {n} {sh : Shape n} → ¬Empty sh → ℕ → Index sh
unflatten′ {sh = Z} _ _ = Z
unflatten′ {sh = ss ∷ zero} (¬E ∷ .0 [ m≢0 ]) i = ⊥-elim (m≢0 refl)
unflatten′ {sh = ss ∷ suc s} (¬E ∷ .(suc s) [ m≢0 ]) i with i divMod suc s
unflatten′ {sh = ss ∷ suc s} (¬E ∷ .(suc s) [ m≢0 ]) .(toℕ r + q * suc s) | result q r = unflatten′ ¬E q ∷ r

unflatten : ∀ {n} {sh : Shape n} → Fin n → Index sh
unflatten {zero} ()
unflatten {suc n} i = unflatten′ (n≢0→¬Empty _ absurd) (toℕ i)
  module unflatten where 
  absurd : suc n ≢ 0
  absurd ()


flatten′∘unflatten′≡id : ∀ {n} {sh : Shape n} (¬E : ¬Empty sh) x → x < n → flatten′ (unflatten′ ¬E x) ≡ x
flatten′∘unflatten′≡id Z zero x<n = refl
flatten′∘unflatten′≡id Z (suc x) (s≤s ())
flatten′∘unflatten′≡id (¬E ∷ zero [ m≢0 ]) x x<n = ⊥-elim (m≢0 refl)
flatten′∘unflatten′≡id (_∷_[_] {n} ¬E (suc m) m≢0) x x<n with x divMod suc m
flatten′∘unflatten′≡id (_∷_[_] {n} ¬E (suc m) m≢0) .(toℕ r + q * suc m) x<n | result q r = 
    begin
      flatten′ (unflatten′ ¬E q) * suc m + toℕ r
    ≡⟨ cong (λ q → q * suc m + toℕ r) (flatten′∘unflatten′≡id ¬E q (lemma₅ q n m lemma₃)) ⟩
      q * suc m + toℕ r
    ≡⟨ +-comm (q * suc m) (toℕ r) ⟩ 
      toℕ r + q * suc m
    ∎
  where
  open IsCommutativeSemiring isCommutativeSemiring hiding (sym; zero; refl)
  open EqReasoning (≡-setoid ℕ)

  m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero    n = refl
  m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

  lemma₀ : ∀ x y z → x + y ≤ z → y ≤ z
  lemma₀ zero y z x+y≤z = x+y≤z
  lemma₀ (suc x) zero .(suc z) (s≤s {n = z} x+y≤z) = z≤n
  lemma₀ (suc x) (suc y) .(suc z) (s≤s {n = z} x+y≤z) = s≤s (lemma₀ x y z (lemma₀ 1 (x + y) z (subst (λ q → q ≤ z) (m+1+n≡1+m+n x y) x+y≤z)))

  lemma₁ : ∀ x y z → x + y < z → y < z
  lemma₁ x y z x+y<z = lemma₀ x (suc y) z (subst (λ q → q ≤ z) (sym (m+1+n≡1+m+n x y)) x+y<z)

  lemma₂ : toℕ r + q * suc m < n * suc m
  lemma₂ = subst (λ z → toℕ r + q * suc m < z ) (*-comm (suc m) n) x<n

  lemma₃ : q * suc m < n * suc m
  lemma₃ = lemma₁ (toℕ r) (q * suc m) (n * suc m) lemma₂

  lemma₄ : ∀ x y z → x + y ≤ x + z → y ≤ z
  lemma₄ zero y z x+y≤x+z = x+y≤x+z
  lemma₄ (suc x) y z (s≤s x+y≤x+z) = lemma₄ x y z x+y≤x+z

  lemma₅ : ∀ x y z → x * suc z < y * suc z → x < y
  lemma₅ zero zero z ()
  lemma₅ zero (suc y) z pf = s≤s z≤n
  lemma₅ (suc x) zero z ()
  lemma₅ (suc x) (suc y) z (s≤s pf) = s≤s (lemma₅ x y z (lemma₄ z (suc (x * suc z)) (y * suc z) proof))
    where
    proof : z + suc (x * suc z) ≤ z + y * suc z
    proof = subst (λ q → q ≤ z + y * suc z) (sym (m+1+n≡1+m+n z (x * suc z))) pf

toℕ-inj : ∀ {n} {x y : Fin n} → toℕ x ≡ toℕ y → x ≡ y
toℕ-inj {x = zero} {zero} pf = refl
toℕ-inj {x = zero} {suc y} ()
toℕ-inj {x = suc x} {zero} ()
toℕ-inj {x = suc x} {suc y} pf = cong suc (toℕ-inj (cong pred pf))

flatten∘unflatten≡id : ∀ {n} {sh : Shape n} i → flatten (unflatten {sh = sh} i) ≡ i
flatten∘unflatten≡id {zero} ()
flatten∘unflatten≡id {suc n} {sh} i = toℕ-inj step₂
  where
  absurd : suc n ≢ 0
  absurd = unflatten.absurd n i

  step₁ : toℕ (fromℕ≤ (flatten′-fits (unflatten′ (n≢0→¬Empty sh absurd) (toℕ i))))
       ≡ flatten′ (unflatten′ (n≢0→¬Empty sh absurd) (toℕ i))
  step₁ = toℕ-fromℕ≤ (flatten′-fits (unflatten′ (n≢0→¬Empty sh absurd) (toℕ i)))

  step₂ : toℕ (fromℕ≤ (flatten′-fits (unflatten′ (n≢0→¬Empty sh absurd) (toℕ i)))) ≡ toℕ i
  step₂ = trans step₁ (flatten′∘unflatten′≡id (n≢0→¬Empty sh absurd) (toℕ i) (bounded i))

open IsCommutativeSemiring isCommutativeSemiring hiding (sym; zero; refl)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

+-injʳ : ∀ x y z → x + y ≡ x + z → y ≡ z
+-injʳ zero y z x+y≡x+z = x+y≡x+z
+-injʳ (suc x) y z x+y≡x+z = +-injʳ x y z (cong pred x+y≡x+z)

addMul-lemma : ∀ x x′ d (r r′ : Fin (suc d)) → toℕ r + x * suc d ≡ toℕ r′ + x′ * suc d → r ≡ r′ × x ≡ x′
addMul-lemma zero zero d zero zero pf = refl , refl
addMul-lemma zero (suc x′) d zero zero ()
addMul-lemma (suc x) zero d zero zero ()
addMul-lemma (suc x) (suc x′) d zero zero pf = refl , cong suc (proj₂ (addMul-lemma x x′ d zero zero (cancel-+-left d (cong pred pf))))
addMul-lemma zero x′ d zero (suc r′) ()
addMul-lemma (suc x) x′ zero zero (suc ()) pf
addMul-lemma zero zero d r r′ pf rewrite proj₂ +-identity (toℕ r) | proj₂ +-identity (toℕ r′) = (toℕ-inj pf) , refl
addMul-lemma zero (suc x′) d r r′ pf rewrite proj₂ +-identity (toℕ r) = ⊥-elim (large pf)
    where 
    open ≤-Reasoning
    proof : toℕ r < toℕ r′ + suc x′ * suc d
    proof = ≤-steps (toℕ r′) (
      begin
        suc (toℕ r)
      ≤⟨ bounded r ⟩
        suc d
      ≡⟨ sym (proj₁ *-identity (suc d)) ⟩
        1 * suc d
      ≤⟨ s≤s (z≤n {x′}) *-mono (≤-refl {suc d}) ⟩
        suc x′ * suc d
      ∎)

    large : toℕ r ≢ toℕ r′ + suc x′ * suc d
    large pf with toℕ r | toℕ r′ + suc x′ * suc d | proof
    large pf | left | .(suc n) | s≤s {.left} {n} left≤n rewrite pf = 1+n≰n left≤n
addMul-lemma (suc x) zero d r r′ pf rewrite proj₂ +-identity (toℕ r′) = ⊥-elim (large pf)
    where
    open ≤-Reasoning
    proof : toℕ r′ < toℕ r + suc x * suc d
    proof = ≤-steps (toℕ r) (
      begin
        suc (toℕ r′)
      ≤⟨ bounded r′ ⟩
        suc d
      ≡⟨ sym (proj₁ *-identity (suc d)) ⟩
        1 * suc d
      ≤⟨ s≤s (z≤n {x}) *-mono (≤-refl {suc d}) ⟩
        suc x * suc d
      ∎)

    large : toℕ r + suc x * suc d ≢ toℕ r′
    large pf with toℕ r′ | toℕ r + suc x * suc d | proof
    large pf | left | .(suc n) | s≤s {.left} {n} left≤n rewrite sym pf = 1+n≰n left≤n
addMul-lemma (suc x) (suc x′) d r r′ pf rewrite sym (+-assoc (toℕ r) (suc d) (x * suc d))
                                        | sym (+-assoc (toℕ r′) (suc d) (x′ * suc d))
                                        | +-comm (toℕ r) (suc d) 
                                        | +-comm (toℕ r′) (suc d)
                                        | +-assoc (suc d) (toℕ r) (x * suc d) 
                                        | +-assoc (suc d) (toℕ r′) (x′ * suc d) 
                                  with addMul-lemma x x′ d r r′ (+-injʳ (suc d) (toℕ r + x * suc d) (toℕ r′ + x′ * suc d) pf)
...                                     | pf₁ , pf₂ = pf₁ , cong suc pf₂


DivMod'-lemma : ∀ x d (r : Fin (suc d)) → (res : DivMod' (toℕ r + x * suc d) (suc d)) → res ≡ result x r refl
DivMod'-lemma x d r (result q r′ eq) with addMul-lemma x q d r r′ eq
DivMod'-lemma x d r (result .x .r eq)   | refl , refl = cong (result x r) (proof-irrelevance eq refl) -- holy fuck

divMod-lemma : ∀ x d (r : Fin (suc d)) → (toℕ r + x * suc d) divMod suc d ≡ result x r
divMod-lemma x d r with (toℕ r + x * suc d) divMod' suc d
divMod-lemma x d r | q rewrite DivMod'-lemma x d r q = refl

unflatten′∘flatten′≡id : ∀ {n} {sh : Shape n} (¬E : ¬Empty sh) (i : Index sh) → unflatten′ ¬E (flatten′ i) ≡ i
unflatten′∘flatten′≡id ¬E Z = refl
unflatten′∘flatten′≡id {sh = ss ∷ zero} ¬E (is ∷ ())
unflatten′∘flatten′≡id {sh = ss ∷ suc s} (¬E ∷ ._ [ _ ]) (is ∷ i) with inspect (flatten′ is * suc s + toℕ i)
unflatten′∘flatten′≡id {sh = ss ∷ suc s} (¬E ∷ ._ [ _ ]) (is ∷ i) | f with-≡ eq rewrite eq with f divMod suc s
unflatten′∘flatten′≡id {sh = ss ∷ suc s} (¬E ∷ ._ [ _ ]) (is ∷ i) | ._ with-≡ eq | result q r rewrite +-comm (flatten′ is * suc s) (toℕ i) with addMul-lemma (flatten′ is) q s i r eq
unflatten′∘flatten′≡id {sh = ss ∷ suc s} (¬E ∷ ._ [ _ ]) (is ∷ i) | ._ with-≡ eq | result q r | pf₁ , pf₂ rewrite sym pf₁ | sym pf₂ = cong (λ z → z ∷ i) (unflatten′∘flatten′≡id ¬E is)
  
unflatten∘flatten≡id : ∀ {n} {sh : Shape n} (i : Index sh) → unflatten (flatten i) ≡ i
unflatten∘flatten≡id {zero} i = ⊥-elim (¬Empty→n≢0 (Index→¬Empty i) refl)
unflatten∘flatten≡id {suc n} {sh} i rewrite toℕ-fromℕ≤ (flatten′-fits i) = unflatten′∘flatten′≡id (n≢0→¬Empty sh (unflatten.absurd n (fromℕ≤ (flatten′-fits i)))) i

Simple-Bijection : ∀ {A B : Set} → (f : A → B) (g : B → A) → (∀ a → g (f a) ≡ a) → (∀ b → f (g b) ≡ b) → Bijection (≡-setoid A) (≡-setoid B)
Simple-Bijection f g pf₁ pf₂ = record 
  { to = record 
    { _⟨$⟩_ = f
    ; cong = cong f
    }
  ; bijective = record 
    { injective = injective
    ; surjective = record 
      { from = record 
        { _⟨$⟩_ = g
        ; cong = cong g
        }
      ; right-inverse-of = pf₂
      }
    }
  }
  where
  injective : ∀ {x y} → f x ≡ f y → x ≡ y
  injective {x} {y} fx≡fy with cong g fx≡fy 
  ...             | q rewrite pf₁ x | pf₁ y = q


Index↔Fin : ∀ {n} (sh : Shape n) → Bijection (≡-setoid (Index sh)) (≡-setoid (Fin n))
Index↔Fin sh = Simple-Bijection flatten unflatten unflatten∘flatten≡id flatten∘unflatten≡id
