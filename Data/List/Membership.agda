open import Relation.Binary using (Rel; IsStrictTotalOrder; IsStrictPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Empty using (⊥)
open import Data.List using (List; [_]; _++_)
open List
open import Data.List.All using (All)
open All
open import Data.Empty using (⊥; ⊥-elim)

module Data.List.Membership where

infix 4 _∈_
data _∈_ {a} {A : Set a} (x : A) : List A → Set a where
  instance
    here  : ∀ {xs : List A} → x ∈ x ∷ xs
    there : ∀ {y} {xs : List A} → (x∈xs : x ∈ xs) → x ∈ y ∷ xs

∈[]-empty : ∀ {a} {A : Set a} {x : A} -> x ∈ [] -> ⊥
∈[]-empty ()

module Ordered
  {k r} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

  open IsStrictTotalOrder isStrictTotalOrder
    using (compare) renaming (trans to <-trans; isStrictPartialOrder to <-isStrictPartialOrder)
  open IsStrictPartialOrder <-isStrictPartialOrder
    using () renaming (irrefl to <-irrefl)

  ∈-left
    : ∀ {ls rs} {key₁ key₂}
    -> All (λ x → key₂ < x) rs
    -> key₁ < key₂
    -> key₁ ∈ ls ++ [ key₂ ] ++ rs
    -> key₁ ∈ ls
  ∈-left {[]} key₂<rs key₁<key₂ here = ⊥-elim (<-irrefl refl key₁<key₂)
  ∈-left {[]} {_} {key₁} {key₂} key₂<rs key₁<key₂ (there prf) = ⊥-elim (∉-right key₂<rs prf)
    where
    ∉-right : ∀ {xs} -> All (λ x → key₂ < x) xs -> key₁ ∈ xs -> ⊥
    ∉-right [] ()
    ∉-right (key₂<x ∷ key₂<xs) here = ⊥-elim (<-irrefl refl (<-trans key₂<x key₁<key₂))
    ∉-right (key₂<x ∷ key₂<xs) (there prf) = ∉-right key₂<xs prf
  ∈-left {x ∷ ls} key₂<rs key₁<key₂ here = here
  ∈-left {x ∷ ls} key₂<rs key₁<key₂ (there prf) = there (∈-left key₂<rs key₁<key₂ prf)

  ∈-right
    : ∀ {ls rs} {key₁ key₂}
    -> All (λ x → x < key₂) ls
    -> key₂ < key₁
    -> key₁ ∈ ls ++ [ key₂ ] ++ rs
    -> key₁ ∈ rs
  ∈-right [] key₂<key₁ here = ⊥-elim (<-irrefl refl key₂<key₁)
  ∈-right [] key₂<key₁ (there prf) = prf
  ∈-right (l<key₂ ∷ ls<key₂) key₂<key₁ here = ⊥-elim (<-irrefl refl (<-trans l<key₂ key₂<key₁))
  ∈-right (l<key₂ ∷ ls<key₂) key₂<key₁ (there prf) = ∈-right ls<key₂ key₂<key₁ prf

