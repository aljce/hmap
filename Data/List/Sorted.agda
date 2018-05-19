open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Level using (_⊔_)
open import Data.List using (List; foldr)
open List
open import Relation.Binary using (Tri)
open Tri

module Data.List.Sorted
  {a r} (A : Set a) {_<_ : Rel A r}
  (is-strict-total-order : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder is-strict-total-order

postulate
  undefined : ∀ {a} {A : Set a} -> A

infixr 5 _<*_
data _<*_ (x : A) : List A -> Set (a ⊔ r) where
  <[]  : x <* []
  <∷_ : ∀ {y} {ys} -> x < y -> x <* y ∷ ys

data Ascending : List A -> Set (a ⊔ r) where
  []  : Ascending []
  _∷_ : ∀ {x} {xs} -> x <* xs -> Ascending xs -> Ascending (x ∷ xs)

data _◂_≡_ (x : A) : List A → List A → Set a where
  here  : ∀ {xs}           → x ◂ xs ≡ (x ∷ xs)
  there : ∀ {y} {xs} {xys} → x ◂ xs ≡ xys → x ◂ (y ∷ xs) ≡ (y ∷ xys)

data Permutation : List A → List A → Set a where
  []  : Permutation [] []
  _∷_ : ∀ {x xs ys xys}
      → x ◂ ys ≡ xys
      → Permutation xs ys
      → Permutation (x ∷ xs) xys

record Sorted (xs : List A) : Set (a ⊔ r) where
  constructor sorted
  field
    ys : List A
    is-ascending : Ascending ys
    is-permutation : Permutation ys xs

empty-list-is-sorted : Sorted []
empty-list-is-sorted = record { ys = [] ; is-ascending = [] ; is-permutation = [] }

insert : A -> List A -> List A
insert x [] = x ∷ []
insert x (y ∷ ys) with compare x y
... | tri> _ _ _ = y ∷ insert x ys
... | _          = x ∷ y ∷ ys

insert-preserves-sorted : ∀ {xs} x -> Sorted xs -> Sorted (x ∷ xs)
insert-preserves-sorted {xs} x (sorted ys ys-asc ys-perm) =
  sorted (insert x ys) (insert-preserves-ascending ys-asc) (insert-preserves-perm ys-perm)
  where
  insert-preserves-ascending : ∀ {zs} -> Ascending zs -> Ascending (insert x zs)
  insert-preserves-ascending [] = <[] ∷ []
  insert-preserves-ascending (_∷_ {z} {zs} z<*zs zs-asc) with compare x z
  ... | tri< x<z _ _ = (<∷ x<z) ∷ z<*zs ∷ zs-asc
    -- where
    -- insert-preserves-<* : ∀ {z} {zs} -> z <* zs -> z <* insert x zs
    -- insert-preserves-<* <[] = <∷ {!!}
    -- insert-preserves-<* (<∷ x₁) = {!!}
  ... | tri≈ _ _ _ = {!!} ∷ {!!}
  ... | tri> _ _ _ = {!!} ∷ {!!}
  insert-preserves-perm : Permutation ys xs -> Permutation (insert x ys) (x ∷ xs)
  insert-preserves-perm perm = undefined

insertion-sort : ∀ xs -> Sorted xs
insertion-sort [] = empty-list-is-sorted
insertion-sort (x ∷ xs) = insert-preserves-sorted x (insertion-sort xs)
