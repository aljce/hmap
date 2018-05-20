open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Level using (_⊔_)
open import Data.Nat using (ℕ)
open ℕ
open import Data.Product using (_,_)
open import Data.List using (List; _++_)
open List

module Data.AVL.Higher
  {k r v} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  (V : Key -> Set v) where

open import Data.AVL.Key Key isStrictTotalOrder public
open import Data.AVL.Height public

[_] : ∀ {a} {A : Set a} -> A -> List A
[_] x = x ∷ []

data AVL (l-bound r-bound : Bound) : (height : ℕ) -> (keys : List Key) -> Set (k ⊔ r ⊔ v) where
  Leaf : l-bound <ᵇ r-bound -> AVL l-bound r-bound 0 []
  Node :
    ∀ {h-left h-right h l-left l-right}
      (key     : Key)
      (value   : V key)
      (left    : AVL l-bound ⟨ key ⟩ h-left  l-left)
      (right   : AVL ⟨ key ⟩ r-bound h-right l-right)
      (balance : max (h-left , h-right) ↦ h)
    → AVL l-bound r-bound (suc h) (l-left ++ [ key ] ++ l-right)

empty : ∀ {l-bound r-bound} -> l-bound <ᵇ r-bound -> AVL l-bound r-bound 0 []
empty = Leaf

singleton
  : ∀ {l-bound r-bound} (key : Key)
  -> V key
  -> l-bound < key < r-bound
  -> AVL l-bound r-bound 1 [ key ]
singleton key value bst = Node key value (Leaf (lower bst)) (Leaf (upper bst)) ↦b


