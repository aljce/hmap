open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Level using (_⊔_)
open import Data.Product using (Σ)
open Σ
open import Data.List using (List; [_]; foldr)
open List
open import Function using (const; _∘_)

module Data.Map
  {k r v} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  (V : Key -> Set v) where

open import Data.Map.Key Key isStrictTotalOrder
open import Data.List.Insert Key isStrictTotalOrder
  using () renaming (insert to insertˡ)
open import Data.List.Membership
import Data.Map.Indexed Key isStrictTotalOrder V as Bounded
open Bounded.Insert

data Map (ks : List Key) : Set (k ⊔ v ⊔ r) where
  tree : ∀ {h} -> Bounded.AVL -∞ +∞ h ks -> Map ks

empty : Map []
empty = tree (Bounded.empty -∞<+∞)

singleton : (key : Key) -> V key -> Map [ key ]
singleton key value = tree (Bounded.singleton key value (open-bounds key))

lookup : ∀ {ks} -> (key : Key) -> {{ prf : key ∈ ks }} -> Map ks -> V key
lookup key (tree avl) = Bounded.lookup key avl

insertWith
  : ∀ {ks}
  -> (key : Key)
  -> V key
  -> (V key -> V key -> V key)
  -> Map ks
  -> Map (insertˡ key ks)
insertWith key value update (tree avl₁) with Bounded.insertWith key value update (open-bounds key) avl₁
... | +zero avl₂ = tree avl₂
... | +one  avl₂ = tree avl₂

insert : ∀ {ks} -> (key : Key) -> V key -> Map ks -> Map (insertˡ key ks)
insert key value = insertWith key value const

fromList : (xs : List (Σ Key V)) -> Map (foldr (insertˡ ∘ proj₁) [] xs)
fromList [] = empty
fromList (kv ∷ kvs) = insert (proj₁ kv) (proj₂ kv) (fromList kvs)
