open import Relation.Binary
  using (Rel; Tri; IsStrictTotalOrder; IsPartialOrder)
open Tri
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; cong)
open P.≡-Reasoning

open import Level using (_⊔_)
open import Data.Nat using (ℕ)
open ℕ
open import Data.Product using (_,_)
open import Data.List using (List; _++_)
open List
open import Data.List.All using (All)
open All
open import Data.Maybe using (Maybe)
open Maybe
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_)
open _⊎_

module Data.Map.Higher
  {k r v} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  (V : Key -> Set v) where

open IsStrictTotalOrder isStrictTotalOrder
  using (compare; isStrictPartialOrder) renaming (trans to <-trans)
open import Relation.Binary.StrictToNonStrict _≡_ _<_
  using (_≤_; reflexive; isPartialOrder)
open IsPartialOrder (isPartialOrder isStrictPartialOrder)
  using () renaming (antisym to ≤-antisym)



open import Data.Map.Key Key isStrictTotalOrder public
open import Data.Map.Height public

postulate
  undefined : ∀ {a} {A : Set a} -> A

[_] : ∀ {a} {A : Set a} -> A -> List A
[ x ] = x ∷ []

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

lookup : ∀ {h} {l-bound r-bound} {xs} -> (key : Key) -> AVL l-bound r-bound h xs -> Maybe (V key)
lookup key₁ (Leaf _) = nothing
lookup key₁ (Node key₂ value left right _) with compare key₁ key₂
... | tri< _ _ _ = lookup key₁ left
... | tri≈ _ key₁≡key₂ _ rewrite key₁≡key₂ = just value
... | tri> _ _ _ = lookup key₁ right

data Insert (l-bound r-bound : Bound) (height : ℕ) (xs : List Key) : Set (k ⊔ v ⊔ r) where
  +zero : AVL l-bound r-bound height xs       -> Insert l-bound r-bound height xs
  +one  : AVL l-bound r-bound (suc height) xs -> Insert l-bound r-bound height xs

merge-leftⁱ
  : ∀ {h-left h-right h}
  {l-bound r-bound}
  {l-left l-right}
  (key : Key)
  -> V key
  -> Insert l-bound ⟨ key ⟩ h-left l-left
  -> AVL ⟨ key ⟩ r-bound h-right l-right
  -> max (h-left , h-right) ↦ h
  -> Insert l-bound r-bound (suc h) (l-left ++ [ key ] ++ l-right)
merge-leftⁱ = undefined

merge-rightⁱ
  : ∀ {h-left h-right h}
  {l-bound r-bound}
  {l-left l-right}
  (key : Key)
  -> V key
  -> AVL l-bound ⟨ key ⟩ h-left l-left
  -> Insert ⟨ key ⟩ r-bound h-right l-right
  -> max (h-left , h-right) ↦ h
  -> Insert l-bound r-bound (suc h) (l-left ++ [ key ] ++ l-right)
merge-rightⁱ = undefined

insert : Key -> List Key -> List Key
insert x [] = x ∷ []
insert x (y ∷ ys) with compare x y
... | tri< _ _ _ = x ∷ y ∷ ys
... | tri≈ _ _ _ = x ∷ ys
... | tri> _ _ _ = y ∷ insert x ys

<-raise : ∀ {x y z} -> x < y -> y ≤ z -> x < z
<-raise x<y (inj₁ y<z) = <-trans x<y y<z
<-raise x<y (inj₂ y≡z) rewrite y≡z = x<y

insert-< : ∀ {key₁ key₂} {ks} -> key₁ < key₂ -> insert key₁ ([ key₂ ] ++ ks) ≡ key₁ ∷ key₂ ∷ ks
insert-< {key₁} {key₂} key₁<key₂ with compare key₁ key₂
... | tri< _ _ _          = refl
... | tri≈ ¬key₁<key₂ _ _ = ⊥-elim (¬key₁<key₂ key₁<key₂)
... | tri> ¬key₁<key₂ _ _ = ⊥-elim (¬key₁<key₂ key₁<key₂)

insert-≡ : ∀ {key} {ks} -> insert key ([ key ] ++ ks) ≡ [ key ] ++ ks
insert-≡ {key} with compare key key
... | tri< _ ¬key≡key _ = ⊥-elim (¬key≡key refl)
... | tri≈ _ _ _        = refl
... | tri> _ ¬key≡key _ = ⊥-elim (¬key≡key refl)

insert-> : ∀ {key₁ key₂} {ks} -> key₂ < key₁ -> insert key₁ ([ key₂ ] ++ ks) ≡ key₂ ∷ insert key₁ ks
insert-> {key₁} {key₂} key₂<key₁ with compare key₁ key₂
... | tri< _ _ ¬key₂<key₁ = ⊥-elim (¬key₂<key₁ key₂<key₁)
... | tri≈ _ _ ¬key₂<key₁ = ⊥-elim (¬key₂<key₁ key₂<key₁)
... | tri> _ _ _          = refl

insert-move-right
  : ∀ {key₁} {key₂} left right
  -> key₁ ≤ key₂
  -> All (λ x → x < key₁) left
  -> insert key₂ (left ++ [ key₁ ] ++ right) ≡ left ++ insert key₂ ([ key₁ ] ++ right)
insert-move-right {key₁} {key₂} [] right key₁≤key₂ [] with compare key₂ key₁
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> _ _ _ = refl
insert-move-right {key₁} {key₂} (l ∷ left) right key₁≤key₂ (l<key₁ ∷ left<key₁) with compare key₁ l
... | tri< _ _ ¬l<key₁ = ⊥-elim (¬l<key₁ l<key₁)
... | tri≈ _ _ ¬l<key₁ = ⊥-elim (¬l<key₁ l<key₁)
... | tri> _ _ _ with compare key₂ l
... | tri< _ _ ¬l<key₂ = ⊥-elim (¬l<key₂ (<-raise l<key₁ key₁≤key₂))
... | tri≈ _ _ ¬l<key₂ = ⊥-elim (¬l<key₂ (<-raise l<key₁ key₁≤key₂))
... | tri> _ _ _ = cong (λ ls → l ∷ ls) (insert-move-right left right key₁≤key₂ left<key₁)

insert-leftⁱ
  : ∀ {key₁ key₂} left right
  -> key₁ < key₂
  -> insert key₁ (left ++ [ key₂ ] ++ right) ≡ insert key₁ left ++ [ key₂ ] ++ right
insert-leftⁱ [] right key₁<key₂ = insert-< key₁<key₂
insert-leftⁱ {key₁} {key₂} (l ∷ left) right key₁<key₂ with compare key₁ l
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> _ _ _ = cong (λ ls → l ∷ ls) (insert-leftⁱ left right key₁<key₂)

insertⁱ
  : ∀ key left right
  -> All (λ x -> x < key) left
  -> insert key (left ++ [ key ] ++ right) ≡ left ++ [ key ] ++ right
insertⁱ key left right left<key =
  insert key (left ++ [ key ] ++ right) ≡⟨ insert-move-right left right (reflexive refl) left<key ⟩
  left ++ insert key ([ key ] ++ right) ≡⟨ cong (λ r → left ++ r) insert-≡ ⟩
  left ++ [ key ] ++ right ∎

insert-rightⁱ
  : ∀ {key₁ key₂} left right
  -> key₂ < key₁
  -> All (λ x → x < key₂) left
  -> insert key₁ (left ++ [ key₂ ] ++ right) ≡ left ++ [ key₂ ] ++ insert key₁ right
insert-rightⁱ {key₁} {key₂} left right key₂<key₁ left<key₂ =
  insert key₁ (left ++ [ key₂ ] ++ right)   ≡⟨ insert-move-right left right (inj₁ key₂<key₁) left<key₂ ⟩
  left ++ (insert key₁ ([ key₂ ] ++ right)) ≡⟨ cong (λ r → left ++ r) (insert-> key₂<key₁)  ⟩
  left ++ [ key₂ ] ++ insert key₁ right ∎

insertWith
  : ∀ {h} {l-bound r-bound} {ks}
  -> (key : Key)
  -> V key
  -> (V key -> V key -> V key)
  -> l-bound < key < r-bound
  -> AVL l-bound r-bound h ks
  -> Insert l-bound r-bound h (insert key ks)
insertWith key₁ value₁ update
  l-bound<key<r-bound (Leaf l-bound<r-bound)
  = +one (singleton key₁ value₁ l-bound<key<r-bound)
insertWith key₁ value₁ update (l-bound<key <×< key<r-bound)
  (Node {l-left = l-left} {l-right = l-right} key₂ value₂ left₁ right₁ bal) with compare key₁ key₂
... | tri< key₁<key₂ _ _ rewrite insert-leftⁱ l-left l-right key₁<key₂
    = merge-leftⁱ key₂ value₂ left₂ right₁ bal
    where left₂ = insertWith key₁ value₁ update (l-bound<key <×< ⟨ key₁<key₂ ⟩) left₁
... | tri≈ _ key₁≡key₂ _ rewrite key₁≡key₂ | insertⁱ key₂ l-left l-right undefined
    = +zero (Node key₂ (update value₁ value₂) left₁ right₁ bal)
... | tri> _ _ key₂<key₁ rewrite insert-rightⁱ l-left l-right key₂<key₁ undefined
    = merge-rightⁱ key₂ value₂ left₁ right₂ bal
    where right₂ = insertWith key₁ value₁ update (⟨ key₂<key₁ ⟩ <×< key<r-bound) right₁
