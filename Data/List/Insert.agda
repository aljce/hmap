open import Relation.Binary using (Rel; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong)
open P.≡-Reasoning

open import Data.List using (List; [_]; _++_)
open List
open import Data.List.All using (All)
open All
open import Relation.Binary using (Tri)
open Tri
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_)
open _⊎_

module Data.List.Insert
  {k r} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder isStrictTotalOrder renaming (trans to <-trans)
open import Relation.Binary.StrictToNonStrict _≡_ _<_
  using (_≤_; reflexive) renaming (isPartialOrder to ≤-isPartialOrder)

insert : Key -> List Key -> List Key
insert x [] = x ∷ []
insert x (y ∷ ys) with compare x y
... | tri< _ _ _ = x ∷ y ∷ ys
... | tri≈ _ _ _ = x ∷ ys
... | tri> _ _ _ = y ∷ insert x ys

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

<-raise : ∀ {x y z} -> x < y -> y ≤ z -> x < z
<-raise x<y (inj₁ y<z) = <-trans x<y y<z
<-raise x<y (inj₂ y≡z) rewrite y≡z = x<y

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
  insert key₁ (left ++ [ key₂ ] ++ right)   ≡⟨ insert-move-right left right key₂≤key₁ left<key₂ ⟩
  left ++ (insert key₁ ([ key₂ ] ++ right)) ≡⟨ cong (λ r → left ++ r) (insert-> key₂<key₁)  ⟩
  left ++ [ key₂ ] ++ insert key₁ right ∎
  where key₂≤key₁ = inj₁ key₂<key₁


