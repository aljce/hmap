open import Relation.Binary using
  (Rel; IsStrictTotalOrder; IsDecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Level using (_⊔_)
open import Data.Sum using (inj₁)
open import Data.List using (List; foldr)
open List
open import Relation.Binary using (Tri)
open Tri
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning

module Data.List.Sorted
  {a r} (A : Set a) {_<_ : Rel A r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder isStrictTotalOrder
open import Relation.Binary.StrictToNonStrict _≡_ _<_
  using (_≤_; reflexive; isDecTotalOrder)
open IsDecTotalOrder (isDecTotalOrder isStrictTotalOrder)
  using () renaming (trans to ≤-trans)

↑_ : _<_ ⇒ _≤_
↑ i<j = inj₁ i<j

infixr 5 _≤*_
data _≤*_ (x : A) : List A -> Set (a ⊔ r) where
  ≤[]  : x ≤* []
  _≤∷_ : ∀ {y} {ys} -> x ≤ y -> x ≤* ys -> x ≤* y ∷ ys

≤*-lower : ∀ {x y} {ys} -> x ≤ y -> y ≤* ys -> x ≤* ys
≤*-lower x≤y ≤[] = ≤[]
≤*-lower x≤y (y≤z ≤∷ y≤*ys) = ≤-trans x≤y y≤z ≤∷ ≤*-lower x≤y y≤*ys

data _◂_≡_ (x : A) : List A → List A → Set a where
  here  : ∀ {xs}           → x ◂ xs ≡ (x ∷ xs)
  there : ∀ {y} {xs} {xys} → x ◂ xs ≡ xys → x ◂ (y ∷ xs) ≡ (y ∷ xys)

data Sorted : List A -> Set (a ⊔ r) where
  nil  : Sorted []
  cons : ∀ x {xs xys} -> x ≤* xs -> x ◂ xs ≡ xys -> Sorted xs -> Sorted xys

sorted-list : ∀ {xs} -> Sorted xs -> List A
sorted-list nil = []
sorted-list (cons x _ _ xs) = x ∷ sorted-list xs

≤*-insert : ∀ {x y} {ys xs} -> y ◂ ys ≡ xs -> x ≤ y -> x ≤* ys -> x ≤* xs
≤*-insert here x≤y x≤*ys = x≤y ≤∷ x≤*ys
≤*-insert (there p) x≤y (x≤z ≤∷ x≤*ys) = x≤z ≤∷ ≤*-insert p x≤y x≤*ys

insert : ∀ x {xs} -> Sorted xs -> Sorted (x ∷ xs)
insert x nil = cons x ≤[] here nil
insert x {xs} sorted-xs@(cons y {ys} {xys} y≤*ys y◂ys≡yxs sorted-ys) with compare x y
... | tri< x<y _ _ = cons x (≤*-insert y◂ys≡yxs x≤y (≤*-lower x≤y y≤*ys)) here sorted-xs
  where x≤y = ↑ x<y
... | tri≈ _ x≡y _ = cons x (≤*-insert y◂ys≡yxs x≤y (≤*-lower x≤y y≤*ys)) here sorted-xs
  where x≤y = reflexive x≡y
... | tri> _ _ y<x = cons y (y≤x ≤∷ y≤*ys) (there y◂ys≡yxs) (insert x sorted-ys)
  where y≤x = ↑ y<x

insertion-sort : ∀ xs -> Sorted xs
insertion-sort [] = nil
insertion-sort (x ∷ xs) = insert x (insertion-sort xs)

-- smallest-placed-equal : ∀ {a b} {as bs xs} -> a ≤* as -> b ≤* bs -> a ◂ as ≡ xs -> b ◂ bs ≡ xs -> a ≡ b
-- smallest-placed-equal a b c d = {!!}

-- sorted-unique : ∀ {xs} (as bs : Sorted xs) -> sorted-list as ≡ sorted-list bs
-- sorted-unique nil nil = refl
-- sorted-unique nil (cons b b≤bs () sorted-bs)
-- sorted-unique (cons a a≤*as () sorted-as) nil
-- sorted-unique (cons a {as} a≤*as a◂as≡xs sorted-as) (cons b {bs} b≤*bs b◂bs≡xs sorted-bs) =
--   cong₂ _∷_ a≡b rec
--   where
--   a≡b : a ≡ b
--   a≡b =
--     begin a
--     ≡⟨ smallest-placed-equal a≤*as b≤*bs a◂as≡xs b◂bs≡xs ⟩
--     b ∎
--   as≡bs : as ≡ bs
--   as≡bs =
--     begin as
--     ≡⟨ {!!} ⟩
--     bs ∎
--   asequalbs = as≡bs
--   rec : sorted-list sorted-as ≡ sorted-list sorted-bs
--   rec =
--     begin
--       (sorted-list sorted-as)
--     ≡⟨ sorted-unique sorted-as (subst Sorted (sym as≡bs) sorted-bs) ⟩
--       sorted-list (subst Sorted (sym as≡bs) sorted-bs)
--     ≡⟨ {!!} ⟩
--     (sorted-list sorted-bs) ∎

