open import Relation.Binary
  using (Rel; IsStrictTotalOrder; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Data.Map.Key
  {k r} (Key : Set k) {_<_ : Rel Key r}
  (is-strict-total-order : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder is-strict-total-order

data Bound : Set k where
  -∞  : Bound
  ⟨_⟩ : Key -> Bound
  +∞  : Bound

infix 4 _<ᵇ_
infix 5 -∞<_ _<+∞
data _<ᵇ_ : Bound -> Bound -> Set r where
  -∞<_ : (top : Key) -> -∞ <ᵇ ⟨ top ⟩
  ⟨_⟩ : ∀ {bot top} -> bot < top -> ⟨ bot ⟩ <ᵇ ⟨ top ⟩
  _<+∞ : (bot : Key) -> ⟨ bot ⟩ <ᵇ +∞
  -∞<+∞ : -∞ <ᵇ +∞

<ᵇ-transitive : Transitive _<ᵇ_
<ᵇ-transitive {k = ⟨ top ⟩} (-∞< bot) ⟨ bot<top ⟩ = -∞< top
<ᵇ-transitive (-∞< top) (.top <+∞) = -∞<+∞
<ᵇ-transitive ⟨ bot<mid ⟩ ⟨ mid<top ⟩ = ⟨ trans bot<mid mid<top ⟩
<ᵇ-transitive {i = ⟨ bot ⟩} ⟨ bot<top ⟩ (top <+∞) = bot <+∞
<ᵇ-transitive (bot <+∞) ()
<ᵇ-transitive -∞<+∞ ()

infix 3 _<×<_
record _<_<_ (l-bound : Bound) (key : Key) (r-bound : Bound) : Set r where
  constructor _<×<_
  field
    lower : l-bound <ᵇ ⟨ key ⟩
    upper : ⟨ key ⟩ <ᵇ r-bound
open _<_<_ public
