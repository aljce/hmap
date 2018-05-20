open import Data.Nat using (ℕ; pred)
open ℕ
open import Data.Product using (_×_; _,_)

module Data.Map.Height where

infix 4 max_↦_
data max_↦_ : ℕ × ℕ -> ℕ -> Set where
  ↦l : ∀ {n} → max (suc n , n) ↦ suc n
  ↦b : ∀ {n} → max (n ,     n) ↦ n
  ↦r : ∀ {n} → max (n , suc n) ↦ suc n

max[h,l]↦h : ∀ {l r h} -> max (l , r) ↦ h -> max (h , l) ↦ h
max[h,l]↦h ↦l = ↦b
max[h,l]↦h ↦b = ↦b
max[h,l]↦h ↦r = ↦l

max[r,h]↦h : ∀ {l r h} -> max (l , r) ↦ h -> max (r , h) ↦ h
max[r,h]↦h ↦l = ↦r
max[r,h]↦h ↦b = ↦b
max[r,h]↦h ↦r = ↦b

max[h-1,h]↦h : ∀ {h} -> max (pred h , h) ↦ h
max[h-1,h]↦h {zero}  = ↦b
max[h-1,h]↦h {suc h} = ↦r
