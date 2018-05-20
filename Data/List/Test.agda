module Data.List.Test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-isStrictTotalOrder)
open import Data.List using (List)
open List
open import Data.List.Sorted ℕ <-isStrictTotalOrder

unit₁ : sorted-list (insertion-sort (3 ∷ 5 ∷ 2 ∷ 8 ∷ 1 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
unit₁ = refl
