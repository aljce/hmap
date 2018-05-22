open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-isStrictTotalOrder)
open import Function using (const)
open import Data.String using (String)
open import Data.List using (List)
open List
open import Data.Product using (_,_)

module Test where

open import Data.List.Membership
open import Data.Map ℕ <-isStrictTotalOrder (const String)

map₁ : Map (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
map₁ = fromList ((2 , "foo") ∷ (1 , "bar") ∷ (3 , "baz") ∷ (0 , "quix") ∷ [])

lookup-unit₁ : lookup 3 map₁ ≡ "baz"
lookup-unit₁ = refl
