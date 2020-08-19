open import Data.Nat hiding (_≟_)
open import Lattice
open import Generic.Valid

module Generic.Store.Valid
  {{𝑳 : Lattice}}
  {Ty : Set}
  {Value : Ty → Set}
  {∥_∥ⱽ : ∀ {τ} → Value τ → ℕ}
  (𝑽 : IsValid Ty Value ∥_∥ⱽ ) where

--  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set) where

open import Generic.Store Ty Value
open import Generic.Memory.Valid 𝑽 public

Validˢ : ℕ → Store → Set
Validˢ n Σ = ∀ ℓ → Validᴹ n (Σ ℓ)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

update-validˢ : ∀ {Σ ℓ} {M : Memory ℓ} n → Validˢ n Σ → Validᴹ n M → Validˢ n (Σ [ ℓ ↦ M ]ˢ)
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' with ℓ ≟ ℓ'
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' | yes refl = isVᴹ
update-validˢ {Σ} {ℓ} _ isV isVᴹ ℓ' | no ¬p = isV ℓ'

validˢ-⊆ᴴ : ∀ {Σ n n'} → n ≤ n' → Validˢ n Σ → Validˢ n' Σ
validˢ-⊆ᴴ {Σ} ≤₁ isV ℓ = wken-valid (Σ ℓ) ≤₁ (isV ℓ)
  where open IsValid IsValidᴹ
