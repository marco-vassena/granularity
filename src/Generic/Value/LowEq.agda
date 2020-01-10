open import Relation.Binary

module Generic.Value.LowEq
  {Ty : Set} {Value : Ty → Set}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set) where


-- Heterogeneous version of low-equivlence (accepts values with different types).
data _≅ⱽ_ {τ} (v : Value τ) : ∀ {τ} → Value τ → Set where
  ⌞_⌟ : ∀ {v' : Value τ} → v ≈ⱽ v' → v ≅ⱽ v'

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  open import Relation.Binary renaming (IsEquivalence to R)

  refl-≈ⱽ : ∀ {τ} → {v : Value τ} → v ≈ⱽ v
  refl-≈ⱽ = R.refl 𝑽

  sym-≈ⱽ : ∀ {τ} {v₁ v₂ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₁
  sym-≈ⱽ = R.sym 𝑽

  trans-≈ⱽ : ∀ {τ} {v₁ v₂ v₃ : Value τ} → v₁ ≈ⱽ v₂ → v₂ ≈ⱽ v₃ → v₁ ≈ⱽ v₃
  trans-≈ⱽ = R.trans 𝑽
