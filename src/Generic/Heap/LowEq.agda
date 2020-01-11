open import Lattice
open import Relation.Binary

module Generic.Heap.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈ⱽ_ :  ∀ {τ} → Value τ → Value τ → Set)
  (A : Label) where

open import Data.Product
open import Data.Fin
open import Data.Maybe
open import Generic.Bijection
open import Generic.Heap.Base Ty Value
open import Function.Equality
open import Function.Bijection as B
open import Relation.Binary.PropositionalEquality as P

-- Syntatic sugar. A bijection with domain and range equal
-- to the given heaps.
Bij⟨_,_⟩ : Heap → Heap → Set
Bij⟨ μ₁ , μ₂ ⟩ = Bij ∥ μ₁ ∥ᴴ ∥ μ₂ ∥ᴴ

-- Two heaps are A-equivalent up to bijection β iff the addresses
-- related by the bijection map to related values in the respective
-- heaps. Since the domain and the range of the bijection is indexed with
-- the size of the heaps, the lookups are safe.
-- To index the bijection correctly, the relation must first introduce
-- the heaps and then the bijection. The following definition defines
-- the usual infix operator as syntatic sugar.
Heap-≈ : (μ₁ μ₂ : Heap) → Bij⟨ μ₁ , μ₂ ⟩ → Set
Heap-≈ μ₁ μ₂ β =
  ∀ (x : Fin ∥ μ₁ ∥ᴴ) →
  let τ , v , ∈₁ = μ₁ [ x ]ᴴ
      τ' , v' , ∈₂ = μ₂ [ to ⟨$⟩ x ]ᴴ in v ≅ⱽ v'
  where open Bijection β
        open import Function.Equality
        open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_

-- Syntactic sugar
_≈⟨_⟩ᴴ_ : ∀ {n} → (μ₁ : Heap) → Bij ∥ μ₁ ∥ᴴ n → (μ₂ : Heap) → {{eq : n ≡ ∥ μ₂ ∥ᴴ}} → Set
_≈⟨_⟩ᴴ_ μ₁ β μ₂ {{eq}} rewrite eq = Heap-≈ μ₁ μ₂ β

module Props (𝑽 : ∀ {τ} → IsEquivalence (_≈ⱽ_ {τ})) where

  open import Generic.Value.HLowEq {Ty} {Value} _≈ⱽ_
  open Props 𝑽

  refl-≈ᴴ : ∀ {μ} → μ ≈⟨ ι ⟩ᴴ μ
  refl-≈ᴴ {μ} x = refl-≅ⱽ

  sym-≈ᴴ : ∀ {μ₁ μ₂} {β : Bij⟨ μ₁ , μ₂ ⟩ } → μ₁ ≈⟨ β ⟩ᴴ μ₂ → μ₂ ≈⟨ β ⁻¹ ⟩ᴴ μ₁
  sym-≈ᴴ {β = β} ≈ᴴ x with ≈ᴴ (Bijection.to (β ⁻¹) ⟨$⟩ x) | Bijection.left-inverse-of (β ⁻¹) x
  ... | ≈ⱽ | eq rewrite eq = sym-≅ⱽ ≈ⱽ

  trans-≈ᴴ : ∀ {μ₁ μ₂ μ₃} {β₁ : Bij⟨ μ₁ , μ₂ ⟩} {β₂ : Bij⟨ μ₂ , μ₃ ⟩} →
               μ₁ ≈⟨ β₁ ⟩ᴴ μ₂ → μ₂ ≈⟨ β₂ ⟩ᴴ μ₃ → μ₁ ≈⟨ β₂ ∘ᴮ β₁ ⟩ᴴ μ₃
  trans-≈ᴴ {β₁ = β₁} {β₂} ≈₁ ≈₂ x = trans-≅ⱽ (≈₁ x) (≈₂ (Bijection.to β₁ ⟨$⟩ x) )

  -- Notice that this is not strictly an equivalence because we must be able to choose the
  -- identity bijection for refl.

_≈ᴴ_ : Heap → Heap → Set
μ₁ ≈ᴴ μ₂ = Σ Bij⟨ μ₁ , μ₂ ⟩ (λ β → μ₁ ≈⟨ β ⟩ᴴ μ₂)
