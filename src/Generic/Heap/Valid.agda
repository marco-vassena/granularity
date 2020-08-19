open import Data.Nat
open import Lattice
open import Generic.Valid

module Generic.Heap.Valid
  {{𝑳 : Lattice}}
  {Ty : Set}
  {Value : Ty → Set}
  {∥_∥ⱽ : ∀ {τ} → Value τ → ℕ}
--  (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set)
  (𝑽 : IsValid Ty Value ∥_∥ⱽ)

  where


open import Data.Unit hiding (_≤_)
import Generic.Container.Base ⊤ Ty Value as B
open import Generic.Heap.Base Ty Value as S
open import Generic.Heap.Lemmas Ty Value
open import Data.Product
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open IsValid 𝑽 renaming (Valid to Validⱽ)

open import Generic.Container.Valid ⊤ 𝑽
  renaming ( read-valid to read-validⱽ
           ; write-valid to write-validᴴ
           ; tail-valid to tail-validᴴ )
  hiding (∥_∥ᶜ ; snoc-valid) public

Validᴴ : Heap → Set
Validᴴ μ = Validᶜ ∥ μ ∥ᴴ μ

open import Data.Sum

snoc-validᴴ′ : ∀ {τ} {μ : Heap} {v : Value τ} → Validᴴ μ →  Validⱽ (suc ∥ μ ∥ᴴ) v → Validᴴ (snocᴴ μ v)
snoc-validᴴ′ {μ = μ} {v} isV isVⱽ {n} ∈₁ with split-lookup μ v ∈₁
snoc-validᴴ′ {μ = μ} isV isVⱽ {n} ∈₁ | inj₁ ∈' = wken-valid _ snoc-≤ (isV ∈')
snoc-validᴴ′ {μ = μ} {v} isV isVⱽ {n} ∈₁ | inj₂ (refl , refl) rewrite ∥snoc∥ μ v = isVⱽ
