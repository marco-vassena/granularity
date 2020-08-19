open import Lattice
open import Data.Nat
open import Generic.Valid

module Generic.Memory.Valid
   {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set)
--   (Validⱽ : ∀ {τ} → ℕ → Value τ  → Set)
  {{𝑽 : IsValid Value}} where


open import Generic.Memory.Base Ty Value
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Generic.Container.Valid Label Ty Value -- (λ n v → ∥ v ∥ⱽ ≤ n)
  renaming ( Validᶜ to Validᴹ
           ; read-valid to read-validᴿ
           ; snoc-valid to snoc-validᴹ
           ; write-valid to write-validᴹ
           ; tail-valid to tail-validᴹ
           ;  IsValidᶜ to IsValidᴹ
           ; valid-≤ᶜ to valid-≤ᴹ
           ; wken-validᶜ to wken-validᴹ
           ; ∥_∥ᶜ to ∥_∥ᴹ ) public

-- Validᴹ : ∀ {ℓ} → ℕ → Memory ℓ → Set
-- Validᴹ n [] = ⊤
-- Validᴹ n (v ∷ M) = ∥ v ∥ⱽ ≤ n × Validᴹ n M

-- Validᴹ : ∀ {ℓ} → ℕ → Memory ℓ → Set
-- Validᴹ = {!!}

-- Validᴹ
