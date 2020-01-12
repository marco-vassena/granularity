open import Lattice
open import Generic.LValue

module Generic.Heap.Lemmas
  {{𝑳 : Lattice}}
  {Ty : Set}
  {Value : Ty → Set}
  (𝑯 : HasLabel Ty Value) where

open import Generic.Heap.Base 𝑯
open import Data.Unit
open import Generic.Container.Lemmas ⊤ Ty LValue public

open HasLabel 𝑯
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

snocᴴ-⋤ : ∀ {ℓ τ} (μ : Heap) (v : LValue τ) → (label v) ⋤ ℓ → ((snocᴴ μ v) ↓⊑ ℓ) ≡ (μ ↓⊑ ℓ)
snocᴴ-⋤ {ℓ} [] v ⋤ℓ with label v ⊑? ℓ
... | yes ⊑ℓ =  ⊥-elim (⋤ℓ ⊑ℓ)
... | no _ = refl
snocᴴ-⋤ {ℓ} (x ∷ μ) v ⋤ℓ with label x ⊑? ℓ
... | yes _ rewrite snocᴴ-⋤ μ v ⋤ℓ = refl
... | no _ rewrite snocᴴ-⋤ μ v ⋤ℓ = refl

-- {-# REWRITE snocᴴ-⋤ #-}  -- Not accepted ... probably a bug in Agda
