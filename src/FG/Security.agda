-- This module proves security of FG, i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security level A ∈ 𝓛.

open import Lattice hiding (_≟_)

module FG.Security {{𝑳 : Lattice}} (A : Label) where

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product renaming (_,_ to _∧_) hiding (,_)
open import Data.Nat hiding (_^_)

-- FG Definitions
open import FG.Types hiding (_×_) renaming (_⊆_ to _⊆ᶜ_) hiding (refl-⊆)
open import FG.Syntax hiding (_∘_ )
open import FG.Semantics
open import Generic.Bijection as B hiding (_∈_)
open import FG.LowEq A public

-- Valid assumptions
open import FG.Valid
open import Generic.Valid
open IsValid isValidᴱ
open Validᴾ

step-≈ᴾ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , μ , _ ⟩ = c
                 ⟨ Σ' , μ' , _ ⟩ = c' in
                 {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩

step-≈ᴾ (Var τ∈Γ x) pc⋤A = refl-≈ᴾ

step-≈ᴾ Unit pc⋤A = refl-≈ᴾ

step-≈ᴾ (Lbl ℓ) pc⋤A = refl-≈ᴾ

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Test₁ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′}} {{isVᴱ′}} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Test₂ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ′′ ∧ isVᴾ′ ∧ isVᴱ′ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′′ }} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ Fun pc⋤A = refl-≈ᴾ

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (App x₁ x₂ refl x₃) pc⋤A =
  let isV₁ᴱ ∧ isVᴾ′ ∧ isVᴱ′ = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      _ ∧ isVᴾ′′ ∧ isVⱽ = valid-invariant x₂ (isVᴾ′ ∧ isV₁ᴱ)
      ≈ᴾ′ = step-≈ᴾ x₁ pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isV₁ᴱ }} x₂ pc⋤A
      isVᴱ′′ = wken-valid _ (step-≤ x₂) isVᴱ′
      ≈ᴾ′′′ = step-≈ᴾ {{ isVᴾ′′ }} {{  isVⱽ ∧ isVᴱ′′  }} x₃ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ≈ᴾ′′′)

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Wken p x) pc⋤A = step-≈ᴾ {{ isVᴾ }} {{ slice-validᴱ _ p isVᴱ }} x pc⋤A

step-≈ᴾ (Inl x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (Inr x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Case₁ x₁ refl x₂) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ = valid-invariant x₁ (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x₁ pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVⱽ ∧ isVᴱ′ }} x₂ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Case₂ x refl x₁) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ isVⱽ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVⱽ ∧ isVᴱ′ }} x₁ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Pair x x₁) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ (Fst x refl) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (Snd x x₁) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (LabelOf x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ GetLabel pc⋤A = refl-≈ᴾ

step-≈ᴾ {{ isVᴾ }} {{isVᴱ}} (Taint refl x x₁ pc'⊑pc'') pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ (join-⋤₁ pc⋤A)
  in trans-≈ᴾ-ι ≈ᴾ′ ≈ᴾ′′

step-≈ᴾ (LabelOfRef x eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (New x) pc⋤A =
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴾ x pc⋤A
      _ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      ≈ˢ′ = updateᴴ-≈ˢ {{ isVˢ′ }} (trans-⋤ (step-⊑ x) pc⋤A) in
      ⟨ trans-≈ˢ-ι (step-≤ x) ≈ˢ ≈ˢ′ , ≈ᴴ ⟩

step-≈ᴾ (Read x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Write x ⊑₁ x₁ ⊑₂ w) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      isVᴱ′′ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x₁ (isVᴾ′ ∧ isVᴱ′)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
      ℓ⋤A = trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A
      ≈ᴾ′′′ = ⟨ updateᴴ-≈ˢ {{ isVˢ′ }} ℓ⋤A , refl-≈ᴴ {{ isVᴴ′ }} ⟩
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ≈ᴾ′′′)

step-≈ᴾ (LabelOfRef-FS x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

-- TODO: Do we need all of them implicits?
step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (New-FS x) pc⋤A =
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴾ {{ isVᴾ }} {{isVᴱ}} x pc⋤A
      isVᴾ′ ∧ _ = validᴾ-⇓ x (isVᴾ ∧ isVᴱ)
      ≈ˢ′ = trans-≈ˢ-ι (step-≤ x) ≈ˢ (refl-≈ˢ {{ validˢ isVᴾ′ }}) in
      ⟨ ≈ˢ′ , snoc-≈ᴴ _ ≈ᴴ ⟩

step-≈ᴾ (Read-FS x x₁ eq) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ {{isVᴾ}} {{isVᴱ}} (Write-FS x x₁ ∈₁ ⊑₁ refl w) pc⋤A =
  let isVᴱ′ ∧ isVᴾ′ ∧ _ = valid-invariant x (isVᴾ ∧ isVᴱ)
      isVᴱ′′ ∧ isVᴾ′′ ∧ _ = valid-invariant x₁ (isVᴾ′ ∧ isVᴱ′)
      ≈ᴾ′ = step-≈ᴾ x pc⋤A
      ≈ᴾ′′ = step-≈ᴾ {{ isVᴾ′ }} {{ isVᴱ′ }} x₁ pc⋤A
      v≈ = Valueᴴ (trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A) (join-⋤₁ (trans-⋤ (step-⊑ x) pc⋤A))
      ≈ᴾ′′′ = writeᴴ-≈ᴴ {{ validᴴ isVᴾ′′ }} ∈₁ w v≈
  in trans-≈ᴾ-ι ≈ᴾ′ (trans-≈ᴾ-ι ≈ᴾ′′ ⟨ refl-≈ˢ {{ validˢ isVᴾ′′ }} , ≈ᴾ′′′ ⟩)
  where open Validᴾ

step-≈ᴾ (Id x) pc⋤A = step-≈ᴾ x pc⋤A

step-≈ᴾ (UnId x eq) pc⋤A = step-≈ᴾ x pc⋤A

wken-∃ : ∀ {τ β β'} {c₁ c₂ : FConf τ} →
         β ⊆ β' → (x : ∃ (λ β'' → β' ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)) →
         ∃ (λ β'' → β ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)
wken-∃ β⊆β' (β'' ∧ β'⊆β'' ∧ ≈₁)  = β'' ∧ (trans-⊆ β⊆β' β'⊆β'') ∧ ≈₁

mutual

  -- TINI for low steps
  tiniᴸ : ∀ {pc β τ Γ μ₁ μ₂ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , e ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , e ⟩ in
                    {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
                    θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                    pc ⊑ A →
                    ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')

  tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
    where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  tiniᴸ Unit Unit ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ (Lbl ℓ) (Lbl .ℓ) ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  --------------------------------------------------------------------------------
  -- Test cases

  -- Both true
  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨  ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ isV₁ }} {{ validᴾ-⇓ y₁ isV₂ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ isV₁ }} {{ validᴾ-⇓ y₁ isV₂ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... |  β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

    -- True vs False
  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧  ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }}  x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- False vs True
  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ  {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- False and False
  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ _ (Lbl ℓ₁) ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }}  x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₂ ¬p₁) (join-⋤₂ ¬p₂) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) ≈ᴾ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩
    with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴴ (join-⋤₁ pc⋤ℓ₁') (join-⋤₁ pc⋤ℓ₂') ⟩

  -- End Test Cases
  --------------------------------------------------------------------------------

  tiniᴸ Fun Fun ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  --------------------------------------------------------------------------------
  -- App Cases

  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ eq₁ x₃) (App y₁ y₂ eq₂ y₃) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ with valid-invariant x₁ ( isV₁) | valid-invariant y₁ (isV₂)
  ... | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    with tiniᴸ {{ isV₁ᴾ′ ∧ isV₁ᴱ′ }} {{ isV₂ᴾ′ ∧ isV₂ᴱ′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ≈) pc⊑A

  -- Public closure
  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ refl x₃) (App y₁ y₂ refl y₃) ≈ᴾ θ≈ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑ℓ' (Fun θ≈′) ⟩ | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₁'≈v₂' ⟩
       = let _ ∧ isV₁ᴾ′′ ∧ isV₁ⱽ = valid-invariant x₂ (isV₁ᴾ′ ∧ isV₁ᴱ′)
             _ ∧ isV₂ᴾ′′ ∧ isV₂ⱽ = valid-invariant y₂ (isV₂ᴾ′ ∧ isV₂ᴱ′)
             vi₁ = isV₁ᴾ′′ ∧ (isV₁ⱽ ∧ wken-valid _ (step-≤ x₂) isV₁ᴱ′′)
             vi₂ = isV₂ᴾ′′ ∧ (isV₂ⱽ ∧ wken-valid _ (step-≤ y₂) isV₂ᴱ′′)
             θ≈′′ = v₁'≈v₂' ∷ wken-≈ᴱ β'⊆β'' θ≈′
             ≈₁ = tini {{ vi₁ }} {{ vi₂ }} x₃ y₃  ⟨ ≈ᴾ′′ , refl ⟩ θ≈′′  in
             wken-∃ (trans-⊆ β⊆β' β'⊆β'') ≈₁


  -- Secret closure
  tiniᴸ {{isV₁}} {{isV₂}} (App x₁ x₂ refl x₃) (App y₁ y₂ refl y₃) ≈ᴾ θ≈ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ᴱ′′ | isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ᴱ′′
    | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₁'≈v₂' ⟩
      = let _ ∧ isV₁ᴾ′′ ∧ isV₁ⱽ = valid-invariant x₂ (isV₁ᴾ′ ∧ isV₁ᴱ′)
            _ ∧ isV₂ᴾ′′ ∧ isV₂ⱽ = valid-invariant y₂ (isV₂ᴾ′ ∧ isV₂ᴱ′)
            vi₁ = (isV₁ᴾ′′ ∧ isV₁ⱽ ∧ wken-valid _ (step-≤ x₂) isV₁ᴱ′′)
            vi₂ = (isV₂ᴾ′′ ∧ isV₂ⱽ ∧ wken-valid _ (step-≤ y₂) isV₂ᴱ′′)
            ≈₁ = tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′′ x₃ y₃ (join-⋤₂ pc⋤ℓ₁) (join-⋤₂ pc⋤ℓ₂) in
            wken-∃ (trans-⊆ β⊆β' β'⊆β'') ≈₁

  -- End App Cases
  --------------------------------------------------------------------------------

  tiniᴸ {{ isV₁ᴾ ∧ isV₁ᴱ }} {{ isV₂ᴾ ∧ isV₂ᴱ}} (Wken p x) (Wken .p y) ≈ᴾ θ≈ pc⊑A =
    let θ≈′ = slice-≈ᴱ θ≈ p
        isV₁ᴱ′ = slice-validᴱ _ p isV₁ᴱ
        isV₂ᴱ′ = slice-validᴱ _ p isV₂ᴱ in
        tiniᴸ {{ isV₁ᴾ ∧ isV₁ᴱ′ }} {{ isV₂ᴾ ∧ isV₂ᴱ′ }} x y ≈ᴾ θ≈′ pc⊑A

  tiniᴸ (Inl x) (Inl x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ =  β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  tiniᴸ (Inr x) (Inr x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩


  --------------------------------------------------------------------------------
  -- Case inspection

  -- Both left
  tiniᴸ {{isV₁}} {{isV₂}} (Case₁ x₁ refl x₂) (Case₁ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Inl v≈) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′
        θ≈′ = v≈ ∷ wken-≈ᴱ β⊆β' θ≈  in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ θ≈′)

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- Left vs right
  tiniᴸ {{isV₁}} {{isV₂}} (Case₁ x₁ refl x₂) (Case₂ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A () ⟩   -- Public scrutinee with different injections (impossible)
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)) -- Secret scrutinee

  -- Right vs left (like above)
  tiniᴸ {{isV₁}} {{isV₂}} (Case₂ x₁ refl x₂) (Case₁ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A () ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)) -- Secret scrutinee

  -- Both right
  tiniᴸ {{isV₁}} {{isV₂}} (Case₂ x₁ refl x₂) (Case₂ y₁ refl y₂) ≈ᴾ θ≈ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ≈ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Inr v≈) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′
        θ≈′ = v≈ ∷ wken-≈ᴱ β⊆β' θ≈  in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ θ≈′)


  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = isV₁ᴾ′ ∧ isV₁ⱽ ∧ isV₁ᴱ′
        vi₂ = isV₂ᴾ′ ∧ isV₂ⱽ ∧ isV₂ᴱ′ in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- End case inspection cases
  --------------------------------------------------------------------------------

  tiniᴸ {{isV₁}} {{isV₂}} (Pair x₁ x₂) (Pair y₁ y₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v₁≈v₁' ⟩ with tiniᴸ {{ validᴾ-⇓ x₁ ( isV₁) }} {{ validᴾ-⇓ y₁ (isV₂) }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ≈ᴾ′′ , v₂≈v₂' ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ≈ᴾ′′ , Valueᴸ pc⊑A (Pair (wken-≈ⱽ β'⊆β'' v₁≈v₁') v₂≈v₂') ⟩

  tiniᴸ (Fst x refl) (Fst x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (Snd x refl) (Snd x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOf x) (LabelOf x₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Lbl _) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  tiniᴸ GetLabel GetLabel ≈ᴾ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ≈ᴾ , Valueᴸ pc⊑A (Lbl _) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (Taint refl x₁ x₂ ⊑₁) (Taint refl y₁ y₂ ⊑₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Lbl ℓ) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = (isV₁ᴾ′ ∧ isV₁ᴱ′)
        vi₂ = (isV₂ᴾ′ ∧ isV₂ᴱ′) in
        wken-∃ β⊆β' (tini {{ vi₁ }} {{ vi₂ }} x₂ y₂ ⟨ ≈ᴾ′ , refl ⟩ (wken-≈ᴱ β⊆β' θ₁≈θ₂))

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =
    let isV₁ᴱ′ ∧ isV₁ᴾ′ ∧ isV₁ⱽ = valid-invariant x₁ (isV₁)
        isV₂ᴱ′ ∧ isV₂ᴾ′ ∧ isV₂ⱽ = valid-invariant y₁ (isV₂)
        vi₁ = (isV₁ᴾ′ ∧ isV₁ᴱ′)
        vi₂ = (isV₂ᴾ′ ∧ isV₂ᴱ′) in
        wken-∃ β⊆β' (tiniᴴ {{ vi₁ }} {{ vi₂ }} ≈ᴾ′ x₂ y₂ (trans-⋤ ⊑₁ ℓ₁⋤A) (trans-⋤ ⊑₂ ℓ₂⋤A))


  tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ⊑A₁) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A) ⟩

  tiniᴸ {{isV₁}} {{isV₂}} (New x₁) (New y₁) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴴ ⋤₁ ⋤₂  ⟩ =
    let isV₁ᴾ′ ∧ _  = validᴾ-⇓ x₁ isV₁
        isV₂ᴾ′ ∧ _  = validᴾ-⇓ y₁ isV₂
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′ }} ⋤₁
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′ }} ⋤₂
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι
        v≈′ = Valueᴸ pc⊑A (Ref-Iᴴ ⋤₁ ⋤₂) in
        β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , v≈′ ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A r≈ ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , v≈′ ⟩
      where M≈ = getᴸ Σ≈ ℓ⊑A
            Σ≈′ = updateᴸ-≈ˢ Σ≈ (new-≈ᴹ M≈  r≈)
            v≈′ = Valueᴸ pc⊑A (Ref-Iᴸ′ ℓ⊑A ∥ M≈ ∥-≡)

  -- Read public reference
  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩
       where M≈ = getᴸ Σ≈ ℓ'⊑A
             v≈ = Valueᴸ (join-⊑' ℓ'⊑A ℓ⊑A) (read-≈ᴹ M≈ n∈M₁ n∈M₂)

  -- Read secret reference.
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)

  -- Read secret-dependent reference
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ {{isV₁}} {{isV₂}} (Write x₁ ⊑₁ x₂ ℓ₂⊑ℓ w₁) (Write y₁ ⊑₂ y₂ ℓ₂⊑ℓ' w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    with  validᴾ-⇓ x₁ isV₁ | validᴾ-⇓ y₁ isV₂ | tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A

  -- Write low-data to a secret-dependent reference
  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩  , v≈ ⟩ =
    let isV₁ᴾ′′ ∧ _  = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _  = validᴾ-⇓ y₂ isV₂′
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′′ }} (trans-⋤ ⊑₁ ℓ₁⋤A)
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′′ }} (trans-⋤ ⊑₂ ℓ₂⋤A)
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  -- Write low data to low reference
  tiniᴸ {{isV₁}} {{isV₂}} (Write x₁ ℓ'⊑ℓ x₂ ℓ₂⊑ℓ w₁) (Write y₁ ℓ'⊑ℓ' y₂ ℓ₂⊑ℓ' w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β'  ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴸ ⊑₁) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
      where M≈ = getᴸ Σ≈ ⊑₁
            Σ≈′ = updateᴸ-≈ˢ Σ≈ (update-≈ᴹ M≈ (extract-≈ᴿ v≈ (trans-⊑ ℓ₂⊑ℓ ⊑₁)) w₁ w₂)

  -- Write low data to high reference
  tiniᴸ  {{isV₁}} {{isV₂}} (Write x₁ ⊑₁ x₂ ⊑₁′ w₁) (Write y₁ ⊑₂ y₂ ⊑₂′ w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β'  ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Ref-Iᴴ ⋤₁ ⋤₂) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ =
    let isV₁ᴾ′′ ∧ _  = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _  = validᴾ-⇓ y₂ isV₂′
        Σ₁≈ = updateᴴ-≈ˢ {{ validˢ isV₁ᴾ′′ }} ⋤₁
        Σ₂≈ = updateᴴ-≈ˢ {{ validˢ isV₂ᴾ′′ }} ⋤₂
        Σ≈′ = square-≈ˢ-ι Σ≈ Σ₁≈ Σ₂≈ ⊆ᴿ-ι ⊆ᴰ-ι in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈′ , μ≈ ⟩ , Valueᴸ pc⊑A Unit ⟩
    where open _≈⟨_⟩ᴴ_ μ≈

  tiniᴸ (Id x₁) (Id x₂) ≈ᴾ θ₁≈θ₂ pc⊑A with  tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ pc⊑A (Id v≈) ⟩

  tiniᴸ (UnId x₁ refl) (UnId x₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴸ ℓ⊑A (Id v≈) ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , ≈ⱽ-⊑ _ v≈ ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOfRef-FS x₁ ∈₁ refl) (LabelOfRef-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-S ∈β') ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩
    where v≈ = ≈ⱽ-⊑ _ (label-of-≈ⱽ (readᴸ-≈ⱽ ∈β' ∈₁ ∈₂ μ≈))
  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (New-FS {μ' = μ₁'} x₁) (New-FS {μ' = μ₂'} x₂) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ ⟨ ⟨ wken-≈ˢ ⊆₁ Σ≈ , μ≈′ ⟩ , wken-≈ⱽ ⊆₂ v≈′ ⟩
      where
        instance _ = _≟_
                 _ = ≈-# μ≈
        β₁ =  ∥ μ₁' ∥ᴴ ↔ ∥ μ₂' ∥ᴴ
        β'' = β' ∣ᴮ β₁
        ⊆₁ = ∣ᴮ-⊆₁ β' β₁
        ⊆₂ = ∣ᴮ-⊆₂ β' β₁
        β⊆β'' = trans-⊆ β⊆β' ⊆₁
        μ≈′ = newᴸ-≈ᴴ v≈ μ≈
        v≈′ = Valueᴸ pc⊑A (Ref-S (↔-∈ᵗ ∥ μ₁' ∥ᴴ ∥ μ₂' ∥ᴴ))

  tiniᴸ (Read-FS x₁ ∈₁ refl) (Read-FS x₂ ∈₂ refl) ≈ᴾ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A

  ... | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , v≈ ⟩
    where v≈ = Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A)

  ... | β' ∧ β⊆β' ∧ ⟨  ⟨ Σ≈ , μ≈ ⟩ , Valueᴸ ℓ⊑A (Ref-S ∈β) ⟩ = β' ∧ β⊆β' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , ≈ⱽ-⊑ _ v≈ ⟩
       where v≈ = readᴸ-≈ⱽ ∈β ∈₁ ∈₂ μ≈

  tiniᴸ  {{isV₁}} {{isV₂}} (Write-FS x₁ x₂ ∈₁ ⊑₁ refl w₁) (Write-FS y₁ y₂ ∈₂ ⊑₂ refl w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    with  validᴾ-⇓ x₁ (isV₁) | validᴾ-⇓ y₁ (isV₂) | tiniᴸ x₁ y₁ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴸ ℓ⊑A (Ref-S ∈β')) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈′ ⟩ =
            let ∈β'' = bij-⊆ β'⊆β'' ∈β'
                v≈ = readᴸ-≈ⱽ ∈β'' ∈₁ ∈₂ μ≈
                μ≈′ = writeᴸ-≈ᴴ μ≈ (≈ⱽ-⊑ _ v≈′) w₁ w₂ ∈β'' in
                β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈′ ⟩ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ  {{isV₁}} {{isV₂}} (Write-FS x₁ x₂ ∈₁ ⊑₁ refl w₁) (Write-FS y₁ y₂ ∈₂ ⊑₂ refl w₂) ≈ᴾ θ₁≈θ₂ pc⊑A
    | isV₁′ | isV₂′ | β' ∧ β⊆β' ∧ ⟨ ≈ᴾ′ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩
    with tiniᴸ {{ isV₁′ }} {{ isV₂′ }} x₂ y₂ ≈ᴾ′ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈ ⟩ , v≈ ⟩ =
    let v≈₁ = Valueᴴ (trans-⋤ ⊑₁ ℓ₁⋤A) (join-⋤₁ ℓ₁⋤A)
        v≈₂ = Valueᴴ (trans-⋤ ⊑₂ ℓ₂⋤A) (join-⋤₁ ℓ₂⋤A)
        isV₁ᴾ′′ ∧ _ = validᴾ-⇓ x₂ isV₁′
        isV₂ᴾ′′ ∧ _ = validᴾ-⇓ y₂ isV₂′
        μ≈₁ = writeᴴ-≈ᴴ {{ validᴴ isV₁ᴾ′′ }} ∈₁ w₁ v≈₁
        μ≈₂ = writeᴴ-≈ᴴ {{ validᴴ isV₂ᴾ′′ }} ∈₂ w₂ v≈₂
        μ≈′ = square-≈ᴴ-ι μ≈  μ≈₁ μ≈₂ in
        β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ ⟨ Σ≈ , μ≈′ ⟩ , Valueᴸ pc⊑A Unit ⟩

  -- TINI for high steps. The computations depend on a secret and thus
  -- might produce different results and code. We then prove TINI by
  -- showing that the program counter can only remain secret and that
  -- each high step preserves low-equivalence of stores and heaps.  In
  -- particular we prove that the final program state  are low-equivalent (p₁'
  -- ≈ p₂'), i.e., the square:
  --
  -- p₁ ≈ᴾ p₁'
  -- ≈ᴾ    ≈ᴾ
  -- p₂ ≈ᴾ p₂'
  --
  -- using transitivity and symmetry of ≈ᴾ
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂ β} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
             let ⟨ Σ₁ , μ₁ , _ ⟩ = c₁
                 ⟨ Σ₂ , μ₂ , _ ⟩ = c₂ in
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
             c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
             pc₁ ⋤ A → pc₂ ⋤ A →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tiniᴴ {β = β} {{isV₁ᴾ ∧ isV₁ᴱ}} {{isV₂ᴾ  ∧ isV₂ᴱ}}
         ≈ᴾ x₁ x₂ pc₁⋤A pc₂⋤A =
    let ≈₁ᴾ = step-≈ᴾ {{ isV₁ᴾ }} {{ isV₁ᴱ }} x₁ pc₁⋤A
        ≈₂ᴾ = step-≈ᴾ {{ isV₂ᴾ }} {{ isV₂ᴱ }} x₂ pc₂⋤A
        ≈ᴾ′ = square-≈ᴾ-ι ≈ᴾ ≈₁ᴾ ≈₂ᴾ
        v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A) in
        β ∧ B.refl-⊆ ∧ ⟨ ≈ᴾ′ , v≈ ⟩

  -- TINI: top level theorem
  tini : ∀ {τ Γ θ₁ θ₂ pc β} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
             c₁ ≈⟨ β ⟩ᴵ c₂ →
             θ₁ ≈⟨ β ⟩ᴱ θ₂ →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tini {pc = pc} x₁ x₂ ⟨ ≈ᴾ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ ≈ᴾ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ ≈ᴾ x₁ x₂ pc⋤A pc⋤A
