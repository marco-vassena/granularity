-- This module proves security of FG, i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice hiding (_≟_)

module FG.Security {{𝑳 : Lattice}} (A : Label) where

open import FG.Types hiding (_×_) renaming (_⊆_ to _⊆ᶜ_) hiding (refl-⊆)
open import FG.Syntax hiding (_∘_)
open import FG.Semantics
open import FG.LowEq A as E public

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection as B hiding (_∈_)

import Generic.Store.LowEq {Ty} {Raw} _≈⟨_⟩ᴿ_ as S

--------------------------------------------------------------------------------
-- TODO: move this to FG LowEq module?
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-≈ⱽ : ∀ {τ Γ θ₁ θ₂ β} → (τ∈Γ : τ ∈ Γ) →
              θ₁ ≈⟨ β ⟩ᴱ θ₂ → (θ₁ !! τ∈Γ) ≈⟨ β ⟩ⱽ (θ₂ !! τ∈Γ)
lookup-≈ⱽ here (v₁≈v₂ ∷ θ₁≈θ₂) = v₁≈v₂
lookup-≈ⱽ (there τ∈Γ) (v₁≈v₂ ∷ θ₁≈θ₂) = lookup-≈ⱽ τ∈Γ θ₁≈θ₂


-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-≈ᴱ : ∀ {Γ₁ Γ₂ β} {θ₁ θ₂ : Env Γ₂} →
                 θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                 (Γ₁⊆Γ₂ : Γ₁ ⊆ᶜ Γ₂) →
                 slice θ₁ Γ₁⊆Γ₂ ≈⟨ β ⟩ᴱ slice θ₂ Γ₁⊆Γ₂
slice-≈ᴱ [] base = []
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (cons p) = v₁≈v₂ ∷ slice-≈ᴱ θ₁≈θ₂ p
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (drop p) = slice-≈ᴱ θ₁≈θ₂ p

--------------------------------------------------------------------------------

open import Data.Product renaming (_,_ to _∧_) hiding (,_)


open import FG.Valid
open import Generic.Store.Valid Ty Raw ∥_∥ᴿ as V
open Conf
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties

postulate step-≈ˢ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , _ ⟩ = c
                 ⟨ Σ' , _ ⟩ = c' in
                {{validˢ : Validˢ Σ}} {{validᴱ : Validᴱ Σ θ}} →
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               Σ ≈⟨ ι ∥ Σ ∥ ⟩ˢ Σ'
-- step-≈ˢ {{isV₁}} {{isV₂}} (Var τ∈Γ x) pc⋤A = refl-≈ˢ {{isV₁}}
-- step-≈ˢ {{isV₁}} {{isV₂}} Unit pc⋤A = refl-≈ˢ {{isV₁}}
-- step-≈ˢ {{isV₁}} {{isV₂}} (Lbl ℓ) pc⋤A = refl-≈ˢ {{isV₁}}

-- step-≈ˢ {{isV₁}} {{isV₂}} (Test₁ x x₁ ℓ⊑ refl) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} (Test₂ x x₁ ℓ⊑ refl) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} Fun pc⋤A = refl-≈ˢ {{isV₁}}
-- step-≈ˢ {{isV₁}} {{isV₂}} (App {θ' = θ'} x x₁ refl x₃) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--       isVᴱ′′ = validᴱ-⊆ {θ = θ'} (step-⊆ x₁) isV₂′
--       Σ₂⊆Σ₃ = step-≈ˢ {{ isV₁′′ }} {{ isV₂′′ ∧ isVᴱ′′ }} x₃ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
--   in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂⊆Σ₃)

-- step-≈ˢ {{isV₁}} {{isV₂}} (Wken p x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ validᴱ-⊆ᶜ p isV₂ }} x pc⋤A

-- step-≈ˢ {{isV₁}} {{isV₂}} (Inl x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

-- step-≈ˢ {{isV₁}} {{isV₂}} (Inr x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

-- step-≈ˢ {{isV₁}} {{isV₂}} (Case₁ x refl x₁) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} (Case₂ x refl x₁) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} (Pair x x₁) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} (Fst x refl) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A

-- step-≈ˢ {{isV₁}} {{isV₂}} (Snd x x₁) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} (LabelOf x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} GetLabel pc⋤A = refl-≈ˢ {{isV₁}}
-- step-≈ˢ {{isV₁}} {{isV₂}} (Taint refl x x₁ pc'⊑pc'') pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
--   in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

-- step-≈ˢ {{isV₁}} {{isV₂}} (LabelOfRef x eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} (New x) pc⋤A = snoc-≈ˢ (step-≈ˢ {{isV₁}} {{isV₂}} x pc⋤A)
-- step-≈ˢ {{isV₁}} {{isV₂}} (Read x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} (Write {ℓ = ℓ} {n = n} {τ = τ} x ⊑₁ x₁ ⊑₂ w) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
--       ref ∧ ∈₂ = validᴿ-⊆ {r = Refᴵ {τ = τ} ℓ n} (step-⊆ x₁) isV₂′
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--       ℓ⋤A = trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A
--       c≈c' = S.⌞ S.cellᴴ ℓ⋤A  ℓ⋤A ⌟
--       Σ₂≈Σ₃ = writeᴴ-≈ˢ {{ isV₁′′  }} ∈₂ w c≈c'
--   in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂≈Σ₃)

-- step-≈ˢ {{isV₁}} {{isV₂}} (LabelOfRef-FS x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} (New-FS x) pc⋤A = snoc-≈ˢ (step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A)
-- step-≈ˢ {{isV₁}} {{isV₂}} (Read-FS x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A

-- step-≈ˢ {{isV₁}} {{isV₂}} (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x x₁ ∈₁ ⊑₁ refl w) pc⋤A =
--   let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
--       isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
--       Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
--       Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
--       c≈c' = S.⌞ S.cellᴴ (trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A) (join-⋤₁ (trans-⋤ (step-⊑ x) pc⋤A)) ⌟
--       Σ₂≈Σ₃ = writeᴴ-≈ˢ {{ isV₁′′ }} ∈₁ w c≈c'
--   in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂≈Σ₃ )

-- step-≈ˢ {{isV₁}} {{isV₂}} (Id x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A
-- step-≈ˢ {{isV₁}} {{isV₂}} (UnId x eq) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

--------------------------------------------------------------------------------

open _≈⟨_,_⟩ᴬ_
open import Data.Unit hiding (_≟_)
open import Generic.Heap 𝑯
-- open SecurityLattice 𝑳
open import Generic.LValue
open HasLabel 𝑯 -- import Generic.LValue as H

wken-∃ : ∀ {τ β β'} {c₁ c₂ : FConf τ} →
         β ⊆ β' → (x : ∃ (λ β'' → β' ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)) →
         ∃ (λ β'' → β ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)
wken-∃ β⊆β' (β'' ∧ β'⊆β'' ∧ ≈₁)  = β'' ∧ (trans-⊆ β⊆β' β'⊆β'') ∧ ≈₁

mutual

  -- TINI for low steps
  tiniᴸ : ∀ {pc β τ Γ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ ,  e ⟩
                        c₂ = ⟨ Σ₂ ,  e ⟩ in
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
                    θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                    pc ⊑ A →
                    ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  -- tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
  --   where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  -- tiniᴸ Unit Unit Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A Unit ⟩

  -- tiniᴸ (Lbl ℓ) (Lbl .ℓ) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  -- -- Both true
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨  Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... |  β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  --   -- True vs False
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | _ ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | _ ∧ _ ∧  ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- -- False vs True
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | _ ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | _ ∧ _ ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- -- False and False
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- tiniᴸ Fun Fun Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₄ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ with tiniᴸ x₁ x₅ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , E.Valueᴸ pc⊑ℓ' (Fun θ₁'≈θ₂') ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ = wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tini {{ {!!} }} {{ {!!} }} x₃ x₇  ⟨ Σ₁''≈Σ₂'' , refl ⟩ (v₁'≈v₂' ∷ wken-≈ᴱ β'⊆β'' θ₁'≈θ₂' ))

  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , E.Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ =  wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁''≈Σ₂'' x₃ x₇ (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₁) (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₂))

  -- tiniᴸ (Wken p x) (Wken .p x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂′ pc⊑A
  --   where θ₁≈θ₂′ = slice-≈ᴱ θ₁≈θ₂ p

  -- tiniᴸ (Inl x) (Inl x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ =  β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  -- tiniᴸ (Inr x) (Inr x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩

  tiniᴸ (Case₁ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inl v₁≈v₂) ⟩ = wken-∃ β⊆β' (tini {{ {!!} }} {{ {!!} }} x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ wken-≈ᴱ β⊆β' θ₁≈θ₂))
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  tiniᴸ (Case₁ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  tiniᴸ (Case₂ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  tiniᴸ (Case₂ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inr v₁≈v₂) ⟩ = wken-∃ β⊆β' (tini {{ {!!} }} {{ {!!} }} x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ wken-≈ᴱ β⊆β' θ₁≈θ₂))
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- tiniᴸ (Pair x x₁) (Pair x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₁' ⟩ with tiniᴸ x₁ x₃ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₂≈v₂' ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , Valueᴸ pc⊑A (Pair (wken-≈ⱽ β'⊆β'' v₁≈v₁') v₂≈v₂') ⟩

  tiniᴸ (Fst x refl) (Fst x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (Snd x refl) (Snd x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOf x) (LabelOf x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Lbl _) ⟩
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl _) ⟩

  tiniᴸ (Taint refl x₁ x₂ pc'⊑pc'') (Taint refl x₃ x₄ pc'⊑pc''') Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , E.Valueᴸ ℓ⊑A (E.Lbl ℓ) ⟩ = wken-∃ β⊆β' ( tini {{ {!!} }} {{ {!!} }} x₂ x₄ ⟨ Σ₁'≈Σ₂' , refl ⟩ (wken-≈ᴱ β⊆β' θ₁≈θ₂))
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =  wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁'≈Σ₂' x₂ x₄ (trans-⋤ pc'⊑pc'' ℓ₁⋤A) (trans-⋤ pc'⊑pc''' ℓ₂⋤A))

  tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , (Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)) ⟩
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A) ⟩

  -- Maybe this two cases can be merged as long as the new cells are L-equiv
  tiniᴸ  {pc = pc} {Σ₁ = Σ₁} {Σ₂ = Σ₂} (New {ℓ = ℓ₁} {τ = τ} {Σ' = Σ₁'} {r = r₁} x₁) (New {ℓ = ℓ₂} {Σ' = Σ₂'} {r = r₂} x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈′ , r≈′ ⟩
      where Σ≈′ = newᴴ-≈ˢ Σ≈ ℓ₁⋤A ℓ₂⋤A
            r≈′ = Valueᴸ pc⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A)
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A r≈ ⟩ = β'' ∧ β⊆β'' ∧ E.⟨ Σ≈′ , wken-≈ⱽ (∣ᴮ-⊆₂ β' β₁) v≈′ ⟩
      where instance _ = _≟_
                     _ = ≈-# Σ≈
            β₁ =  ∥ Σ₁' ∥ ↔ ∥ Σ₂' ∥
            β'' = β' ∣ᴮ β₁
            β'⊆β'' = ∣ᴮ-⊆₁ β' β₁
            β⊆β'' = trans-⊆ β⊆β' β'⊆β''
            Σ≈′ = newᴸ-≈ˢ (cellᴸ ℓ⊑A r≈) Σ≈
            v≈′ = Valueᴸ pc⊑A (Ref-Iᴸ′ ℓ⊑A (proj₁ (↔-∈ ∥ Σ₁' ∥ ∥ Σ₂' ∥)))

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}
-- with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
--   ... | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A n) ⟩ = ? -- E.⟨ _ , Σ≈ , v≈ ⟩
--     -- where M≈ = getᴸ Σ≈ ℓ'⊑A
--     --       v≈ = Valueᴸ (join-⊑' ℓ'⊑A ℓ⊑A) (read-≈ᴹ M≈ n∈M₁ n∈M₂)

--   ... | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = E.⟨ _ , Σ≈ , v≈ ⟩
--     where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)

--   ... | E.⟨ _ , Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ _ , Σ≈ , v≈ ⟩
--     where v≈ = Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}
  -- with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A

  -- -- Write high reference in low context (impossible)
  -- ... | E.⟨ _ , Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ'⊑pc' pc⊑A))

  -- ... | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A r≈' ⟩ with tiniᴸ x₃ x₄ Σ≈ θ₁≈θ₂ pc⊑A

  -- -- Write low data to low-reference
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ | E.⟨ _ , Σ≈′ , E.Valueᴸ ℓ⊑A₂ r≈ ⟩
  --   = ? -- ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --     -- where M≈ = getᴸ Σ≈′ ℓ⊑A₁
  --     --       Σ≈′′ = updateᴸ-≈ˢ Σ≈′ (update-≈ᴹ M≈  r≈ M≔₁ M≔₂)

  -- Write high data to low-reference (impossible)
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ | E.⟨ _ , Σ≈′ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ₂⊑ℓ' ℓ⊑A₁))

  -- -- Write low data to high reference
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ _ , Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ | E.⟨ _ , Σ≈′ , v≈ ⟩ = ? -- ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --     -- where Σ≈′′ = square-≈ˢ Σ≈′ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)

  tiniᴸ (Id x₁) (Id x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with  tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴸ pc⊑A (E.Id v≈) ⟩

  tiniᴸ (UnId x₁ refl) (UnId x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Id v≈) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOfRef-FS x x₁ eq) (LabelOfRef-FS x₂ x₃ eq₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}

  tiniᴸ (New-FS x) (New-FS x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}

  tiniᴸ (Read-FS x x₁ eq) (Read-FS x₂ x₃ eq₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}

  tiniᴸ (Write-FS x x₁ x₂ x₃ eq x₄) (Write-FS x₅ x₆ x₇ x₈ eq₁ x₉) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = {!!}


  -- TINI for high steps. The computations depend on a secret and thus
  -- might produce different results and code. We then prove TINI by
  -- showing that the program counter can only remain secret and that
  -- each high step preserves low-equivalence of stores.  In
  -- particular we prove that the final stores are low-equivalent (Σ₁'
  -- ≈ Σ₂'), i.e., the square:
  --
  -- Σ₁ ≈ˢ Σ₁'
  -- ≈ˢ    ≈ˢ
  -- Σ₂ ≈ˢ Σ₂'
  --
  -- using transitivity and symmetry of ≈ˢ
  -- TODO: do the same for FS-Store
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂ β} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
             let ⟨ Σ₁ , _ ⟩ = c₁
                 ⟨ Σ₂ , _ ⟩ = c₂ in
             -- {{valid₁ᴵ : Validᴵ c₁}} {{validᴱ : Validᴱ ∥ Σ₁ ∥ θ₁}} →
             -- {{valid₂ᴵ : Validᴵ c₂}} {{valid₂ᴱ : Validᴱ ∥ Σ₂ ∥ θ₂}} →
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
             c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
             pc₁ ⋤ A → pc₂ ⋤ A →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  -- Do we actually need to prove β ⊆ β' ? Not clear from Banjaree proof if this is ever used.
  -- The only reason I can think of is that the theorem might be trivial if we choose β' = ∅
  -- because we do not need to take care of the references. Check this with Deepak.
  tiniᴴ {β = β} {{⟨ isV₁ˢ , isV₁ᴱ ⟩ }} {{⟨ isV₂ˢ , isV₂ᴱ ⟩ }}
         Σ₁≈Σ₂ x₁ x₂ pc₁⋤A pc₂⋤A =
    let Σ₁≈Σ₁' = step-≈ˢ {{ isV₁ˢ }} {{ isV₁ᴱ }} x₁ pc₁⋤A
        Σ₂≈Σ₂' = step-≈ˢ {{ isV₂ˢ }} {{ isV₂ᴱ }} x₂ pc₂⋤A
        Σ₁'≈Σ₂' = square-≈ˢ-ι Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'
        v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A) in
        β ∧ B.refl-⊆ ∧ ⟨ Σ₁'≈Σ₂' , v≈ ⟩


  -- TINI: top level theorem
  tini : ∀ {τ Γ θ₁ θ₂ pc β} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
             -- {{valid₁ᴵ : Validᴵ c₁}} {{validᴱ : Validᴱ ∥ store c₁ ∥ θ₁}} →
             -- {{valid₂ᴵ : Validᴵ c₂}} {{valid₂ᴱ : Validᴱ ∥ store c₂ ∥ θ₂}} →
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
             c₁ ≈⟨ β ⟩ᴵ c₂ →
             θ₁ ≈⟨ β ⟩ᴱ θ₂ →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  tini {pc = pc} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ Σ₁≈Σ₂ x₁ x₂ pc⋤A pc⋤A
