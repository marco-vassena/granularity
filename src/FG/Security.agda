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

-- TODO: trans-⋤ (join-⊑ ...) proofs are simplified by join-⋤₁

step-≈ˢ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , _ ⟩ = c
                 ⟨ Σ' , _ ⟩ = c' in
                {{validˢ : Validˢ Σ}} {{validᴱ : Validᴱ Σ θ}} →
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               Σ ≈⟨ ι ∥ Σ ∥ ⟩ˢ Σ'
step-≈ˢ {{isV₁}} {{isV₂}} (Var τ∈Γ x) pc⋤A = refl-≈ˢ {{isV₁}}
step-≈ˢ {{isV₁}} {{isV₂}} Unit pc⋤A = refl-≈ˢ {{isV₁}}
step-≈ˢ {{isV₁}} {{isV₂}} (Lbl ℓ) pc⋤A = refl-≈ˢ {{isV₁}}

step-≈ˢ {{isV₁}} {{isV₂}} (Test₁ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} (Test₂ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} Fun pc⋤A = refl-≈ˢ {{isV₁}}
step-≈ˢ {{isV₁}} {{isV₂}} (App {θ' = θ'} x x₁ refl x₃) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
      isVᴱ′′ = validᴱ-⊆ {θ = θ'} (step-⊆ x₁) isV₂′
      Σ₂⊆Σ₃ = step-≈ˢ {{ isV₁′′ }} {{ isV₂′′ ∧ isVᴱ′′ }} x₃ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂⊆Σ₃)

step-≈ˢ {{isV₁}} {{isV₂}} (Wken p x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ validᴱ-⊆ᶜ p isV₂ }} x pc⋤A

step-≈ˢ {{isV₁}} {{isV₂}} (Inl x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

step-≈ˢ {{isV₁}} {{isV₂}} (Inr x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

step-≈ˢ {{isV₁}} {{isV₂}} (Case₁ x refl x₁) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} (Case₂ x refl x₁) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} (Pair x x₁) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} (Fst x refl) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A

step-≈ˢ {{isV₁}} {{isV₂}} (Snd x x₁) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} (LabelOf x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} GetLabel pc⋤A = refl-≈ˢ {{isV₁}}
step-≈ˢ {{isV₁}} {{isV₂}} (Taint refl x x₁ pc'⊑pc'') pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ˢ-ι Σ⊆Σ₁ Σ₁⊆Σ₂

step-≈ˢ {{isV₁}} {{isV₂}} (LabelOfRef x eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} (New x) pc⋤A = snoc-≈ˢ _ (step-≈ˢ {{isV₁}} {{isV₂}} x pc⋤A)
step-≈ˢ {{isV₁}} {{isV₂}} (Read x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} (Write {ℓ = ℓ} {n = n} {τ = τ} x ⊑₁ x₁ ⊑₂ w) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
      ref ∧ ∈₂ = validᴿ-⊆ {r = Refᴵ {τ = τ} ℓ n} (step-⊆ x₁) isV₂′
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
      ℓ⋤A = trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A
      c≈c' = S.⌞ S.cellᴴ ℓ⋤A  ℓ⋤A ⌟
      Σ₂≈Σ₃ = writeᴴ-≈ˢ {{ isV₁′′  }} ∈₂ w c≈c'
  in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂≈Σ₃)

step-≈ˢ {{isV₁}} {{isV₂}} (LabelOfRef-FS x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} (New-FS x) pc⋤A = snoc-≈ˢ _ (step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A)
step-≈ˢ {{isV₁}} {{isV₂}} (Read-FS x x₁ eq) pc⋤A = step-≈ˢ {{ isV₁ }} x pc⋤A

step-≈ˢ {{isV₁}} {{isV₂}} (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x x₁ ∈₁ ⊑₁ refl w) pc⋤A =
  let isVᴱ ∧ isV₁′ ∧ isV₂′ = valid-invariant x ⟨ isV₁ , isV₂ ⟩
      isVᴱ′ ∧ isV₁′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isV₁′ , isVᴱ ⟩
      Σ⊆Σ₁ = step-≈ˢ {{ isV₁ }} x pc⋤A
      Σ₁⊆Σ₂ = step-≈ˢ {{ isV₁′ }} {{ isVᴱ }} x₁ pc⋤A
      c≈c' = S.⌞ S.cellᴴ (trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A) (join-⋤₁ (trans-⋤ (step-⊑ x) pc⋤A)) ⌟
      Σ₂≈Σ₃ = writeᴴ-≈ˢ {{ isV₁′′ }} ∈₁ w c≈c'
  in trans-≈ˢ-ι Σ⊆Σ₁ (trans-≈ˢ-ι Σ₁⊆Σ₂ Σ₂≈Σ₃ )

step-≈ˢ {{isV₁}} {{isV₂}} (Id x) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A
step-≈ˢ {{isV₁}} {{isV₂}} (UnId x eq) pc⋤A = step-≈ˢ {{ isV₁ }} {{ isV₂ }} x pc⋤A

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
  tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
    where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  tiniᴸ Unit Unit Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ (Lbl ℓ) (Lbl .ℓ) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  -- Both true
  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨  Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... |  β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

    -- True vs False
  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧  ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- False vs True
  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | _ ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | _ ∧ _ ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- False and False
  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , v≈ ⟩
    = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  tiniᴸ Fun Fun Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₄ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ with tiniᴸ x₁ x₅ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , E.Valueᴸ pc⊑ℓ' (Fun θ₁'≈θ₂') ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ = wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tini {{ {!!} }} {{ {!!} }} x₃ x₇  ⟨ Σ₁''≈Σ₂'' , refl ⟩ (v₁'≈v₂' ∷ wken-≈ᴱ β'⊆β'' θ₁'≈θ₂' ))

  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , E.Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ =  wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tiniᴴ {{ {!!} }} {{ {!!} }} Σ₁''≈Σ₂'' x₃ x₇ (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₁) (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₂))

  tiniᴸ (Wken p x) (Wken .p x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂′ pc⊑A
    where θ₁≈θ₂′ = slice-≈ᴱ θ₁≈θ₂ p

  tiniᴸ (Inl x) (Inl x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ =  β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  tiniᴸ (Inr x) (Inr x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩

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

  tiniᴸ (Pair x x₁) (Pair x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ ⟨ Σ₁'≈Σ₂' , v₁≈v₁' ⟩ with tiniᴸ x₁ x₃ Σ₁'≈Σ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , v₂≈v₂' ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ₁''≈Σ₂'' , Valueᴸ pc⊑A (Pair (wken-≈ⱽ β'⊆β'' v₁≈v₁') v₂≈v₂') ⟩

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

  tiniᴸ  {pc = pc} {Σ₁ = Σ₁} {Σ₂ = Σ₂} (New {ℓ = ℓ₁} {τ = τ} {Σ' = Σ₁'} {r = r₁} x₁) (New {ℓ = ℓ₂} {Σ' = Σ₂'} {r = r₂} x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ E.⟨ Σ≈′ , v≈′ ⟩
      where instance _ = _≟_
                     _ = ≈-# Σ≈
            β₁ =  ∥ Σ₁' ∥ ↔ ∥ Σ₂' ∥
            β'' = β' ∣ᴮ β₁
            β'⊆β'' = ∣ᴮ-⊆₁ β' β₁
            β⊆β'' = trans-⊆ β⊆β' β'⊆β''
            Σ≈′ = newᴸ-≈ˢ (≈ⱽ-≈ᶜ v≈) Σ≈
            v≈′ = Valueᴸ pc⊑A (Ref-I′ (bij-⊆ (∣ᴮ-⊆₂ β' β₁) (↔-∈ᵗ ∥ Σ₁' ∥ ∥ Σ₂' ∥)) (wken-≈ⱽ β'⊆β'' v≈))

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨  Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A x) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
       where v≈ = ≈ᶜ-≈ⱽ (readᴸ-≈ᶜ x n∈M₁ n∈M₂ Σ≈)

  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩
    where v≈ = Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩
    where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)

  tiniᴸ (Write {ℓ = ℓ₁} x₁ ⊑₁ y₁ ℓ₂⊑ℓ w₁) (Write {ℓ = ℓ₂} x₂ ⊑₂ y₂ ℓ₂⊑ℓ' w₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A

  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ with tiniᴸ y₁ y₂ Σ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ E.⟨ Σ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ E.⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
    where
          postulate valid-ref₁ : Validᴿ _ (Refᴵ ℓ₁ _)
          postulate valid-ref₂ : Validᴿ _ (Refᴵ ℓ₂ _)
          c≈₁ = ⌞ cellᴴ (trans-⋤ ⊑₁ ℓ₁⋤A ) (trans-⋤ ⊑₁ ℓ₁⋤A) ⌟
          c≈₂ = ⌞ cellᴴ (trans-⋤ ⊑₂ ℓ₂⋤A ) (trans-⋤ ⊑₂ ℓ₂⋤A) ⌟
          Σ≈′′ = square-≈ˢ-ι Σ≈′ (writeᴴ-≈ˢ {{ {!!} }} (proj₂ valid-ref₁) w₁ c≈₁)
                                 (writeᴴ-≈ˢ {{ {!!} }} (proj₂ valid-ref₂) w₂ c≈₂)

  tiniᴸ (Write x₁ ℓ'⊑ℓ y₁ ℓ₂⊑ℓ w₁) (Write x₂ ℓ'⊑ℓ' y₂ ℓ₂⊑ℓ' w₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β'  ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴸ ⊑′ ∈β') ⟩ with tiniᴸ y₁ y₂ Σ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ E.⟨ Σ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
    where ∈β'' = bij-⊆ β'⊆β'' ∈β'
          Σ≈′′ = writeᴸ-≈ˢ Σ≈′ (≈ⱽ-≈ᶜ (Valueᴸ ⊑′ (extract-≈ᴿ v≈ (trans-⊑ ℓ₂⊑ℓ ⊑′)))) w₁ w₂ ∈β''

  tiniᴸ (Write x₁ ⊑₁ y₁ ⊑₁′ w₁) (Write x₂ ⊑₂ y₂ ⊑₂′ w₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | β' ∧ β⊆β'  ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴴ ⋤₁ ⋤₂) ⟩ with tiniᴸ y₁ y₂ Σ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ E.⟨ Σ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
      where postulate valid-ref₁ : Validᴿ _ (Refᴵ _ _)
            postulate valid-ref₂ : Validᴿ _ (Refᴵ _ _)
            c≈₁ = ⌞ cellᴴ ⋤₁ ⋤₁ ⌟
            c≈₂ = ⌞ cellᴴ ⋤₂ ⋤₂ ⌟
            Σ≈′′ = square-≈ˢ-ι Σ≈′ (writeᴴ-≈ˢ {{ {!!} }} (proj₂ valid-ref₁) w₁ c≈₁) (writeᴴ-≈ˢ {{ {!!} }} (proj₂ valid-ref₂) w₂ c≈₂)

  tiniᴸ (Id x₁) (Id x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with  tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴸ pc⊑A (E.Id v≈) ⟩

  tiniᴸ (UnId x₁ refl) (UnId x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Id v≈) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOfRef-FS x₁ ∈₁ refl) (LabelOfRef-FS x₂ ∈₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-S ∈β') ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩
    where v≈ = ≈ⱽ-⊑ _ (label-of≈ᶜ-≈ⱽ (readᴸ-≈ᶜ ∈β' ∈₁ ∈₂ Σ≈))
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (New-FS {Σ' = Σ₁'} x₁) (New-FS {Σ' = Σ₂'} x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ E.⟨ Σ≈′ , wken-≈ⱽ (∣ᴮ-⊆₂ β' β₁) v≈′ ⟩
      where instance _ = _≟_
                     _ = ≈-# Σ≈
            β₁ =  ∥ Σ₁' ∥ ↔ ∥ Σ₂' ∥
            β'' = β' ∣ᴮ β₁
            β'⊆β'' = ∣ᴮ-⊆₁ β' β₁
            β⊆β'' = trans-⊆ β⊆β' β'⊆β''
            Σ≈′ = newᴸ-≈ˢ (≈ⱽ-≈ᶜ v≈) Σ≈
            v≈′ = Valueᴸ pc⊑A (Ref-S (↔-∈ᵗ ∥ Σ₁' ∥ ∥ Σ₂' ∥)) -- (Ref-Iᴸ′ ℓ⊑A (proj₁ (↔-∈ ∥ Σ₁' ∥ ∥ Σ₂' ∥)))


  tiniᴸ (Read-FS x₁ ∈₁ refl) (Read-FS x₂ ∈₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , v≈ ⟩
    where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A ) ((trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A ))

  ... | β' ∧ β⊆β' ∧ E.⟨  Σ≈ , E.Valueᴸ ℓ⊑A (Ref-S ∈β) ⟩ = β' ∧ β⊆β' ∧ E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
       where v≈ = ≈ᶜ-≈ⱽ (readᴸ-≈ᶜ ∈β ∈₁ ∈₂ Σ≈)


  tiniᴸ (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x₁ y₁ ∈₁ ⊑₁ refl w₁) (Write-FS x₂ y₂ ∈₂ ⊑₂ refl w₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , (Valueᴸ ℓ⊑A (Ref-S ∈β')) ⟩ with tiniᴸ y₁ y₂ Σ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ E.⟨ Σ≈′ , v≈ ⟩ =
            let ∈β'' = bij-⊆ β'⊆β'' ∈β'
                c≈ = readᴸ-≈ᶜ ∈β'' ∈₁ ∈₂ Σ≈′
                Σ≈′′ = writeᴸ-≈ˢ Σ≈′ (≈ᶜ-⊑ ℓ (taint-update-≈ᶜ c≈ v≈)) w₁ w₂ ∈β'' in β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩

  tiniᴸ (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x₁ y₁ ∈₁ ⊑₁ refl w₁) (Write-FS x₂ y₂ ∈₂ ⊑₂ refl w₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A | β' ∧ β⊆β' ∧ E.⟨ Σ≈ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ with tiniᴸ y₁ y₂ Σ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  ... | β'' ∧ β'⊆β'' ∧ E.⟨ Σ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ E.⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
    where c≈₁ = ⌞ cellᴴ (trans-⋤ ⊑₁ ℓ₁⋤A) (join-⋤₁ ℓ₁⋤A) ⌟
          c≈₂ = ⌞ cellᴴ (trans-⋤ ⊑₂ ℓ₂⋤A) (join-⋤₁ ℓ₂⋤A) ⌟
          Σ≈′′ = square-≈ˢ-ι Σ≈′ (writeᴴ-≈ˢ {{ {!!} }} ∈₁ w₁ c≈₁) (writeᴴ-≈ˢ {{ {!!} }} ∈₂ w₂ c≈₂)


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
