-- This module proves security of FG, i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice hiding (_≟_)

module FG.Security {{𝑳 : Lattice}} (A : Label) where

open import FG.Types hiding (_×_) renaming (_⊆_ to _⊆ᶜ_) hiding (refl-⊆)
open import FG.Syntax hiding (_∘_ )
open import FG.Semantics
open import FG.LowEq A public

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Generic.Bijection as B hiding (_∈_)

import Generic.Store.LowEq {Ty} {Raw} _≈⟨_⟩ᴿ_ as S

--------------------------------------------------------------------------------
-- TODO: move this to.FG LowEq module?
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

open Conf
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties

import Generic.Heap.Lemmas Ty Value as H

-- TODO: trans-⋤ (join-⊑ ...) proofs are simplified by join-⋤₁

-- TODO: rename high step
step-≈ᴴ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , μ , _ ⟩ = c
                 ⟨ Σ' , μ' , _ ⟩ = c' in
                {{validᴾ : Validᴾ ⟨ Σ , μ ⟩ }} {{validᴱ : Validᴱ ∥ μ ∥ᴴ θ}} →
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               ⟨ Σ , μ ⟩ ≈⟨ ι ∥ μ ∥ᴴ ⟩ᴾ ⟨ Σ' , μ' ⟩
-- TODO: helper data type? we probably always apply the same operations.
step-≈ᴴ {{isVᴾ}} {{isV₂}} (Var τ∈Γ x) pc⋤A = refl-≈ᴾ {{isVᴾ}}
step-≈ᴴ {{isVᴾ}} {{isV₂}} Unit pc⋤A = refl-≈ᴾ {{isVᴾ}}
step-≈ᴴ {{isVᴾ}} {{isV₂}} (Lbl ℓ) pc⋤A = refl-≈ᴾ {{isVᴾ}}

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Test₁ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Test₂ x x₁ ℓ⊑ refl) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} Fun pc⋤A = refl-≈ᴾ {{isVᴾ}}
step-≈ᴴ {{isVᴾ}} {{isV₂}} (App {θ' = θ'} x x₁ refl x₃) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      isVᴱ′ ∧ isVᴾ′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isVᴾ′ , isVᴱ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
      isVᴱ′′ = {!!} -- validᴱ-⊆ᶜ {θ = θ'} (step-⊆ᴴ x₁) isV₂′
      μ₂⊆μ₃ = step-≈ᴴ {{ isVᴾ′′ }} {{ isV₂′′ ∧ isVᴱ′′ }} x₃ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ᴾ-ι μ⊆μ₁ (trans-≈ᴾ-ι μ₁⊆μ₂ μ₂⊆μ₃)

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Wken p x) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ validᴱ-⊆ᶜ p isV₂ }} x pc⋤A

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Inl x) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Inr x) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Case₁ x refl x₁) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Case₂ x refl x₁) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isV₂′ ∧ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Pair x x₁) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Fst x refl) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Snd x x₁) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A
step-≈ᴴ {{isVᴾ}} {{isV₂}} (LabelOf x) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A
step-≈ᴴ {{isVᴾ}} {{isV₂}} GetLabel pc⋤A = refl-≈ᴾ {{isVᴾ}}
step-≈ᴴ {{isVᴾ}} {{isV₂}} (Taint refl x x₁ pc'⊑pc'') pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
  in trans-≈ᴾ-ι μ⊆μ₁ μ₁⊆μ₂

step-≈ᴴ {{isVᴾ}} {{isV₂}} (LabelOfRef x eq) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A
step-≈ᴴ {{isVᴾ}} {{isV₂}} (New x) pc⋤A =
  -- TODO: should be like the previous formalization
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴴ {{ isVᴾ }} {{isV₂}} x pc⋤A
      _ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      ≈ˢ′ = {!updateᴴ-≈ˢ ? ? {{ ? }} ?!} in -- updateᴴ-≈ˢ ? ? {{ ? }} ? ? ?
      ⟨ ≈ˢ′ , ≈ᴴ ⟩ -- snoc-≈ᴴ _ (step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A)
-- ⟨ {!!} , {!refl-≈ᴴ!} ⟩ -- snoc-≈ᴴ _ (step-≈ᴴ {{isVᴾ}} {{isV₂}} x pc⋤A)

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Read x x₁ eq) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A
step-≈ᴴ {{isVᴾ}} {{isV₂}} (Write {ℓ = ℓ} {n = n} {τ = τ} x ⊑₁ x₁ ⊑₂ w) pc⋤A = {!!}
  -- Outdated: This case should be the same as in the old formalizatiom
  -- let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
  --     isVᴱ′ ∧ isVᴾ′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isVᴾ′ , isVᴱ ⟩
  --     -- ref ∧ ∈₂ = validᴿ-⊆ᴴ {r = Refᴵ {τ = τ} ℓ n} (step-⊆ᴴ x₁) isV₂′
  --     μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
  --     μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
  --     ℓ⋤A = trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A
  --     c≈c' = {!!} -- S.⌞ S.cellᴴ ℓ⋤A  ℓ⋤A ⌟
  --     μ₂≈μ₃ = ⟨ {!!} , writeᴴ-≈ᴴ {{ {!!}  }} {!!} {!w!} {!!} ⟩ -- writeᴴ-≈ᴴ {{ isVᴾ′′  }} ∈₂ w c≈c' -- Do I need the valid assumption here?
  -- in trans-≈ᴾ-ι μ⊆μ₁ (trans-≈ᴾ-ι μ₁⊆μ₂ μ₂≈μ₃)

step-≈ᴴ {{isVᴾ}} {{isV₂}} (LabelOfRef-FS x x₁ eq) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A
step-≈ᴴ {{⟨ isVˢ , isVᴴ ⟩}} {{isV₂}} (New-FS x) pc⋤A =
  let ⟨ ≈ˢ , ≈ᴴ ⟩ = step-≈ᴴ {{ ⟨ isVˢ , isVᴴ ⟩ }} {{isV₂}} x pc⋤A
      _ ∧ ⟨ isVˢ′ , isVᴴ′ ⟩ ∧ _ = valid-invariant x ⟨ ⟨ isVˢ , isVᴴ ⟩ , isV₂ ⟩
      ≈ˢ′ =  trans-≈ˢ-ι ≈ˢ refl-≈ˢ (refl-≈ˢ {{ validˢ-⊆ᴴ (step-⊆ᴴ x) {!isVˢ′!} }}) in -- trans-≈ˢ-ι ≈ˢ refl-≈ˢ refl-≈ˢ in
      ⟨ ≈ˢ′ , snoc-≈ᴴ _ ≈ᴴ ⟩ -- snoc-≈ᴴ _ (step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A)
step-≈ᴴ {{isVᴾ}} {{isV₂}} (Read-FS x x₁ eq) pc⋤A = step-≈ᴴ {{ isVᴾ }} x pc⋤A

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x x₁ ∈₁ ⊑₁ refl w) pc⋤A =
  let isVᴱ ∧ isVᴾ′ ∧ isV₂′ = valid-invariant x ⟨ isVᴾ , isV₂ ⟩
      isVᴱ′ ∧ isVᴾ′′ ∧ isV₂′′ = valid-invariant x₁ ⟨ isVᴾ′ , isVᴱ ⟩
      μ⊆μ₁ = step-≈ᴴ {{ isVᴾ }} x pc⋤A
      μ₁⊆μ₂ = step-≈ᴴ {{ isVᴾ′ }} {{ isVᴱ }} x₁ pc⋤A
      v≈ = Valueᴴ (trans-⋤ (trans-⊑ (step-⊑ x) ⊑₁) pc⋤A) (join-⋤₁ (trans-⋤ (step-⊑ x) pc⋤A))
      μ₂≈μ₃ = writeᴴ-≈ᴴ {{ {!!} }} ∈₁ w v≈
  in trans-≈ᴾ-ι μ⊆μ₁ (trans-≈ᴾ-ι μ₁⊆μ₂ ⟨ refl-≈ˢ {{ {!!} }} , μ₂≈μ₃ ⟩ )

step-≈ᴴ {{isVᴾ}} {{isV₂}} (Id x) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A
step-≈ᴴ {{isVᴾ}} {{isV₂}} (UnId x eq) pc⋤A = step-≈ᴴ {{ isVᴾ }} {{ isV₂ }} x pc⋤A

--------------------------------------------------------------------------------

open _≈⟨_,_⟩ᴬ_
open import Data.Unit hiding (_≟_) -- ?
-- open import Generic.Heap 𝑯
-- open SecurityLattice 𝑳
-- open import Generic.LValue
-- open HasLabel 𝑯 -- import Generic.LValue as H

wken-∃ : ∀ {τ β β'} {c₁ c₂ : FConf τ} →
         β ⊆ β' → (x : ∃ (λ β'' → β' ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)) →
         ∃ (λ β'' → β ⊆ β'' × c₁ ≈⟨ β'' ⟩ᶜ c₂)
wken-∃ β⊆β' (β'' ∧ β'⊆β'' ∧ ≈₁)  = β'' ∧ (trans-⊆ β⊆β' β'⊆β'') ∧ ≈₁

mutual

  -- TINI for low steps
  postulate tiniᴸ : ∀ {pc β τ Γ μ₁ μ₂ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ ,  e ⟩
                        c₂ = ⟨ Σ₂ , μ₂ ,  e ⟩ in
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
                    θ₁ ≈⟨ β ⟩ᴱ θ₂ →
                    pc ⊑ A →
                    ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  -- tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ ? , μ₁≈μ₂ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
  --   where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  -- tiniᴸ Unit Unit μ₁≈μ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ μ₁≈μ₂ , Valueᴸ pc⊑A Unit ⟩

  -- tiniᴸ (Lbl ℓ) (Lbl .ℓ) μ₁≈μ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ μ₁≈μ₂ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  -- -- Both true
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨  μ₁'≈μ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... |  β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , v≈ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  --   -- True vs False
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | _ ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | _ ∧ _ ∧  ⟨ μ₁'≈μ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ μ₃≈μ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- -- False vs True
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | _ ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | _ ∧ _ ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | _ ∧ _ ∧ ⟨ μ₃≈μ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- -- False and False
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ₃≈μ₃' , v≈ ⟩
  --   = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₃≈μ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- tiniᴸ Fun Fun μ₁≈μ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ μ₁≈μ₂ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₄ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , v₁≈v₂ ⟩ with tiniᴸ x₁ x₅ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , E.Valueᴸ pc⊑ℓ' (Fun θ₁'≈θ₂') ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₁''≈μ₂'' , v₁'≈v₂' ⟩
  --     rewrite eq₁ | eq₂ = wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tini {{ {!!} }} {{ {!!} }} x₃ x₇  ⟨ μ₁''≈μ₂'' , refl ⟩ (v₁'≈v₂' ∷ wken-≈ᴱ β'⊆β'' θ₁'≈θ₂' ))

  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , E.Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | β'' ∧ β'⊆β'' ∧ ⟨ μ₁''≈μ₂'' , v₁'≈v₂' ⟩
  --     rewrite eq₁ | eq₂ =  wken-∃ (trans-⊆ β⊆β' β'⊆β'') (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁''≈μ₂'' x₃ x₇ (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₁) (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₂))

  -- tiniᴸ (Wken p x) (Wken .p x₁) μ₁≈μ₂ θ₁≈θ₂ pc⊑A = tiniᴸ x x₁ μ₁≈μ₂ θ₁≈θ₂′ pc⊑A
  --   where θ₁≈θ₂′ = slice-≈ᴱ θ₁≈θ₂ p

  -- tiniᴸ (Inl x) (Inl x₁) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , v₁≈v₂ ⟩ =  β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  -- tiniᴸ (Inr x) (Inr x₁) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩

  -- tiniᴸ (Case₁ x refl x₂) (Case₁ x₃ refl x₅) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A (Inl v₁≈v₂) ⟩ = wken-∃ β⊆β' (tini {{ {!!} }} {{ {!!} }} x₂ x₅ ⟨ μ₁'≈μ₂' , refl ⟩ (v₁≈v₂ ∷ wken-≈ᴱ β⊆β' θ₁≈θ₂))
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁'≈μ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- tiniᴸ (Case₁ x refl x₂) (Case₂ x₃ refl x₅) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A () ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁'≈μ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- tiniᴸ (Case₂ x refl x₂) (Case₁ x₃ refl x₅) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A () ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁'≈μ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- tiniᴸ (Case₂ x refl x₂) (Case₂ x₃ refl x₅) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A (Inr v₁≈v₂) ⟩ = wken-∃ β⊆β' (tini {{ {!!} }} {{ {!!} }} x₂ x₅ ⟨ μ₁'≈μ₂' , refl ⟩ (v₁≈v₂ ∷ wken-≈ᴱ β⊆β' θ₁≈θ₂))
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁'≈μ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A))

  -- tiniᴸ (Pair x x₁) (Pair x₂ x₃) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , v₁≈v₁' ⟩ with tiniᴸ x₁ x₃ μ₁'≈μ₂' (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ₁''≈μ₂'' , v₂≈v₂' ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ₁''≈μ₂'' , Valueᴸ pc⊑A (Pair (wken-≈ⱽ β'⊆β'' v₁≈v₁') v₂≈v₂') ⟩

  -- tiniᴸ (Fst x refl) (Fst x₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (Snd x refl) (Snd x₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (LabelOf x) (LabelOf x₁) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴸ ℓ⊑A (Lbl _) ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  -- tiniᴸ GetLabel GetLabel μ₁≈μ₂ θ₁≈θ₂ pc⊑A = _ ∧ refl-⊆ ∧ ⟨ μ₁≈μ₂ , Valueᴸ pc⊑A (Lbl _) ⟩

  -- tiniᴸ (Taint refl x₁ x₂ pc'⊑pc'') (Taint refl x₃ x₄ pc'⊑pc''') μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₃ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , E.Valueᴸ ℓ⊑A (E.Lbl ℓ) ⟩ = wken-∃ β⊆β' ( tini {{ {!!} }} {{ {!!} }} x₂ x₄ ⟨ μ₁'≈μ₂' , refl ⟩ (wken-≈ᴱ β⊆β' θ₁≈θ₂))
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ₁'≈μ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ =  wken-∃ β⊆β' (tiniᴴ {{ {!!} }} {{ {!!} }} μ₁'≈μ₂' x₂ x₄ (trans-⋤ pc'⊑pc'' ℓ₁⋤A) (trans-⋤ pc'⊑pc''' ℓ₂⋤A))

  -- tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ⊑A₁ n) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , (Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)) ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A) ⟩

  -- tiniᴸ  {pc = pc} {μ₁ = μ₁} {μ₂ = μ₂} (New {ℓ = ℓ₁} {τ = τ} {μ' = μ₁'} {r = r₁} x₁) (New {ℓ = ℓ₂} {μ' = μ₂'} {r = r₂} x₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ ⟨ μ≈′ , v≈′ ⟩
  --     where instance _ = _≟_
  --                    _ = ≈-# μ≈
  --           β₁ =  ∥ μ₁' ∥ᴴ ↔ ∥ μ₂' ∥ᴴ
  --           β'' = β' ∣ᴮ β₁
  --           β'⊆β'' = ∣ᴮ-⊆₁ β' β₁
  --           β⊆β'' = trans-⊆ β⊆β' β'⊆β''
  --           μ≈′ = newᴸ-≈ᴴ ? ? -- (≈ⱽ-≈ᶜ v≈) μ≈
  --           v≈′ = Valueᴸ pc⊑A (Ref-I′ (bij-⊆ (∣ᴮ-⊆₂ β' β₁) ? ?)) -- (↔-∈ᵗ ∥ μ₁' ∥ ∥ μ₂' ∥)) (wken-≈ⱽ β'⊆β'' v≈))

  -- tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨  μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A x) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  --      where v≈ = ? -- ≈ᶜ-≈ⱽ (readᴸ-≈ᶜ x n∈M₁ n∈M₂ μ≈)

  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈ ⟩
  --   where v≈ = Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈ ⟩
  --   where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)

  -- tiniᴸ (Write {ℓ = ℓ₁} x₁ ⊑₁ y₁ ℓ₂⊑ℓ w₁) (Write {ℓ = ℓ₂} x₂ ⊑₂ y₂ ℓ₂⊑ℓ' w₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A

  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ with tiniᴸ y₁ y₂ μ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --   where
  --         postulate valid-ref₁ : Validᴿ _ (Refᴵ ℓ₁ _)
  --         postulate valid-ref₂ : Validᴿ _ (Refᴵ ℓ₂ _)
  --         c≈₁ = ? -- ⌞ cellᴴ (trans-⋤ ⊑₁ ℓ₁⋤A ) (trans-⋤ ⊑₁ ℓ₁⋤A) ⌟
  --         c≈₂ = ? -- ⌞ cellᴴ (trans-⋤ ⊑₂ ℓ₂⋤A ) (trans-⋤ ⊑₂ ℓ₂⋤A) ⌟
  --         μ≈′′ = square-≈ᴴ-ι μ≈′ (writeᴴ-≈ᴴ {{ {!!} }} (proj₂ valid-ref₁) w₁ c≈₁)
  --                                (writeᴴ-≈ᴴ {{ {!!} }} (proj₂ valid-ref₂) w₂ c≈₂)

  -- tiniᴸ (Write x₁ ℓ'⊑ℓ y₁ ℓ₂⊑ℓ w₁) (Write x₂ ℓ'⊑ℓ' y₂ ℓ₂⊑ℓ' w₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β'  ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴸ ⊑′ ∈β') ⟩ with tiniᴸ y₁ y₂ μ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --   where ∈β'' = bij-⊆ β'⊆β'' ∈β'
  --         μ≈′′ = writeᴸ-≈ᴴ μ≈′ ? ? ? -- (≈ⱽ-≈ᶜ (Valueᴸ ⊑′ (extract-≈ᴿ v≈ (trans-⊑ ℓ₂⊑ℓ ⊑′)))) w₁ w₂ ∈β''

  -- tiniᴸ (Write x₁ ⊑₁ y₁ ⊑₁′ w₁) (Write x₂ ⊑₂ y₂ ⊑₂′ w₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  --   | β' ∧ β⊆β'  ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-Iᴴ ⋤₁ ⋤₂) ⟩ with tiniᴸ y₁ y₂ μ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --     where postulate valid-ref₁ : Validᴿ _ (Refᴵ _ _)
  --           postulate valid-ref₂ : Validᴿ _ (Refᴵ _ _)
  --           c≈₁ = ? -- ⌞ cellᴴ ⋤₁ ⋤₁ ⌟
  --           c≈₂ = ? -- ⌞ cellᴴ ⋤₂ ⋤₂ ⌟
  --           μ≈′′ = square-≈ᴴ-ι μ≈′ (writeᴴ-≈ᴴ {{ {!!} }} (proj₂ valid-ref₁) w₁ c≈₁) (writeᴴ-≈ᴴ {{ {!!} }} (proj₂ valid-ref₂) w₂ c≈₂)

  -- tiniᴸ (Id x₁) (Id x₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with  tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈ ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ pc⊑A (Id v≈) ⟩

  -- tiniᴸ (UnId x₁ refl) (UnId x₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Id v≈) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (LabelOfRef-FS x₁ ∈₁ refl) (LabelOfRef-FS x₂ ∈₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴸ ℓ⊑A (Ref-S ∈β') ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈ ⟩
  --   where v≈ = ? -- ≈ⱽ-⊑ _ (label-of≈ᶜ-≈ⱽ (readᴸ-≈ᶜ ∈β' ∈₁ ∈₂ μ≈))
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (New-FS {μ' = μ₁'} x₁) (New-FS {μ' = μ₂'} x₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈  ⟩ = β'' ∧ β⊆β'' ∧ ⟨ μ≈′ , wken-≈ⱽ (∣ᴮ-⊆₂ β' β₁) v≈′ ⟩
  --     where instance _ = _≟_
  --                    _ = ≈-# μ≈
  --           β₁ =  ∥ μ₁' ∥ᴴ ↔ ∥ μ₂' ∥ᴴ
  --           β'' = β' ∣ᴮ β₁
  --           β'⊆β'' = ∣ᴮ-⊆₁ β' β₁
  --           β⊆β'' = trans-⊆ β⊆β' β'⊆β''
  --           μ≈′ = newᴸ-≈ᴴ ? μ≈ --  (≈ⱽ-≈ᶜ v≈)
  --           v≈′ = Valueᴸ pc⊑A (Ref-S (↔-∈ᵗ ∥ μ₁' ∥ᴴ ∥ μ₂' ∥ᴴ)) -- (Ref-Iᴸ′ ℓ⊑A (proj₁ (↔-∈ ∥ μ₁' ∥ ∥ μ₂' ∥)))


  -- tiniᴸ (Read-FS x₁ ∈₁ refl) (Read-FS x₂ ∈₂ refl) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , v≈ ⟩
  --   where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A ) ((trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A ))

  -- ... | β' ∧ β⊆β' ∧ ⟨  μ≈ , Valueᴸ ℓ⊑A (Ref-S ∈β) ⟩ = β' ∧ β⊆β' ∧ ⟨ μ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  --      where v≈ = ? -- ≈ᶜ-≈ⱽ (readᴸ-≈ᶜ ∈β ∈₁ ∈₂ μ≈)


  -- tiniᴸ (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x₁ y₁ ∈₁ ⊑₁ refl w₁) (Write-FS x₂ y₂ ∈₂ ⊑₂ refl w₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  -- ... | β' ∧ β⊆β' ∧ ⟨ μ≈ , (Valueᴸ ℓ⊑A (Ref-S ∈β')) ⟩ with tiniᴸ y₁ y₂ μ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ≈′ , v≈ ⟩ =
  --           let ∈β'' = bij-⊆ β'⊆β'' ∈β'
  --               c≈ = ? -- readᴸ-≈ᶜ ∈β'' ∈₁ ∈₂ μ≈′
  --               μ≈′′ = writeᴸ-≈ᴴ μ≈′ ? w₁ w₂ ∈β'' in β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ≈′′ , Valueᴸ pc⊑A Unit ⟩ -- (≈ᶜ-⊑ ℓ (taint-update-≈ᶜ c≈ v≈))

  -- tiniᴸ (Write-FS {ℓ = ℓ} {ℓ₁} {ℓ₂} {ℓ₂'} x₁ y₁ ∈₁ ⊑₁ refl w₁) (Write-FS x₂ y₂ ∈₂ ⊑₂ refl w₂) μ₁≈μ₂ θ₁≈θ₂ pc⊑A | β' ∧ β⊆β' ∧ ⟨ μ≈ , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ with tiniᴸ y₁ y₂ μ≈ (wken-≈ᴱ β⊆β' θ₁≈θ₂) pc⊑A
  -- ... | β'' ∧ β'⊆β'' ∧ ⟨ μ≈′ , v≈ ⟩ = β'' ∧ trans-⊆ β⊆β' β'⊆β'' ∧ ⟨ μ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --   where c≈₁ = ? -- ⌞ cellᴴ (trans-⋤ ⊑₁ ℓ₁⋤A) (join-⋤₁ ℓ₁⋤A) ⌟
  --         c≈₂ = ? -- ⌞ cellᴴ (trans-⋤ ⊑₂ ℓ₂⋤A) (join-⋤₁ ℓ₂⋤A) ⌟
  --         μ≈′′ = square-≈ᴴ-ι μ≈′ (writeᴴ-≈ᴴ {{ {!!} }} ∈₁ w₁ c≈₁) (writeᴴ-≈ᴴ {{ {!!} }} ∈₂ w₂ c≈₂)


  -- TINI for high steps. The computations depend on a secret and thus
  -- might produce different results and code. We then prove TINI by
  -- showing that the program counter can only remain secret and that
  -- each high step preserves low-equivalence of stores.  In
  -- particular we prove that the final stores are low-equivalent (μ₁'
  -- ≈ μ₂'), i.e., the square:
  --
  -- μ₁ ≈ᴴ μ₁'
  -- ≈ᴴ    ≈ᴴ
  -- μ₂ ≈ᴴ μ₂'
  --
  -- using transitivity and symmetry of ≈ᴴ
  -- TODO: do the same for FS-Store
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂ β} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
             let ⟨ Σ₁ , μ₁ , _ ⟩ = c₁
                 ⟨ Σ₂ , μ₂ , _ ⟩ = c₂ in
             -- {{valid₁ᴵ : Validᴵ c₁}} {{validᴱ : Validᴱ ∥ μ₁ ∥ θ₁}} →
             -- {{valid₂ᴵ : Validᴵ c₂}} {{valid₂ᴱ : Validᴱ ∥ μ₂ ∥ θ₂}} →
             {{valid₁ : Valid-Inputs c₁ θ₁}} {{valid₂ : Valid-Inputs c₂ θ₂}} →
             ⟨ Σ₁ , μ₁ ⟩ ≈⟨ β ⟩ᴾ ⟨ Σ₂ , μ₂ ⟩ →
             c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
             c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
             pc₁ ⋤ A → pc₂ ⋤ A →
             ∃ (λ β' → β ⊆ β' × c₁' ≈⟨ β' ⟩ᶜ c₂')
  -- Do we actually need to prove β ⊆ β' ? Not clear from Banjaree proof if this is ever used.
  -- The only reason I can think of is that the theorem might be trivial if we choose β' = ∅
  -- because we do not need to take care of the references. Check this with Deepak.
  tiniᴴ {β = β} {{⟨ ⟨ _ , isV₁ᴴ ⟩ , isV₁ᴱ ⟩ }} {{⟨ ⟨ _ , isV₂ᴴ ⟩ , isV₂ᴱ ⟩ }}
         μ₁≈μ₂ x₁ x₂ pc₁⋤A pc₂⋤A =
    let μ₁≈μ₁' = step-≈ᴴ {{ {!!} }} {{ isV₁ᴱ }} x₁ pc₁⋤A
        μ₂≈μ₂' = step-≈ᴴ {{ {!!} }} {{ isV₂ᴱ }} x₂ pc₂⋤A
        μ₁'≈μ₂' = square-≈ᴾ-ι μ₁≈μ₂ μ₁≈μ₁' μ₂≈μ₂'
        v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A) in
        β ∧ B.refl-⊆ ∧ ⟨ μ₁'≈μ₂' , v≈ ⟩


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
  tini {pc = pc} x₁ x₂ ⟨ μ₁≈μ₂ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ μ₁≈μ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ μ₁≈μ₂ x₁ x₂ pc⋤A pc⋤A
