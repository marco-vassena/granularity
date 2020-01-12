-- This module proves security of FG, i.e., termination-insensitive
-- non-interference (TINI).  The proof consists in showing that the
-- big-step semantics preserves L-equivalence.
--
-- This module is parametric in the security lattice 𝑳 = (𝓛, ⊑) and in
-- the attacker's security A ∈ 𝓛.

open import Lattice

module FG.Security {{𝑳 : Lattice}} (A : Label) where

open import FG.Types
open import FG.Syntax
open import FG.Semantics
open import FG.LowEq A as E public

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Lemmas on L-equivalent environments.

-- Lookup in L-equivalent envs gives L-equivalent values
lookup-≈ⱽ : ∀ {τ Γ θ₁ θ₂} → (τ∈Γ : τ ∈ Γ) → θ₁ ≈ᴱ θ₂ → (θ₁ !! τ∈Γ) ≈ⱽ (θ₂ !! τ∈Γ)
lookup-≈ⱽ here (v₁≈v₂ ∷ θ₁≈θ₂) = v₁≈v₂
lookup-≈ⱽ (there τ∈Γ) (v₁≈v₂ ∷ θ₁≈θ₂) = lookup-≈ⱽ τ∈Γ θ₁≈θ₂


-- Slicing L-equivalent envs gives gives L-equivalent envs.
slice-≈ᴱ : ∀ {Γ₁ Γ₂} {θ₁ θ₂ : Env Γ₂} →
                 θ₁ ≈ᴱ θ₂ →
                 (Γ₁⊆Γ₂ : Γ₁ ⊆ Γ₂) →
                 slice θ₁ Γ₁⊆Γ₂ ≈ᴱ slice θ₂ Γ₁⊆Γ₂
slice-≈ᴱ [] base = []
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (cons p) = v₁≈v₂ ∷ slice-≈ᴱ θ₁≈θ₂ p
slice-≈ᴱ (v₁≈v₂ ∷ θ₁≈θ₂) (drop p) = slice-≈ᴱ θ₁≈θ₂ p

--------------------------------------------------------------------------------

open import Data.Product renaming (_×_ to _∧_ ; _,_ to ⟨_,_⟩)
open import Generic.Bijection

-- TODO: Ideally combined with the lemma below
step-≈ᴴ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , μ , _ ⟩ = c
                 ⟨ Σ' , μ' , _ ⟩ = c' in
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
               μ ≈ᴴ μ'
step-≈ᴴ {c = c} (Var τ∈Γ x) pc⋤A = ⟨ ι , refl-≈ᴴ {μ = Conf.heap c} ⟩
step-≈ᴴ Unit pc⋤A = {!!}
step-≈ᴴ (Lbl ℓ) pc⋤A = {!!}
step-≈ᴴ (Test₁ x x₁ x₂ x₃) pc⋤A = {!!}
step-≈ᴴ (Test₂ x x₁ x₂ x₃) pc⋤A = {!!}
step-≈ᴴ Fun pc⋤A = {!!}
step-≈ᴴ (App x x₁ refl x₃) pc⋤A =
  let ⟨ β , μ≈μ₁ ⟩ = step-≈ᴴ x pc⋤A
      ⟨ β₁ , μ₁≈μ₂ ⟩ = step-≈ᴴ x₁ pc⋤A
      ⟨ β₂ , μ₂≈μ₃ ⟩ = step-≈ᴴ x₃ (trans-⋤ (join-⊑₁ _ _) pc⋤A) in
        ⟨ β₂ ∘ᴮ β₁ ∘ᴮ β , (trans-≈ᴴ {β₁ = β} {β₂ ∘ᴮ β₁} μ≈μ₁ (trans-≈ᴴ {β₁ = β₁} {β₂ = β₂} μ₁≈μ₂ μ₂≈μ₃)) ⟩
step-≈ᴴ (Wken p x) pc⋤A = {!!}
step-≈ᴴ (Inl x) pc⋤A = {!!}
step-≈ᴴ (Inr x) pc⋤A = {!!}
step-≈ᴴ (Case₁ x x₁ x₂) pc⋤A = {!!}
step-≈ᴴ (Case₂ x x₁ x₂) pc⋤A = {!!}
step-≈ᴴ (Pair x x₁) pc⋤A = {!!}
step-≈ᴴ (Fst x x₁) pc⋤A = {!!}
step-≈ᴴ (Snd x x₁) pc⋤A = {!!}
step-≈ᴴ (LabelOf x) pc⋤A = {!!}
step-≈ᴴ GetLabel pc⋤A = {!!}
step-≈ᴴ (Taint eq x x₁ pc'⊑pc'') pc⋤A = {!!}
step-≈ᴴ (LabelOfRef x eq) pc⋤A = {!!}
step-≈ᴴ (New x) pc⋤A = {!!}
step-≈ᴴ (Read x x₁ eq) pc⋤A = {!!}
step-≈ᴴ (Write x x₁ x₂ ℓ₂⊑ℓ x₃) pc⋤A = {!!}
step-≈ᴴ (LabelOfRef-FS x x₁ eq) pc⋤A = {!!}
step-≈ᴴ (New-FS x) pc⋤A =
  let ⟨ β , μ≈μ' ⟩ = step-≈ᴴ x pc⋤A in new-≈ᴴ μ≈μ' _ (trans-⋤ (step-⊑ x) pc⋤A)
step-≈ᴴ (Read-FS x x₁ eq) pc⋤A = {!!}
step-≈ᴴ (Write-FS x x₁ x₂ x₃ eq x₄) pc⋤A = {!!}
step-≈ᴴ (Id x) pc⋤A = {!!}
step-≈ᴴ (UnId x eq) pc⋤A = {!!}


-- TODO: add FS-Store to this lemma
-- High steps preserve low-equivalence of stores
step-≈ˢ : ∀ {τ Γ θ pc} {c : IConf Γ τ} {c' : FConf τ} →
             let ⟨ Σ , μ , _ ⟩ = c
                 ⟨ Σ' , μ' , _ ⟩ = c' in
               c ⇓⟨ θ , pc ⟩ c' →
               pc ⋤ A →
                 (Σ ≈ˢ Σ')

step-≈ˢ (Var τ∈Γ x) pc⋤A = refl-≈ˢ
step-≈ˢ Unit pc⋤A = refl-≈ˢ
step-≈ˢ (Lbl ℓ) pc⋤A = refl-≈ˢ
step-≈ˢ (Test₁ x x₁ x₂ refl) pc⋤A = trans-≈ˢ Σ₁≈Σ₂′ Σ₁≈Σ₂′′
  where Σ₁≈Σ₂′ = step-≈ˢ x pc⋤A
        Σ₁≈Σ₂′′ = step-≈ˢ x₁ pc⋤A
step-≈ˢ (Test₂ x x₁ x₂ refl) pc⋤A = trans-≈ˢ Σ₁≈Σ₂′ Σ₁≈Σ₂′′
  where Σ₁≈Σ₂′ = step-≈ˢ x pc⋤A
        Σ₁≈Σ₂′′ = step-≈ˢ x₁ pc⋤A
step-≈ˢ Fun pc⋤A = refl-≈ˢ
step-≈ˢ (App x x₁ refl x₃) pc⋤A = trans-≈ˢ Σ₁≈Σ₂′ (trans-≈ˢ Σ₁≈Σ₂′′ Σ₁≈Σ₂′′′)
  where Σ₁≈Σ₂′ = step-≈ˢ x pc⋤A
        Σ₁≈Σ₂′′ = step-≈ˢ x₁ pc⋤A
        Σ₁≈Σ₂′′′ = step-≈ˢ x₃ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
step-≈ˢ (Wken p x) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (Inl x) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (Inr x) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (Case₁ x refl x₂) pc⋤A = trans-≈ˢ Σ≈Σ' Σ'≈Σ''
  where Σ≈Σ' = step-≈ˢ x pc⋤A
        Σ'≈Σ'' = step-≈ˢ x₂ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
step-≈ˢ (Case₂ x refl x₂) pc⋤A = trans-≈ˢ Σ≈Σ' Σ'≈Σ''
  where Σ≈Σ' = step-≈ˢ x pc⋤A
        Σ'≈Σ'' = step-≈ˢ x₂ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
step-≈ˢ (Pair x x₁) pc⋤A = trans-≈ˢ Σ≈Σ' Σ'≈Σ''
  where Σ≈Σ' = step-≈ˢ x pc⋤A
        Σ'≈Σ'' = step-≈ˢ x₁ pc⋤A
step-≈ˢ (Fst x x₁) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (Snd x x₁) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (LabelOf x) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ GetLabel pc⋤A = refl-≈ˢ
step-≈ˢ (Taint refl x₁ x₂ pc'⊑pc'') pc⋤A = trans-≈ˢ Σ≈Σ' Σ'≈Σ''
  where Σ≈Σ' = step-≈ˢ x₁ pc⋤A
        Σ'≈Σ'' = step-≈ˢ x₂ (trans-⋤ (join-⊑₁ _ _) pc⋤A)
step-≈ˢ (LabelOfRef x eq) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (New x) pc⋤A = trans-≈ˢ Σ≈Σ' Σ'≈Σ''
  where Σ≈Σ' = step-≈ˢ x pc⋤A
        Σ'≈Σ'' = updateᴴ-≈ˢ _ _ (trans-⋤ (step-⊑ x) pc⋤A)
step-≈ˢ (Read x₁ x₂ eq) pc⋤A = step-≈ˢ x₁ pc⋤A
step-≈ˢ (Write x ℓ'⊑pc x₂ ℓ₂⊑ℓ x₃) pc⋤A = trans-≈ˢ Σ≈Σ' (trans-≈ˢ Σ'≈Σ'' Σ''≈Σ''')
  where pc⊑ℓ = trans-⊑ (step-⊑ x₂) ℓ₂⊑ℓ
        Σ≈Σ' = step-≈ˢ x pc⋤A
        Σ'≈Σ'' = step-≈ˢ x₂ pc⋤A
        Σ''≈Σ''' = updateᴴ-≈ˢ _ _ (trans-⋤ pc⊑ℓ pc⋤A)
step-≈ˢ (Id x) pc⋤A = step-≈ˢ x pc⋤A
step-≈ˢ (UnId x₁ x₂) pc⋤A = step-≈ˢ x₁ pc⋤A

--------------------------------------------------------------------------------

open _≈⟨_⟩ᴬ_

mutual

  -- TINI for low steps
  postulate tiniᴸ : ∀ {pc τ Γ Σ₁ Σ₂ μ₁ μ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
                    let c₁ = ⟨ Σ₁ , μ₁ , e ⟩
                        c₂ = ⟨ Σ₂ , μ₂ , e ⟩ in
                    c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
                    c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
                    Σ₁ ≈ˢ Σ₂ →
                    θ₁ ≈ᴱ θ₂ →
                    pc ⊑ A →
                    c₁' ≈ᶜ c₂'

  -- tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
  --   where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  -- tiniᴸ Unit Unit Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ ,  Valueᴸ pc⊑A Unit ⟩

  -- tiniᴸ (Lbl ℓ) (Lbl .ℓ) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  -- -- Both true
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- -- True vs False
  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- -- False vs True
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- -- False and False
  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
  --     = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  -- tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- tiniᴸ Fun Fun Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₄ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ with tiniᴸ x₁ x₅ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , E.Valueᴸ pc⊑ℓ' (Fun θ₁'≈θ₂') ⟩ | ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
  --     rewrite eq₁ | eq₂ = tini x₃ x₇ ⟨ Σ₁''≈Σ₂'' , refl ⟩ (v₁'≈v₂' ∷ θ₁'≈θ₂')
  -- tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | ⟨ Σ₁'≈Σ₂' , E.Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
  --     rewrite eq₁ | eq₂ = tiniᴴ Σ₁''≈Σ₂'' x₃ x₇ (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₁) (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₂)

  -- tiniᴸ (Wken p x) (Wken .p x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂′ pc⊑A
  --   where θ₁≈θ₂′ = slice-≈ᴱ θ₁≈θ₂ p

  -- tiniᴸ (Inl x) (Inl x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  -- tiniᴸ (Inr x) (Inr x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩

  -- tiniᴸ (Case₁ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inl v₁≈v₂) ⟩ = tini x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  -- ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  -- tiniᴸ (Case₁ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A  with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  -- tiniᴸ (Case₂ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  -- tiniᴸ (Case₂ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inr v₁≈v₂) ⟩ = tini x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  -- tiniᴸ (Pair x x₁) (Pair x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₁' ⟩ with tiniᴸ x₁ x₃ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁''≈Σ₂'' , v₂≈v₂' ⟩ = ⟨ Σ₁''≈Σ₂'' , Valueᴸ pc⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩

  -- tiniᴸ (Fst x refl) (Fst x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (Snd x refl) (Snd x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  -- ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  -- tiniᴸ (LabelOf x) (LabelOf x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Lbl _) ⟩
  -- ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  -- tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl _) ⟩

  -- tiniᴸ (Taint refl x₁ x₂ pc'⊑pc'') (Taint refl x₃ x₄ pc'⊑pc''') Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   with tiniᴸ x₁ x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | ⟨ Σ₁'≈Σ₂' , E.Valueᴸ ℓ⊑A (E.Lbl ℓ) ⟩ = tini x₂ x₄ ⟨ Σ₁'≈Σ₂' , refl ⟩ θ₁≈θ₂
  -- ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₄ (trans-⋤ pc'⊑pc'' ℓ₁⋤A) (trans-⋤ pc'⊑pc''' ℓ₂⋤A)

  -- tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ = E.⟨ Σ≈ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = E.⟨ Σ≈ , (Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)) ⟩
  -- ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A) ⟩

  -- tiniᴸ (New x) (New x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈′ , r≈′ ⟩
  --     where Σ≈′ = square-≈ˢ Σ≈ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)
  --           r≈′ = Valueᴸ pc⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A)

  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A r≈ ⟩ = E.⟨ Σ≈′ , r≈′ ⟩
  --     where M≈ = getᴸ Σ≈ ℓ⊑A
  --           Σ≈′ = updateᴸ-≈ˢ Σ≈ (new-≈ᴹ M≈  r≈)
  --           r≈′ = Valueᴸ pc⊑A (Ref-Iᴸ′ ℓ⊑A ∥ M≈  ∥-≡)

  -- tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴸ ℓ'⊑A n) ⟩ = E.⟨ Σ≈ , v≈ ⟩
  --   where M≈ = getᴸ Σ≈ ℓ'⊑A
  --         v≈ = Valueᴸ (join-⊑' ℓ'⊑A ℓ⊑A) (read-≈ᴹ M≈ n∈M₁ n∈M₂)

  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = E.⟨ Σ≈ , v≈ ⟩
  --   where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)

  -- ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , v≈ ⟩
  --   where v≈ = Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A

  -- -- Write high reference in low context (impossible)
  -- ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ'⊑pc' pc⊑A))

  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A r≈' ⟩ with tiniᴸ x₃ x₄ Σ≈ θ₁≈θ₂ pc⊑A

  -- -- Write low data to low-reference
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ | E.⟨ Σ≈′ , E.Valueᴸ ℓ⊑A₂ r≈ ⟩ = ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --     where M≈ = getᴸ Σ≈′ ℓ⊑A₁
  --           Σ≈′′ = updateᴸ-≈ˢ Σ≈′ (update-≈ᴹ M≈  r≈ M≔₁ M≔₂)

  -- -- Write high data to low-reference (impossible)
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴸ ℓ⊑A₁ n) ⟩ | E.⟨ Σ≈′ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ₂⊑ℓ' ℓ⊑A₁))

  -- -- Write low data to high reference
  -- tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  --   | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Ref-Iᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ | E.⟨ Σ≈′ , v≈ ⟩ = ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
  --     where Σ≈′′ = square-≈ˢ Σ≈′ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)

  -- tiniᴸ (Id x₁) (Id x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | E.⟨ Σ≈ , v≈ ⟩ = E.⟨ Σ≈ , Valueᴸ pc⊑A (E.Id v≈) ⟩

  -- tiniᴸ (UnId x₁ refl) (UnId x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Id v≈) ⟩ = E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  -- ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩


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
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , _ , _ ⟩ = c₁
               ⟨ Σ₂ , _ , _ ⟩ = c₂ in
           Σ₁ ≈ˢ Σ₂ →
           c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
           pc₁ ⋤ A → pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᴴ Σ₁≈Σ₂ x₁ x₂ pc₁⋤A pc₂⋤A = {!!} -- ⟨ Σ₁'≈Σ₂' , v≈ ⟩
    where Σ₁≈Σ₁' = step-≈ˢ x₁ pc₁⋤A
          Σ₂≈Σ₂' = step-≈ˢ x₂ pc₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'
          v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A)

  -- TINI: top level theorem
  tini : ∀ {τ Γ θ₁ θ₂ pc} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
           c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
           c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
           c₁ ≈ᴵ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tini = {!!}
  -- {pc = pc} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  -- ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  -- ... | no pc⋤A = tiniᴴ Σ₁≈Σ₂ x₁ x₂ pc⋤A pc⋤A
