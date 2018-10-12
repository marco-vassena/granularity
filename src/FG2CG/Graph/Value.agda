open import Lattice

module FG2CG.Graph.Value {{𝑳 : Lattice}} where

open import FG as FG
open import CG as CG
open import FG2CG.Syntax
open import Relation.Binary.PropositionalEquality

open import FG2CG.Graph.Types
open import FG2CG.Graph.Expr

mutual

  -- Graph of the translation function for raw values ⟪_⟫ᴿ
  data Fg2Cgᴿ : ∀ {τ τ'} → MkTy′ τ τ' → FG.Raw τ → CG.Value τ' → Set where
    Unit : Fg2Cgᴿ Unit （） （）
    Lbl : ∀ ℓ → Fg2Cgᴿ 𝓛 ⌞ ℓ ⌟ ⌞ ℓ ⌟
    Inl : ∀ {τ₁ τ₁' τ₂ τ₂'} {v₁ : FG.Value τ₁} {v₁' : CG.Value (Labeled τ₁')}
            {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
            Fg2Cgⱽ p₁ v₁ v₁' →
            Fg2Cgᴿ (Sum (Labeled p₁) (Labeled p₂)) (inl v₁) (inl v₁')
    Inr : ∀ {τ₁ τ₂ τ₁' τ₂'} {v₂' : CG.Value (Labeled τ₂')} {v₂ : FG.Value τ₂} →
            {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
            Fg2Cgⱽ p₂ v₂ v₂' →
            Fg2Cgᴿ (Sum (Labeled p₁) (Labeled p₂)) (inr v₂) (inr v₂')
    Pair : ∀ {τ₁ τ₁' τ₂ τ₂'} {v₁ : FG.Value τ₁} {v₂ : FG.Value τ₂}
             {v₁' : CG.Value (Labeled τ₁')} {v₂' : CG.Value (Labeled τ₂')} →
             {p₁ : MkTy′ τ₁ τ₁'} {p₂ : MkTy′ τ₂ τ₂'} →
             Fg2Cgⱽ p₁ v₁ v₁' →
             Fg2Cgⱽ p₂ v₂ v₂' →
             Fg2Cgᴿ (Prod (Labeled p₁) (Labeled p₂)) ⟨ v₁ , v₂ ⟩ ⟨ v₁' , v₂' ⟩
    Fun : ∀ {τ₁ τ₁' τ₂ τ₂' Γ Γ' θ θ' c p₁ p₂} {e₁ : FG.Expr (τ₁ FG.∷ Γ) τ₂}
            {e₂ : CG.Expr (τ₁' FG.∷ Γ') (LIO (Labeled τ₂'))} →
            Fg2Cgᵉ c θ θ' →
            Fg2Cgᴱ (p₁ ∷ c) p₂ e₁ e₂ →
            Fg2Cgᴿ (Fun p₁ (Labeled p₂)) ⟨ e₁ , θ ⟩ᶜ ⟨ e₂  , θ' ⟩ᶜ
    Ref : ∀ {τ τ' ℓ n} {p : MkTy′ τ τ'} → Fg2Cgᴿ (Ref p) (Ref ℓ n) (Ref ℓ n)
    Id : ∀ {τ τ'} {v : FG.Value τ} {v' : CG.Value (Labeled τ')} {p : MkTy′ τ τ'} →
           Fg2Cgⱽ p v v' →
           Fg2Cgᴿ (Id (Labeled p)) (Id v) v'

  -- Graph of the translation function for values ⟪_⟫ⱽ
  data Fg2Cgⱽ {τ τ'} (p : MkTy′ τ τ') : FG.Value τ → CG.Value (Labeled τ') → Set where
    Labeled : ∀ {r} {v : CG.Value τ'} → (ℓ : Label) → Fg2Cgᴿ p r v → Fg2Cgⱽ p (r ^ ℓ) (Labeled ℓ v)

  -- Graph of the translation function for environments ⟪_⟫ᵉ
  data Fg2Cgᵉ : ∀ {Γ Γ'} → MkCtx Γ Γ' → FG.Env Γ → CG.Env Γ' → Set where
    [] : Fg2Cgᵉ [] [] []
    _∷_ : ∀ {τ τ' Γ Γ'} {v : FG.Value τ} {v' : CG.Value (Labeled τ')} {θ : FG.Env Γ} {θ' : CG.Env Γ'} →
            {p : MkTy′ τ τ'} {c : MkCtx Γ Γ'} →
            Fg2Cgⱽ p v v' →
            Fg2Cgᵉ c θ θ' →
            Fg2Cgᵉ (Labeled p ∷ c) (v ∷ θ) (v' ∷ θ')

mutual

  mkFg2Cgⱽ : ∀ {τ} (v : FG.Value τ) →  Fg2Cgⱽ (mkTy′ τ) v ⟪ v ⟫ⱽ
  mkFg2Cgⱽ (r ^ ℓ) = Labeled ℓ (mkFg2Cgᴿ r)

  mkFg2Cgᴿ : ∀ {τ} (r : FG.Raw τ) →  Fg2Cgᴿ (mkTy′ τ) r ⟪ r ⟫ᴿ
  mkFg2Cgᴿ （） = Unit
  mkFg2Cgᴿ ⟨ e , θ ⟩ᶜ = Fun (mkFg2Cgᵉ θ) (mkFg2Cgᴱ e)
  mkFg2Cgᴿ (inl x) = Inl (mkFg2Cgⱽ x)
  mkFg2Cgᴿ (inr x) = Inr (mkFg2Cgⱽ x)
  mkFg2Cgᴿ ⟨ v , v₁ ⟩ = Pair (mkFg2Cgⱽ v) (mkFg2Cgⱽ v₁)
  mkFg2Cgᴿ (Ref ℓ n) = Ref
  mkFg2Cgᴿ ⌞ ℓ ⌟ = Lbl ℓ
  mkFg2Cgᴿ (Id v) = Id (mkFg2Cgⱽ v)

  mkFg2Cgᵉ : ∀ {Γ} (θ : FG.Env Γ) →  Fg2Cgᵉ (mkCtx Γ) θ ⟪ θ ⟫ᵉ
  mkFg2Cgᵉ [] = []
  mkFg2Cgᵉ (v ∷ θ) = (mkFg2Cgⱽ v) ∷ (mkFg2Cgᵉ θ)

mutual
  ≡-Fg2Cgⱽ : ∀ {τ v' p} {v : FG.Value τ} → Fg2Cgⱽ p v v' → v' ≡ ⟪ v ⟫ⱽ
  ≡-Fg2Cgⱽ (Labeled ℓ x) = cong (Labeled ℓ) (≡-Fg2Cgᴿ x)

  ≡-Fg2Cgᴿ : ∀ {τ r' p} {r : FG.Raw τ} → Fg2Cgᴿ p r r' → r' ≡ ⟪ r ⟫ᴿ
  ≡-Fg2Cgᴿ Unit = refl
  ≡-Fg2Cgᴿ (Lbl ℓ) = refl
  ≡-Fg2Cgᴿ (Inl x) = cong inl (≡-Fg2Cgⱽ x)
  ≡-Fg2Cgᴿ (Inr x) = cong inr (≡-Fg2Cgⱽ x)
  ≡-Fg2Cgᴿ (Pair x x₁) = cong₂ ⟨_,_⟩ (≡-Fg2Cgⱽ x) (≡-Fg2Cgⱽ x₁)
  ≡-Fg2Cgᴿ (Fun {c = c} x₁ x₂) with ≡-MkCtx c
  ... | eq₁ rewrite eq₁ | ≡-Fg2Cgᴱ x₂ = cong₂ ⟨_,_⟩ᶜ refl (≡-Fg2Cgᵉ x₁)
  ≡-Fg2Cgᴿ Ref = refl
  ≡-Fg2Cgᴿ (Id v) rewrite ≡-Fg2Cgⱽ v = refl

  ≡-Fg2Cgᵉ : ∀ {Γ θ' c} {θ : FG.Env Γ} → Fg2Cgᵉ c θ θ' → θ' ≡ ⟪ θ ⟫ᵉ
  ≡-Fg2Cgᵉ [] = refl
  ≡-Fg2Cgᵉ (x₁ ∷ x₂) = cong₂ _∷_ (≡-Fg2Cgⱽ x₁) (≡-Fg2Cgᵉ x₂)
