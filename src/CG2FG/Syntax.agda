-- CG → FG translation for all the categories of the calculus.

open import Lattice as L

module CG2FG.Syntax {{𝑳 : Lattice}} where

open import CG as CG hiding (_↑¹ ; here ; there ; drop ; cons ; refl-⊆)
open import FG as FG
open import CG2FG.Types public

mutual

  -- Value to value translation
  ⟦_⟧ⱽ : ∀ {τ} → CG.Value τ → Label → FG.Value ⟦ τ ⟧ᵗ
  ⟦ v ⟧ⱽ pc = ⟦ v ⟧ᴿ pc ^ pc

  -- Value to raw value translation
  ⟦_⟧ᴿ : ∀ {τ} → CG.Value τ → Label → FG.Raw ⟦ τ ⟧ᵗ
  ⟦ （） ⟧ᴿ pc = （）
  ⟦ ⟨ e , θ ⟩ᶜ ⟧ᴿ pc = ⟨ ⟦ e ⟧ᴱ , ⟦ θ ⟧ᵉ pc ⟩ᶜ
  ⟦ ⟨ t , θ ⟩ᵀ ⟧ᴿ pc = ⟨ ⟦ t ⟧ᵀ ↑¹ , ⟦ θ ⟧ᵉ pc ⟩ᶜ
  ⟦ inl v ⟧ᴿ pc = inl (⟦ v ⟧ⱽ pc)
  ⟦ inr v ⟧ᴿ pc = inr (⟦ v ⟧ⱽ pc)
  ⟦ ⟨ v , v₁ ⟩ ⟧ᴿ pc = ⟨ ⟦ v ⟧ⱽ pc , ⟦ v₁ ⟧ⱽ pc ⟩
  ⟦ Labeled ℓ v ⟧ᴿ pc = Id (⟨ (⌞ ℓ ⌟ ^ ℓ) , ⟦ v ⟧ⱽ ℓ ⟩ ^ pc)  -- This is enforcing the label on the label here!
  ⟦ Ref ℓ n ⟧ᴿ pc = Ref ℓ n
  ⟦ ⌞ ℓ ⌟ ⟧ᴿ pc = ⌞ ℓ ⌟

  -- Environments.
  ⟦_⟧ᵉ : ∀ {Γ} → CG.Env Γ → Label → FG.Env ⟦ Γ ⟧ᶜ
  ⟦ [] ⟧ᵉ _ = []
  ⟦ v ∷ θ ⟧ᵉ pc = (⟦ v ⟧ⱽ pc) ∷ ⟦ θ ⟧ᵉ pc

  -- Expressions.
  ⟦_⟧ᴱ : ∀ {Γ τ} → CG.Expr Γ τ → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  ⟦ var τ∈Γ ⟧ᴱ = var ⟦ τ∈Γ ⟧∈
  ⟦ Λ e ⟧ᴱ = Λ ⟦ e ⟧ᴱ
  ⟦ e ∘ e₁ ⟧ᴱ = ⟦ e ⟧ᴱ ∘ ⟦ e₁ ⟧ᴱ
  ⟦ ⟨ e , e₁ ⟩ ⟧ᴱ = ⟨ ⟦ e ⟧ᴱ , ⟦ e₁ ⟧ᴱ ⟩
  ⟦ fst e ⟧ᴱ = fst ⟦ e ⟧ᴱ
  ⟦ snd e ⟧ᴱ = snd ⟦ e ⟧ᴱ
  ⟦ inl e ⟧ᴱ = inl ⟦ e ⟧ᴱ
  ⟦ inr e ⟧ᴱ = inr ⟦ e ⟧ᴱ
  ⟦ case e e₁ e₂ ⟧ᴱ = case ⟦ e ⟧ᴱ ⟦ e₁ ⟧ᴱ ⟦ e₂ ⟧ᴱ
  ⟦ ⌞ t ⌟ᵀ ⟧ᴱ = Λ (⟦ t ⟧ᵀ ↑¹)
  ⟦ wken e x ⟧ᴱ = wken ⟦ e ⟧ᴱ ⟦ x ⟧⊆
  ⟦ （） ⟧ᴱ = （）
  ⟦ ⌞ ℓ ⌟ ⟧ᴱ = ⌞ ℓ ⌟
  ⟦ e₁ ⊑-? e₂ ⟧ᴱ = ⟦ e₁ ⟧ᴱ ⊑-? ⟦ e₂ ⟧ᴱ

  -- Thunks.
  ⟦_⟧ᵀ : ∀ {τ Γ} → CG.Thunk Γ (LIO τ) → FG.Expr ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
  ⟦ return e ⟧ᵀ = ⟦ e ⟧ᴱ
  ⟦ bind e₁ e₂ ⟧ᵀ = (Λ (taint (labelOf (var here)) (⟦ e₂ ⟧ᴱ FG.∘  Id （） )) ∘ (⟦ e₁ ⟧ᴱ FG.∘ Id （）))
  ⟦ unlabel e ⟧ᵀ = (Λ (taint (fst (var here)) (snd (var here)))) ∘ (unId ⟦ e ⟧ᴱ)
  ⟦ toLabeled e ⟧ᵀ =  (Λ (Id ⟨ (labelOf (var here)) , var here ⟩) ) ∘ (⟦ e ⟧ᴱ FG.∘ (Id （）))
  ⟦ labelOf e ⟧ᵀ = fst (unId ⟦ e ⟧ᴱ)
  ⟦ getLabel ⟧ᵀ = getLabel
  ⟦ taint e ⟧ᵀ = taint ⟦ e ⟧ᴱ （）
  ⟦ new e ⟧ᵀ = new (Λ (taint ( (fst (var here))) (snd (var here))) ∘  (unId ⟦ e ⟧ᴱ))
  ⟦ ! e ⟧ᵀ = ! ⟦ e ⟧ᴱ
  ⟦ e ≔ e₁ ⟧ᵀ = ⟦ e ⟧ᴱ ≔ snd (unId ⟦ e₁ ⟧ᴱ)
  ⟦ labelOfRef e ⟧ᵀ = labelOfRef ⟦ e ⟧ᴱ

--------------------------------------------------------------------------------

-- Derived store and memory translation.
open import Generic.Store.Convert {CG.Ty} {FG.Ty} {CG.Value} {FG.Raw} ⟦_⟧ᵗ ⟦_⟧ᴿ
  renaming (
    ⟪_⟫ˢ to ⟦_⟧ˢ
  ; ⟪_⟫ᴹ to ⟦_⟧ᴹ
  ) public

-- Convert and force program execution.
⟦_⟧ᴵ : ∀ {Γ τ} → EConf Γ (LIO τ) → IConf ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ ⟨ Σ , pc , e ⟩ ⟧ᴵ = ⟨ ⟦ Σ ⟧ˢ , ⟦ e ⟧ᴱ ∘ (Id （）) ⟩
