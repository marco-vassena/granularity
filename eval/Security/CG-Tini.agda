  tini : ∀ {τ Γ θ₁ θ₂} {c₁ c₂ : TConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           c₁ ≈ᵀ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tini {c₁ = ⟨ _ , pc , _ ⟩} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ x₁ x₂ Σ₁≈Σ₂ pc⋤A pc⋤A

  tiniᶠ : ∀ {τ Γ θ₁ θ₂} {c₁ c₂ : EConf Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           c₁ ≈ᴵ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tiniᶠ (Force x x₁) (Force x₂ x₃) ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂ with tiniᴾ x x₂ θ₁≈θ₂
  ... | Thunk′ θ₁≈θ₂' = tini x₁ x₃ ⟨ Σ≈ , refl , refl ⟩ θ₁≈θ₂'
