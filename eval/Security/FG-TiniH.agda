  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂ pc₁ pc₂} {c₁ : IConf Γ₁ τ} {c₂ : IConf Γ₂ τ} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , _ ⟩ = c₁
               ⟨ Σ₂ , _ ⟩ = c₂ in
           Σ₁ ≈ˢ Σ₂ →
           c₁ ⇓⟨ θ₁ , pc₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ , pc₂ ⟩ c₂' →
           pc₁ ⋤ A → pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᴴ Σ₁≈Σ₂ x₁ x₂ pc₁⋤A pc₂⋤A = ⟨ Σ₁'≈Σ₂' , v≈ ⟩
    where Σ₁≈Σ₁' = step-≈ˢ x₁ pc₁⋤A
          Σ₂≈Σ₂' = step-≈ˢ x₂ pc₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'
          v≈ = Valueᴴ (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A)
