  tini : ∀ {τ Γ θ₁ θ₂ pc} {c₁ c₂ : IConf Γ τ} {c₁' c₂' : FConf τ} →
           c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
           c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
           c₁ ≈ᴵ c₂ →
           θ₁ ≈ᴱ θ₂ →
           c₁' ≈ᶜ c₂'
  tini {pc = pc} x₁ x₂ ⟨ Σ₁≈Σ₂ , refl ⟩  θ₁≈θ₂ with pc ⊑? A
  ... | yes pc⊑A = tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | no pc⋤A = tiniᴴ Σ₁≈Σ₂ x₁ x₂ pc⋤A pc⋤A
