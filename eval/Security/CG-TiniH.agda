  tiniᶠᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂} {c₁ : EConf Γ₁ (LIO τ)} {c₂ : EConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , pc₂ , t₂ ⟩ = c₂ in
           c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
           c₂ ⇓ᶠ⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᶠᴴ (Force x x₁) (Force x₂ x₃) = tiniᴴ x₁ x₃


  -- TINI for high steps. The computations depend on a secret and thus
  -- might produce different results and code. We then prove TINI by
  -- showing that the program counter can only remain secret and that
  -- each high step preserves low-equivalence of stores.  In
  -- particular we proce that the final stores are low-equivalent (Σ₁'
  -- ≈ Σ₂'), i.e., the square:
  --
  -- Σ₁ ≈ˢ Σ₁'
  -- ≈ˢ    ≈ˢ
  -- Σ₂ ≈ˢ Σ₂'
  --
  -- using transitivity and symmetry of ≈ˢ
  tiniᴴ : ∀ {τ Γ₁ Γ₂ θ₁ θ₂} {c₁ : TConf Γ₁ (LIO τ)} {c₂ : TConf Γ₂ (LIO τ)} {c₁' c₂' : FConf τ} →
           let ⟨ Σ₁ , pc₁ , t₁ ⟩ = c₁
               ⟨ Σ₂ , pc₂ , t₂ ⟩ = c₂ in
           c₁ ⇓⟨ θ₁ ⟩ c₁' →
           c₂ ⇓⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           pc₁ ⋤ A →
           pc₂ ⋤ A →
           c₁' ≈ᶜ c₂'
  tiniᴴ x₁ x₂ Σ₁≈Σ₂ pc₁⋤A pc₂⋤A = pcᴴ Σ₁'≈Σ₂' (trans-⋤ (step-⊑ x₁) pc₁⋤A) (trans-⋤ (step-⊑ x₂) pc₂⋤A)
    where Σ₁≈Σ₁' = step-≈ˢ x₁ pc₁⋤A
          Σ₂≈Σ₂' = step-≈ˢ x₂ pc₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂'
