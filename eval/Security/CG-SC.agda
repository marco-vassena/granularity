  -- High forcing steps preserve low-equivalence of stores
  stepᶠ-≈ˢ : ∀ {τ Γ θ} {c : EConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , pc , e ⟩ = c
                   ⟨ Σ' , _ , _ ⟩ = c' in
                 c ⇓ᶠ⟨ θ ⟩ c' →
                 pc ⋤ A →
                 Σ ≈ˢ Σ'
  stepᶠ-≈ˢ (Force x x₁) pc⋤A = step-≈ˢ x₁ pc⋤A
  -- High steps preserve low-equivalence of stores
  step-≈ˢ : ∀ {τ Γ θ} {c : TConf Γ (LIO τ)} {c' : FConf τ} →
               let ⟨ Σ , pc , t ⟩ = c
                   ⟨ Σ' , _ , _ ⟩ = c' in
                 c ⇓⟨ θ ⟩ c' →
                 pc ⋤ A →
                 Σ ≈ˢ Σ'
  step-≈ˢ (Return x) pc⋤A = refl-≈ˢ
  step-≈ˢ (Bind x x₁) pc⋤A = trans-≈ˢ (stepᶠ-≈ˢ x pc⋤A) (stepᶠ-≈ˢ x₁ (trans-⋤ (stepᶠ-⊑ x) pc⋤A))
  step-≈ˢ (Unlabel x eq) pc⋤A = refl-≈ˢ
  step-≈ˢ (ToLabeled x) pc⋤A = stepᶠ-≈ˢ x pc⋤A
  step-≈ˢ (LabelOf x x₁) pc⋤A = refl-≈ˢ
  step-≈ˢ GetLabel pc⋤A = refl-≈ˢ
  step-≈ˢ (Taint x x₁) pc⋤A = refl-≈ˢ
  step-≈ˢ (New x pc⊑ℓ) pc⋤A = updateᴴ-≈ˢ _ _ (trans-⋤ pc⊑ℓ pc⋤A)
  step-≈ˢ (Read x n∈M eq) pc⋤A = refl-≈ˢ
  step-≈ˢ (Write x x₁ pc⊑ℓ x₃ up) pc⋤A = updateᴴ-≈ˢ _ _ (trans-⋤ pc⊑ℓ pc⋤A)
  step-≈ˢ (LabelOfRef x eq) pc⋤A = refl-≈ˢ
