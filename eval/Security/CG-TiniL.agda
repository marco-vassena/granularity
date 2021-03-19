  -- TINI for low steps
  tiniᴸ : ∀ {pc τ Γ Σ₁ Σ₂ θ₁ θ₂} {t : Thunk Γ (LIO τ)} {c₁' c₂' : FConf τ} →
           ⟨ Σ₁ , pc , t ⟩ ⇓⟨ θ₁ ⟩ c₁' →
           ⟨ Σ₂ , pc , t ⟩ ⇓⟨ θ₂ ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           θ₁ ≈ᴱ θ₂ →
           pc ⊑ A →
           c₁' ≈ᶜ c₂'

  tiniᴸ (Return x) (Return x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = pcᴸ Σ₁≈Σ₂ pc⊑A (tiniᴾ x x₁ θ₁≈θ₂)

  tiniᴸ (Bind x x₁) (Bind x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A  with tiniᶠ x x₂ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂
  ... | pcᴸ Σ₁'≈Σ₂' pc'⊑A v₁≈v₂ = tiniᶠ x₁ x₃ ⟨ Σ₁'≈Σ₂' , refl , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  ... | pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A = tiniᶠᴴ x₁ x₃ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A

  tiniᴸ (Unlabel x refl) (Unlabel x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) r
  ... | Labeledᴴ pc₁'⋤A pc₂'⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) pc₁'⋤A) ((trans-⋤ (join-⊑₂ _ _) pc₂'⋤A))

  tiniᴸ (ToLabeled x) (ToLabeled x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᶠ x x₁ ⟨ Σ₁≈Σ₂ , refl , refl ⟩ θ₁≈θ₂
  ... | pcᴸ Σ₁'≈Σ₂' pc⊑A' v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴸ pc⊑A' v₁≈v₂)
  ... | pcᴴ Σ₁'≈Σ₂' pc₁'⋤A pc₂'⋤A = pcᴸ Σ₁'≈Σ₂' pc⊑A (Labeledᴴ pc₁'⋤A pc₂'⋤A)

  tiniᴸ (LabelOf x refl) (LabelOf x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A r = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Labeledᴴ ℓ⋤A ℓ₁⋤A = pcᴴ Σ₁≈Σ₂ (join-⋤₂ ℓ⋤A) (join-⋤₂ ℓ₁⋤A)

  tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = pcᴸ Σ₁≈Σ₂ pc⊑A (Lbl _)

  tiniᴸ {pc = pc} (Taint x refl) (Taint x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Lbl ℓ with (pc ⊔ ℓ) ⊑? A
  ... | yes pc'⊑A = pcᴸ Σ₁≈Σ₂ pc'⊑A Unit
  ... | no pc'⋤A = pcᴴ Σ₁≈Σ₂ pc'⋤A pc'⋤A

  tiniᴸ (New x x₁) (New x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₂ θ₁≈θ₂
  ... | Labeledᴸ ℓ⊑A v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A r₁≈r₂
    where M₁≈M₂ = getᴸ Σ₁≈Σ₂ ℓ⊑A
          r₁≈r₂ = Refᴸ′ ℓ⊑A ∥ M₁≈M₂ ∥-≡
          Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (new-≈ᴹ M₁≈M₂ v₁≈v₂)
  ... | Labeledᴴ ℓ₁⋤A ℓ₂⋤A  = pcᴸ Σ₁'≈Σ₂' pc⊑A r₁≈r₂
    where r₁≈r₂ = Refᴴ ℓ₁⋤A ℓ₂⋤A
          Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x₁ x₂ θ₁≈θ₂
  ... | Refᴸ ℓ⊑A n = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (read-≈ᴹ (getᴸ Σ₁≈Σ₂ ℓ⊑A) n∈M₁ n∈M₂)
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ (Write x₁ x₂ pc⊑ℓ₁ ℓ'⊑ℓ₁ u₁) (Write x₁' x₂' pc⊑ℓ₂ ℓ''⊑ℓ₂ u₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    with tiniᴾ x₁ x₁' θ₁≈θ₂ | tiniᴾ x₂ x₂' θ₁≈θ₂
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A | v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A Unit
    where Σ₁'≈Σ₂' = square-≈ˢ Σ₁≈Σ₂ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)
  ... | Refᴸ ℓ⊑A n | Labeledᴴ ℓ'⋤A ℓ''⋤A  = ⊥-elim (trans-⋤ ℓ'⊑ℓ₁ ℓ'⋤A ℓ⊑A)
  ... | Refᴸ ℓ⊑A n | Labeledᴸ x v₁≈v₂ = pcᴸ Σ₁'≈Σ₂' pc⊑A Unit
    where Σ₁'≈Σ₂' = updateᴸ-≈ˢ Σ₁≈Σ₂ (update-≈ᴹ (getᴸ Σ₁≈Σ₂ ℓ⊑A) v₁≈v₂ u₁ u₂)

  tiniᴸ (LabelOfRef x refl) (LabelOfRef x₁ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴾ x x₁ θ₁≈θ₂
  ... | Refᴸ ℓ⊑A n = pcᴸ Σ₁≈Σ₂ (join-⊑' pc⊑A ℓ⊑A) (Lbl _)
  ... | Refᴴ ℓ₁⋤A ℓ₂⋤A = pcᴴ Σ₁≈Σ₂ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

