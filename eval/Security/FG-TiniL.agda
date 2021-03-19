  tiniᴸ : ∀ {pc τ Γ Σ₁ Σ₂ e} {θ₁ θ₂ : Env Γ} {c₁' c₂' : FConf τ} →
           let c₁ = ⟨ Σ₁ , e ⟩
               c₂ = ⟨ Σ₂ , e ⟩ in
           c₁ ⇓⟨ θ₁ , pc ⟩ c₁' →
           c₂ ⇓⟨ θ₂ , pc ⟩ c₂' →
           Σ₁ ≈ˢ Σ₂ →
           θ₁ ≈ᴱ θ₂ →
           pc ⊑ A →
           c₁' ≈ᶜ c₂'

  tiniᴸ (Var τ∈Γ refl) (Var .τ∈Γ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , ≈ⱽ-⊑ _ v₁≈v₂ ⟩
    where v₁≈v₂ = lookup-≈ⱽ τ∈Γ θ₁≈θ₂

  tiniᴸ Unit Unit Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ ,  Valueᴸ pc⊑A Unit ⟩

  tiniᴸ (Lbl ℓ) (Lbl .ℓ) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl ℓ) ⟩

  -- Both true
  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Trueᴸ pc⊑A) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- True vs False
  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ ℓ₁⋤ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  -- False vs True
  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⊥-elim (ℓ₁⋤ℓ₂ ℓ₁⊑ℓ₂)

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₁ y₁ y₂ ℓ₁⊑ℓ₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩


  -- False and False
  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ y₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ _ (Lbl ℓ₁) ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p₁ (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴸ p₂ (Lbl ℓ₂) ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴸ (join-⊑' p₁ p₂) (Falseᴸ pc⊑A) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴸ p (Lbl ℓ₁) ⟩ | ⟨ Σ₃≈Σ₃' , Valueᴴ ¬p₁ ¬p₂ ⟩
      = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ¬p₁) (trans-⋤ (join-⊑₂ _ _) ¬p₂) ⟩

  tiniᴸ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂ refl) (Test₂ y₁ y₂ _ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , Valueᴴ pc⋤ℓ₁' pc⋤ℓ₂' ⟩ with tiniᴸ x₂ y₂ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₃≈Σ₃' , v≈ ⟩ = ⟨ Σ₃≈Σ₃' , Valueᴴ (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₁' ) (trans-⋤ (join-⊑₁ _ _) pc⋤ℓ₂' ) ⟩

  tiniᴸ Fun Fun Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Fun θ₁≈θ₂) ⟩

  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₄ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ with tiniᴸ x₁ x₅ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , E.Valueᴸ pc⊑ℓ' (Fun θ₁'≈θ₂') ⟩ | ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ = tini x₃ x₇ ⟨ Σ₁''≈Σ₂'' , refl ⟩ (v₁'≈v₂' ∷ θ₁'≈θ₂')
  tiniᴸ (App x x₁ eq₁ x₃) (App x₄ x₅ eq₂ x₇) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | ⟨ Σ₁'≈Σ₂' , E.Valueᴴ pc⋤ℓ₁ pc⋤ℓ₂ ⟩ | ⟨ Σ₁''≈Σ₂'' , v₁'≈v₂' ⟩
      rewrite eq₁ | eq₂ = tiniᴴ Σ₁''≈Σ₂'' x₃ x₇ (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₁) (trans-⋤ (join-⊑₂ _ _) pc⋤ℓ₂)

  tiniᴸ (Wken p x) (Wken .p x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂′ pc⊑A
    where θ₁≈θ₂′ = slice-≈ᴱ θ₁≈θ₂ p

  tiniᴸ (Inl x) (Inl x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inl v₁≈v₂) ⟩

  tiniᴸ (Inr x) (Inr x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ pc⊑A (Inr v₁≈v₂) ⟩

  tiniᴸ (Case₁ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inl v₁≈v₂) ⟩ = tini x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ (Case₁ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A  with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ (Case₂ x refl x₂) (Case₁ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A () ⟩
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ (Case₂ x refl x₂) (Case₂ x₃ refl x₅) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Inr v₁≈v₂) ⟩ = tini x₂ x₅ ⟨ Σ₁'≈Σ₂' , refl ⟩ (v₁≈v₂ ∷ θ₁≈θ₂)
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₅ (join-⋤₂ ℓ₁⋤A) (join-⋤₂ ℓ₂⋤A)

  tiniᴸ (Pair x x₁) (Pair x₂ x₃) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , v₁≈v₁' ⟩ with tiniᴸ x₁ x₃ Σ₁'≈Σ₂' θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁''≈Σ₂'' , v₂≈v₂' ⟩ = ⟨ Σ₁''≈Σ₂'' , Valueᴸ pc⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩

  tiniᴸ (Fst x refl) (Fst x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₁≈v₁' ⟩
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (Snd x refl) (Snd x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Pair v₁≈v₁' v₂≈v₂') ⟩ = ⟨ Σ₁'≈Σ₂' , ≈ⱽ-⊑ _ v₂≈v₂' ⟩
  ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩

  tiniᴸ (LabelOf x) (LabelOf x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A v₁≈v₂ ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴸ ℓ⊑A (Lbl _) ⟩
  ... | ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⟨ Σ₁'≈Σ₂' , Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩

  tiniᴸ GetLabel GetLabel Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A = ⟨ Σ₁≈Σ₂ , Valueᴸ pc⊑A (Lbl _) ⟩

  tiniᴸ (Taint refl x₁ x₂ pc'⊑pc'') (Taint refl x₃ x₄ pc'⊑pc''') Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    with tiniᴸ x₁ x₃ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | ⟨ Σ₁'≈Σ₂' , E.Valueᴸ ℓ⊑A (E.Lbl ℓ) ⟩ = tini x₂ x₄ ⟨ Σ₁'≈Σ₂' , refl ⟩ θ₁≈θ₂
  ... | ⟨ Σ₁'≈Σ₂' , (Valueᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = tiniᴴ Σ₁'≈Σ₂' x₂ x₄ (trans-⋤ pc'⊑pc'' ℓ₁⋤A) (trans-⋤ pc'⊑pc''' ℓ₂⋤A)

  tiniᴸ (LabelOfRef x₁ refl) (LabelOfRef x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Refᴸ ℓ⊑A₁ n) ⟩ = E.⟨ Σ≈ , (Valueᴸ (join-⊑' ℓ⊑A₁ ℓ⊑A) (Lbl _)) ⟩
  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Refᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = E.⟨ Σ≈ , (Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)) ⟩
  ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A) ⟩

  tiniᴸ (New x) (New x₁) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x x₁ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈′ , r≈′ ⟩
      where Σ≈′ = square-≈ˢ Σ≈ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)
            r≈′ = Valueᴸ pc⊑A (Refᴴ ℓ₁⋤A ℓ₂⋤A)

  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A r≈ ⟩ = E.⟨ Σ≈′ , r≈′ ⟩
      where M≈ = getᴸ Σ≈ ℓ⊑A
            Σ≈′ = updateᴸ-≈ˢ Σ≈ (new-≈ᴹ M≈  r≈)
            r≈′ = Valueᴸ pc⊑A (Refᴸ′ ℓ⊑A ∥ M≈  ∥-≡)

  tiniᴸ (Read x₁ n∈M₁ refl) (Read x₂ n∈M₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Refᴸ ℓ'⊑A n) ⟩ = E.⟨ Σ≈ , v≈ ⟩
    where M≈ = getᴸ Σ≈ ℓ'⊑A
          v≈ = Valueᴸ (join-⊑' ℓ'⊑A ℓ⊑A) (read-≈ᴹ M≈ n∈M₁ n∈M₂)

  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Refᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ = E.⟨ Σ≈ , v≈ ⟩
    where v≈ = Valueᴴ (trans-⋤ (join-⊑₁ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₁ _ _) ℓ₂⋤A)

  ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , v≈ ⟩
    where v≈ = Valueᴴ (trans-⋤ (join-⊑₂ _ _) ℓ₁⋤A) (trans-⋤ (join-⊑₂ _ _) ℓ₂⋤A)

  tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A

  -- Write high reference in low context (impossible)
  ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ'⊑pc' pc⊑A))

  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A r≈' ⟩ with tiniᴸ x₃ x₄ Σ≈ θ₁≈θ₂ pc⊑A

  -- Write low data to low-reference
  tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Refᴸ ℓ⊑A₁ n) ⟩ | E.⟨ Σ≈′ , E.Valueᴸ ℓ⊑A₂ r≈ ⟩ = ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
      where M≈ = getᴸ Σ≈′ ℓ⊑A₁
            Σ≈′′ = updateᴸ-≈ˢ Σ≈′ (update-≈ᴹ M≈  r≈ M≔₁ M≔₂)

  -- Write high data to low-reference (impossible)
  tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Refᴸ ℓ⊑A₁ n) ⟩ | E.⟨ Σ≈′ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = ⊥-elim (ℓ₂⋤A (trans-⊑ ℓ₂⊑ℓ' ℓ⊑A₁))

  -- Write low data to high reference
  tiniᴸ (Write x₁ ℓ'⊑pc x₃ ℓ₂⊑ℓ M≔₁) (Write x₂ ℓ'⊑pc' x₄ ℓ₂⊑ℓ' M≔₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
    | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (E.Refᴴ ℓ₁⋤A ℓ₂⋤A) ⟩ | E.⟨ Σ≈′ , v≈ ⟩ = ⟨ Σ≈′′ , Valueᴸ pc⊑A Unit ⟩
      where Σ≈′′ = square-≈ˢ Σ≈′ (updateᴴ-≈ˢ _ _ ℓ₁⋤A) (updateᴴ-≈ˢ _ _ ℓ₂⋤A)

  tiniᴸ (Id x₁) (Id x₂) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | E.⟨ Σ≈ , v≈ ⟩ = E.⟨ Σ≈ , Valueᴸ pc⊑A (E.Id v≈) ⟩

  tiniᴸ (UnId x₁ refl) (UnId x₂ refl) Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A with tiniᴸ x₁ x₂ Σ₁≈Σ₂ θ₁≈θ₂ pc⊑A
  ... | E.⟨ Σ≈ , E.Valueᴸ ℓ⊑A (Id v≈) ⟩ = E.⟨ Σ≈ , ≈ⱽ-⊑ _ v≈ ⟩
  ... | E.⟨ Σ≈ , E.Valueᴴ ℓ₁⋤A ℓ₂⋤A ⟩ = E.⟨ Σ≈ , Valueᴴ (join-⋤₁ ℓ₁⋤A) (join-⋤₁ ℓ₂⋤A) ⟩
