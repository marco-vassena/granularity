open import Lattice

module CG2FG.Correct {{𝑳 : Lattice}} where

-- The correctness result states that a transformed program executed
-- with transformed input values gives semantically equivalent outputs
-- (according to the cross-langauge logical relation).  To prove that
-- the statement is generalized, so that the same conclusion holds for
-- any input values that are semantically equivalent to the source
-- inputs.

open import CG as CG hiding (_↑¹ ; _×_ ; here)
open import FG as FG hiding (_×_)
open import CG2FG.Syntax
open import CG2FG.CrossEq
open import CG2FG.Graph
open import Generic.Context.Graph Graph-⟦·⟧ᵗ

open import Function using (flip)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _∧_)

-- Correctnesss for pure steps (the store does not change in FG).
cg2fgᴾ : ∀ {Γ τ} {θ : CG.Env Γ} {θ' : FG.Env ⟦ Γ ⟧ᶜ} {e : CG.Expr Γ τ} {v : CG.Value τ} →
           (p : FG.PState) (pc : Label) →
           θ' ↓≈⟨ pc ⟩ᵉ θ →
           e ⇓ᴾ⟨ θ ⟩ v →
           let FG.⟨ Σ , μ ⟩ = p in
           ∃ (λ r → (r ↓≈⟨ pc ⟩ᴿ v) × (⟨ Σ , μ , ⟦ e ⟧ᴱ ⟩ ⇓⟨ θ' , pc ⟩ ⟨ Σ , μ , r ^ pc ⟩))

cg2fgᴾ p pc ≈θ Unit = （） ∧ （） ∧ Unit

cg2fgᴾ p pc ≈θ (Lbl ℓ) = ⌞ ℓ ⌟ ∧ ⌞ ℓ ⌟ ∧ (Lbl ℓ)

cg2fgᴾ p pc ≈θ (Test₁ x₁ x₂ ℓ₁⊑ℓ₂) with cg2fgᴾ p pc ≈θ x₁ | cg2fgᴾ p pc ≈θ x₂
... | _ ∧ ⌞ ℓ₁ ⌟ ∧ x₁' | _ ∧ ⌞ ℓ₂ ⌟ ∧ x₂'
  = _ ∧ trueᴿ ∧ Test₁ x₁' x₂' ℓ₁⊑ℓ₂ (idem-⊔' pc)

cg2fgᴾ p pc ≈θ (Test₂ x₁ x₂ ℓ₁⋤ℓ₂)  with cg2fgᴾ p pc ≈θ x₁ | cg2fgᴾ p pc ≈θ x₂
... | _ ∧ ⌞ ℓ₁ ⌟ ∧ x₁' | _ ∧ ⌞ ℓ₂ ⌟ ∧ x₂'
  = _ ∧ falseᴿ ∧ Test₂ x₁' x₂' ℓ₁⋤ℓ₂ (idem-⊔' pc)

cg2fgᴾ p pc ≈θ (Wken ⊆₁ x) with cg2fgᴾ p pc (slice-↓≈ ⊆₁ ≈θ) x
... | v ∧ ≈v ∧ x' = v ∧ ≈v ∧ (Wken ⟦ ⊆₁ ⟧⊆ x')

cg2fgᴾ _ pc ≈θ (Var τ∈Γ) with !!-↓≈ τ∈Γ ≈θ
... | p ↓ ≈r = _ ∧ ≈r ∧ Var ⟦ τ∈Γ ⟧∈ (sym (ub' p))

cg2fgᴾ p pc ≈θ SThunk = _ ∧ Thunk′ (mkCg2Fgᵀ _) ≈θ ∧ Fun

cg2fgᴾ p pc ≈θ Fun = _ ∧ Fun (mkCg2Fgᴱ _) ≈θ ∧ Fun

cg2fgᴾ p pc ≈θ (App x x₁ x₂) with cg2fgᴾ p pc ≈θ x | cg2fgᴾ p pc ≈θ x₁
... | ⟨ ._ , _ ⟩ᶜ ∧ Fun {{c = c}} g ≈θ' ∧ x' | r₁ ∧  ≈r₁ ∧ x₁' with ≡-MkCtx c
... | refl rewrite !-MkCtx c (mkCtx _) with cg2fgᴾ p pc ((refl-⊑ ↓ ≈r₁) ∷ ≈θ') x₂
... | r ∧ ≈r ∧ x₂' rewrite ≡-Cg2Fgᴱ g = r ∧ ≈r ∧ App x' x₁' (idem-⊔' pc) x₂'

cg2fgᴾ p pc ≈θ (Inl x) with cg2fgᴾ p pc ≈θ x
... | r ∧ ≈r ∧ x' = inl (r ^ pc) ∧ Inl (refl-⊑ ↓ ≈r) ∧ Inl x'

cg2fgᴾ p pc ≈θ (Inr x) with cg2fgᴾ p pc ≈θ x
... | r ∧ r≈ ∧ x' = inr (r ^ pc) ∧ Inr (refl-⊑ ↓ r≈) ∧ Inr x'

cg2fgᴾ p pc ≈θ (Case₁ x x₁) with cg2fgᴾ p pc ≈θ x
... | inl r₁ ∧ Inl ≈r₁ ∧ x' with cg2fgᴾ p pc (≈r₁ ∷ ≈θ) x₁
... | r ∧ ≈r ∧ x₁' = r ∧ ≈r ∧ Case₁ x' (idem-⊔' pc) x₁'

cg2fgᴾ p pc ≈θ (Case₂ x x₁) with cg2fgᴾ p pc ≈θ x
... | inr r₂ ∧ Inr ≈r₂ ∧ x' with cg2fgᴾ p pc (≈r₂ ∷ ≈θ) x₁
... | r ∧ ≈r ∧ x₁' = r ∧ ≈r ∧ Case₂ x' (idem-⊔' pc) x₁'

cg2fgᴾ p pc ≈θ (Pair x₁ x₂) with cg2fgᴾ p pc ≈θ x₁ | cg2fgᴾ p pc ≈θ x₂
... | r₁ ∧ ≈r₁ ∧ x₁' | r₂ ∧ ≈r₂ ∧ x₂' = _ ∧ Pair (refl-⊑ ↓ ≈r₁) (refl-⊑ ↓ ≈r₂) ∧ (Pair x₁' x₂')

cg2fgᴾ p pc ≈θ (Fst x) with cg2fgᴾ p pc ≈θ x
... | ⟨ r₁ ^ ℓ₁ , _ ⟩  ∧ Pair (ℓ₁⊑pc ↓ ≈r₁) _ ∧ x' = r₁ ∧ ≈r₁ ∧ (Fst x' (sym (ub' ℓ₁⊑pc)))

cg2fgᴾ p pc ≈θ (Snd x) with cg2fgᴾ p pc ≈θ x
... | ⟨ _ , r₂ ^ ℓ₂ ⟩  ∧ Pair _  (ℓ₂⊑pc ↓ ≈r₂) ∧ x' = r₂ ∧ ≈r₂ ∧ (Snd x' (sym (ub' ℓ₂⊑pc)))

open _↓≈ᴾ_

mutual

  -- Forcing semantics.
  cg2fgᶠ : ∀ {Γ τ θ₂ c₁' c₂} {θ₁ : CG.Env Γ} {c₁ : EConf Γ (LIO τ)} →
             let ⟨ _ , _ , pc , _ ⟩ = c₁ in
               θ₂ ↓≈⟨ pc ⟩ᵉ θ₁ →
               c₂ ↓≈ᴵ c₁ →
               c₁ ⇓ᶠ⟨ θ₁ ⟩ c₁' →
                 ∃ (λ c₂' → c₂' ↓≈ᶜ c₁' × c₂ ⇓⟨ θ₂ , pc ⟩ c₂' )
  cg2fgᶠ {c₂ = ⟨ Σ' , μ' , _ ⟩} {c₁ = ⟨ Σ , _ , pc , _ ⟩} ≈θ ⌞ ≈ᴾ ⌟ᴵ (Force x x₁) with cg2fgᴾ FG.⟨ Σ' , μ' ⟩ pc ≈θ x
  ... | ⟨ ._ , θ' ⟩ᶜ ∧ Thunk′ {{c = c}} g ≈θ' ∧ x'  with ≡-MkCtx c
  ... | refl rewrite !-MkCtx c (mkCtx _) with cg2fg ≈θ' ⌞ ≈ᴾ ⌟ᵀ x₁
  ... | c₂' ∧ ≈c₂  ∧ x₁' rewrite ≡-Cg2Fgᵀ g = c₂' ∧ ≈c₂ ∧ App x' (Id Unit) (idem-⊔' _) (↑¹-⇓ x₁')

  -- Thunk semantics.
  cg2fg : ∀ {Γ τ θ₂ c₂ c₁'} {θ₁ : CG.Env Γ} {c₁ : CG.TConf Γ (LIO τ)} →
            let ⟨ _ , _ , pc , _ ⟩ = c₁ in
              θ₂ ↓≈⟨ pc ⟩ᵉ θ₁ →
              c₂ ↓≈ᵀ c₁ →
              c₁ ⇓⟨ θ₁ ⟩ c₁' →
              ∃ (λ c₂' → c₂' ↓≈ᶜ c₁' × c₂ ⇓⟨ θ₂ , pc ⟩ c₂' )
  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (Return {pc = pc} x) with cg2fgᴾ _ pc ≈θ x
  ... | r ∧ ≈r ∧ x' = ⟨ _ , _ , r ^ pc ⟩ ∧ ⟨ ≈ᴾ , ≈r ⟩ ∧ x'

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (Bind {Σ' = Σ'} {pc = pc} {pc'} {pc''} x x₁) with stepᶠ-⊑ x | cg2fgᶠ ≈θ ⌞ ≈ᴾ ⌟ᴵ  x
  ... | pc⊑pc' | ⟨ Σ₁' , _ , r₁' ⟩ ∧ (⟨_,_⟩ {{p}} ≈ᴾ₁ ≈r₁) ∧ x'
    rewrite !-MkTy p (mkTy _) with cg2fgᶠ ((refl-⊑ ↓ ≈r₁) ∷ ≈ᵉ-⊑ ≈θ pc⊑pc') ⌞ ≈ᴾ₁ ⌟ᴵ x₁
  ... | c ∧ ≈c ∧ x₁' = c ∧ ≈c ∧
          (App Fun x' (idem-⊔' _)
            (Taint (sym eq) (LabelOf (Var here (ub' (join-⊑₁ pc pc')))) x₁'
              (trans-⊑ (join-⊑ (join-⊑' pc⊑pc' refl-⊑) pc⊑pc') idem-⊑)))
      where eq =
               begin
                 pc ⊔ (pc ⊔ pc') ⊔ pc
               ≡⟨ cong (λ ℓ → pc ⊔ ℓ ⊔ pc) (ub pc⊑pc') ⟩
                 pc ⊔ pc' ⊔ pc
               ≡⟨ cong (λ ℓ → pc ⊔ ℓ) (ub' pc⊑pc') ⟩
                 pc ⊔ pc'
               ≡⟨ ub pc⊑pc' ⟩
                 pc'
               ∎
               where open ≡-Reasoning

  cg2fg ≈θ (⌞_⌟ᵀ {Σ = Σ} {μ = μ} ≈ᴾ) (Unlabel {pc = pc} {ℓ = ℓ₁} {ℓ' = pc'} x eq) with cg2fgᴾ FG.⟨ Σ , μ ⟩ pc ≈θ x
  ... | Id (⟨ (.(⌞ ℓ₁ ⌟) ^ .ℓ₁) , r ^ ℓ₂ ⟩ ^ ℓ₄) ∧ Labeled {v' = r' ^ ℓ₃} ℓ₄⊑pc (ℓ₃⊑pc' ↓ r≈) ∧ x'
    rewrite eq = c ∧ ≈c ∧ ⇓c
      where
            c = ⟨ _ , _ , r ^ (pc ⊔ ℓ₁) ⟩

            ≈c = ⟨ ≈ᴾ , ≈ᴿ-⊑ r≈ (join-⊑₂ ℓ₁ pc) ⟩

            eq₁ : pc' ⊔ ℓ₃ ≡ pc ⊔ ℓ₁
            eq₁ = pc' ⊔ ℓ₃ ≡⟨ cong (flip _⊔_ ℓ₃) eq ⟩ (pc ⊔ ℓ₁) ⊔ ℓ₃ ≡⟨ ub' (trans-⊑ ℓ₃⊑pc' (join-⊑₂ ℓ₁ pc)) ⟩ pc ⊔ ℓ₁ ∎
              where open ≡-Reasoning

            eq₂ =
              begin
                (pc' ⊔ pc) ⊔ ℓ₃
              ≡⟨ cong (λ ℓ → ℓ ⊔ ℓ₃) (sym-⊔ pc' pc) ⟩
                (pc ⊔ pc') ⊔ ℓ₃
              ≡⟨ sym (assoc-⊔ pc pc' ℓ₃) ⟩
                pc ⊔ pc' ⊔ ℓ₃
              ≡⟨ cong (λ ℓ → pc ⊔ ℓ) eq₁ ⟩
                pc ⊔ pc ⊔ ℓ₁
              ≡⟨ assoc-⊔ pc pc ℓ₁ ⟩
                (pc ⊔ pc) ⊔ ℓ₁
              ≡⟨ cong (λ pc → pc ⊔ ℓ₁) (idem-⊔ pc) ⟩
                (pc ⊔ ℓ₁)
              ∎
              where open ≡-Reasoning

            ⇓c = App Fun (UnId x' (sym (ub' ℓ₄⊑pc))) (idem-⊔' pc)
                     (Taint eq
                       (Fst (Var here (idem-⊔' pc)) eq)
                       (Snd (Var here refl) (sym eq₂))
                       refl-⊑)

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (ToLabeled {pc = pc} {pc' = pc'}  x) with sym (ub (stepᶠ-⊑ x)) | cg2fgᶠ ≈θ ⌞ ≈ᴾ ⌟ᴵ x
  ... | pc'≡ | ⟨ Σ' , _ , r ^ .pc' ⟩  ∧ ⟨ ≈ᴾ' , r≈ ⟩ ∧ x' = c' ∧ ≈ᶜ ∧ c⇓c'
    where c' = ⟨ Σ' , _ , Id (⟨ ⌞ pc' ⌟ ^ pc' , r ^ pc' ⟩ ^ pc ) ^ pc ⟩
          ≈ᶜ = ⟨ ≈ᴾ' , Labeled refl-⊑ (refl-⊑ ↓ r≈) ⟩
          c⇓c' = App Fun x' (idem-⊔' pc) (Id (Pair (LabelOf (Var here pc'≡)) (Var here pc'≡)))


  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (LabelOf {pc = pc} x refl) with cg2fgᴾ _ pc ≈θ x
  ... | Id (⟨ ⌞ ℓ ⌟ ^ ℓ' , x₃ ⟩ ^ ℓ'') ∧ Labeled ℓ''⊑pc ≈r ∧ x'
    = ⟨ _ , _ , ⌞ ℓ ⌟ ^ (pc ⊔ ℓ) ⟩ ∧ ⟨ ≈ᴾ , ⌞ ℓ ⌟ ⟩ ∧ Fst (UnId x' (sym (ub' ℓ''⊑pc))) refl

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (GetLabel {pc = pc}) = ⟨ _ , _ , ⌞ pc ⌟ ^ pc ⟩  ∧ ⟨ ≈ᴾ , ⌞ pc ⌟ ⟩ ∧ GetLabel

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (Taint {pc = pc} x refl) with cg2fgᴾ _ pc ≈θ x
  ... | ⌞ ℓ ⌟ ∧ ⌞ .ℓ ⌟ ∧ x'
    = _ ∧ ⟨ ≈ᴾ , （） ⟩ ∧ Taint refl x' Unit (join-⊑₁ pc ℓ)

  cg2fg ≈θ (⌞_⌟ᵀ {Σ = Σ}  ⟨ ≈Σ , ≈μ ⟩)  (New {pc = pc} x₁ pc⊑ℓ) with sym (ub pc⊑ℓ) | cg2fgᴾ _ pc ≈θ x₁
  ... | pc-⊔-ℓ | Id (⟨ ⌞ ℓ ⌟ ^ .ℓ , r ^ ℓ' ⟩ ^ _) ∧ Labeled ⊑pc (ℓ'⊑ℓ ↓ ≈r) ∧ x₁' = c ∧ ≈c  ∧ ⇓c
    where
       M = Σ ℓ
       ≈M = ≈Σ ℓ
       c = ⟨ Σ FG.[ ℓ ↦ FG.snocᴹ M r ]ˢ , _ , Refᴵ ℓ FG.∥ M ∥ᴹ ^ pc ⟩
       ≈c = ⟨ ⟨ update-↓≈ˢ ≈Σ (new-↓≈ᴹ ≈M ≈r) , ≈μ ⟩ , Ref′ ℓ ∥ ≈M ∥-↓≈ᴹ ⟩
       ⇓c = New
            (App Fun (UnId x₁' (sym (ub' ⊑pc))) (idem-⊔' pc)
              (Taint pc-⊔-ℓ
                (Fst (Var here (idem-⊔' pc)) pc-⊔-ℓ)
                (Snd (Var here (trans pc-⊔-ℓ (sym-⊔ pc ℓ))) (sym (ub' ℓ'⊑ℓ)))
                refl-⊑))

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (Read {pc = pc} x₁ n∈M refl) with cg2fgᴾ _ pc ≈θ x₁
  ... | Refᴵ .ℓ .n ∧ Refᴵ ℓ n ∧ x₁' with lookup-↓≈ᴹ n∈M (store-↓≈ˢ ≈ᴾ ℓ)
  ... | r ∧ n∈M' ∧ ≈r
    = ⟨ _ , _ , r ^ (pc ⊔ ℓ) ⟩ ∧ ⟨ ≈ᴾ , ≈ᴿ-⊑ ≈r (join-⊑₂ ℓ pc) ⟩ ∧ Read x₁' n∈M' (sym-⊔ _ _)

  cg2fg ≈θ ⌞ ⟨ ≈ᴾ , ≈μ ⟩ ⌟ᵀ (Write {pc = pc} x₁ x₂ pc⊑ℓ ℓ₁⊑ℓ M≔) with cg2fgᴾ _ pc ≈θ x₁ | cg2fgᴾ _ pc ≈θ x₂
  ... | Refᴵ .ℓ .n ∧ Refᴵ ℓ n ∧ x₁' | Id (⟨ (⌞ ℓ₁ ⌟ ^ .ℓ₁) , r ^ ℓ' ⟩ ^ _ ) ∧ Labeled ⊑pc (ℓ'⊑ℓ₁ ↓ ≈r) ∧ x₂'
    with write-↓≈ᴹ (≈ᴿ-⊑ ≈r ℓ₁⊑ℓ) M≔ (≈ᴾ ℓ)
  ... | M ∧ M≔' ∧ ≈M = c ∧ ≈c ∧ ⇓c
    where c = ⟨ _ , _ , （） ^ pc ⟩
          ≈c = ⟨ ⟨ update-↓≈ˢ ≈ᴾ ≈M , ≈μ ⟩ , （） ⟩
          ⇓c = Write x₁' pc⊑ℓ (Snd (UnId x₂' (sym (ub' ⊑pc))) refl) (join-⊑' pc⊑ℓ (trans-⊑ ℓ'⊑ℓ₁ ℓ₁⊑ℓ)) M≔'

  cg2fg ≈θ ⌞ ≈ᴾ ⌟ᵀ (LabelOfRef {pc = pc} x refl) with cg2fgᴾ _ pc ≈θ x
  ... | Refᴵ .ℓ .n ∧ Refᴵ ℓ n ∧ x' = ⟨ _ , _ , ⌞ ℓ ⌟ ^ (pc ⊔ ℓ) ⟩ ∧ ⟨ ≈ᴾ , ⌞ ℓ ⌟ ⟩ ∧ (LabelOfRef x' (sym-⊔ pc ℓ))

-- To prove the transformation correct we use the generalized theorem and
-- relfexivity, ie.
⟦·⟧-correct : ∀ {τ Γ c₁'} {θ : CG.Env Γ} {c₁ : CG.EConf Γ (LIO τ)} →
                let ⟨ _ , _ , pc , _ ⟩ = c₁ in
                c₁ ⇓ᶠ⟨ θ ⟩ c₁' →
                ∃ (λ c₂' → c₂' ↓≈ᶜ c₁' × ⟦ c₁ ⟧ᴵ ⇓⟨ ⟦ θ ⟧ᵉ pc  , pc ⟩ c₂' )
⟦·⟧-correct {θ = θ} {c₁ = c₁} x = cg2fgᶠ (refl-≈⟨ _ ⟩ᵉ θ) (refl-≈ᴵ c₁) x
