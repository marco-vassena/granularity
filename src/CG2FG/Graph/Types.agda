module CG2FG.Graph.Types where

open import FG.Types as FG
open import CG.Types as CG
open import CG2FG.Syntax
open import Relation.Binary.PropositionalEquality

data MkTy : CG.Ty → FG.Ty → Set where
  instance
    Unit : MkTy unit unit
    𝓛 : MkTy 𝓛 𝓛
    Prod : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy (τ₁ CG.× τ₂) (τ₁' FG.× τ₂')
    Sum : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy (τ₁ CG.+ τ₂) (τ₁' FG.+ τ₂')
    Labeled : ∀ {τ τ'} → MkTy τ τ' → MkTy (Labeled τ) (Id (𝓛 × τ'))
    Ref : ∀ {τ τ' s} → MkTy τ τ' → MkTy (CG.Ref s τ) (FG.Ref s τ')
    LIO : ∀ {τ τ'} → MkTy τ τ' → MkTy (CG.LIO τ) ((Id unit) FG.➔ τ')
    Fun : ∀ {τ₁ τ₂ τ₁' τ₂'} → MkTy τ₁ τ₁' → MkTy τ₂ τ₂' → MkTy (τ₁ CG.➔ τ₂) (τ₁' FG.➔ τ₂')

Bool′ : MkTy CG.Bool FG.Bool
Bool′ = Sum Unit Unit

instance
  mkTy : ∀ τ → MkTy τ ⟦ τ ⟧ᵗ
  mkTy unit = Unit
  mkTy (τ × τ₁) = Prod (mkTy τ) (mkTy τ₁)
  mkTy (τ + τ₁) = Sum (mkTy τ) (mkTy τ₁)
  mkTy (τ ➔ τ₁) = MkTy.Fun (mkTy τ) (mkTy τ₁)
  mkTy 𝓛 = 𝓛
  mkTy (LIO τ) = LIO (mkTy τ)
  mkTy (Labeled τ) = Labeled (mkTy τ)
  mkTy (Ref s τ) = Ref (mkTy τ)

≡-MkTy : ∀ {τ τ'} → MkTy τ τ' → τ' ≡ ⟦ τ ⟧ᵗ
≡-MkTy Unit = refl
≡-MkTy 𝓛 = refl
≡-MkTy (Prod x x₁) rewrite ≡-MkTy x | ≡-MkTy x₁ = refl
≡-MkTy (Sum x x₁) rewrite ≡-MkTy x | ≡-MkTy x₁ = refl
≡-MkTy (Labeled x) rewrite ≡-MkTy x = refl
≡-MkTy (Ref x) rewrite ≡-MkTy x = refl
≡-MkTy (LIO x) rewrite ≡-MkTy x = refl
≡-MkTy (Fun x x₁) rewrite ≡-MkTy x | ≡-MkTy x₁ = refl

open import Function.Equivalence

-- The relation MkTy is an equivalent representation for the
-- translation function over types.
MkTy-⟦·⟧ᵗ : ∀ {τ τ'} → τ' ≡ ⟦ τ ⟧ᵗ  ⇔  MkTy τ τ'
MkTy-⟦·⟧ᵗ = equivalence (λ { refl → mkTy _ }) ≡-MkTy

instance
  -- Unique proofs
  !-MkTy : ∀ {τ τ'} (p q : MkTy τ τ') → p ≡ q
  !-MkTy Unit Unit = refl
  !-MkTy 𝓛 𝓛 = refl
  !-MkTy (Prod p₁ p₂) (Prod q₁ q₂)
    rewrite !-MkTy p₁ q₁ | !-MkTy p₂ q₂ = refl
  !-MkTy (Sum p₁ p₂) (Sum q₁ q₂)
    rewrite !-MkTy p₁ q₁ | !-MkTy p₂ q₂ = refl
  !-MkTy (Labeled p) (Labeled q) rewrite !-MkTy p q = refl
  !-MkTy (Ref p) (Ref q) rewrite !-MkTy p q = refl
  !-MkTy (LIO p) (LIO q) rewrite !-MkTy p q = refl
  !-MkTy (Fun p₁ p₂) (Fun q₁ q₂)
    rewrite !-MkTy p₁ q₁ | !-MkTy p₂ q₂ = refl

--------------------------------------------------------------------------------
-- TODO: is this ever used?
-- Yes, it is used in the translation of expressions
-- Graph instances

open import Generic.Graph

-- TODO: if we make ctx an instance of our generic container we can reuse the exisiting proofs

Graph-⟦·⟧ᵗ : Graph ⟦_⟧ᵗ
Graph-⟦·⟧ᵗ = record { P = MkTy ; ⌜_⌝ = mkTy ; ⌞_⌟ = ≡-MkTy }

-- Is this eveer used?
-- Derive graph of context generically.
open import Generic.Context.Graph {CG.Ty} {FG.Ty} {⟦_⟧ᵗ} Graph-⟦·⟧ᵗ
  renaming ( S2Tᶜ to MkCtx
           ; mkS2Tᶜ to mkCtx
           ; ≡-S2Tᶜ to ≡-MkCtx
           ; S2T-∈ to Cg2Fg-∈
           ; mkS2T-∈ to mkCg2Fg-∈
           ; ≡-S2T-∈ to ≡-Cg2Fg-∈
           ; S2T-⊆ to Cg2Fg-⊆
           ; mkS2T-⊆ to mkCg2Fg-⊆
           ; ≡-S2T-⊆ to ≡-Cg2Fg-⊆
           ; inj-S2T-∈ to inj-Cg2Fg-∈
           ; inj-⟪_⟫∈ to inj-⟦_⟧∈
           ; inj-S2T-⊆ to inj-Cg2Fg-⊆
           ; inj-⟪_⟫⊆ to inj-⟦_⟧⊆ ) public

-- Derive uniqueness proof generically.
open Unique !-MkTy renaming (!-S2Tᶜ to !-MkCtx) public

--------------------------------------------------------------------------------
open import Generic.CrossEq

-- TODO: rename MkTy to ↓≈ᵗ ?
_↓≈ᵗ_ : FG.Ty → CG.Ty → Set
τ₁ ↓≈ᵗ τ₂ = MkTy τ₂ τ₁

𝑻 : CEq CG.Ty FG.Ty
𝑻 = record { ⟦_⟧ = ⟦_⟧ᵗ ; _↓≈_ = _↓≈ᵗ_ ; ⌞_⌟ = ≡-MkTy ; refl-↓≈ = mkTy ; !-↓≈ = !-MkTy }

-- For labeled values
𝑻ᴸ : CEq CG.Ty FG.Ty
𝑻ᴸ = record
     { ⟦_⟧ = λ τ → ⟦ Labeled τ ⟧ᵗ
     ; _↓≈_ = λ τ₁ τ₂ → MkTy (Labeled τ₂) τ₁
     ; ⌞_⌟ = ≡-MkTy
     ; refl-↓≈ = λ τ → mkTy (Labeled τ)
     ; !-↓≈ = !-MkTy }
