-- TODO: are we using this?
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

instance
  _≟_ : ∀ (τ₁ τ₂ : Ty) → Dec (τ₁ ≡ τ₂)
  unit ≟ unit = yes refl
  unit ≟ (τ₂ × τ₃) = no (λ ())
  unit ≟ (τ₂ + τ₃) = no (λ ())
  unit ≟ (τ₂ ➔ τ₃) = no (λ ())
  unit ≟ 𝓛 = no (λ ())
  unit ≟ Ref τ₂ = no (λ ())
  unit ≟ Id τ₂ = no (λ ())
  (τ₁ × τ₃) ≟ unit = no (λ ())
  (τ₁ × τ₃) ≟ (τ₂ × τ₄) with τ₁ ≟ τ₂ | τ₃ ≟ τ₄
  (τ₁ × τ₃) ≟ (.τ₁ × .τ₃) | yes refl | yes refl = yes refl
  (τ₁ × τ₃) ≟ (τ₂ × τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ × τ₃) ≟ (τ₂ × τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ × τ₃) ≟ (τ₂ + τ₄) = no (λ ())
  (τ₁ × τ₃) ≟ (τ₂ ➔ τ₄) = no (λ ())
  (τ₁ × τ₃) ≟ 𝓛 = no (λ ())
  (τ₁ × τ₃) ≟ Ref τ₂ = no (λ ())
  (τ₁ × τ₃) ≟ Id τ₂ = no (λ ())
  (τ₁ + τ₃) ≟ unit = no (λ ())
  (τ₁ + τ₃) ≟ (τ₂ × τ₄) = no (λ ())
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) with τ₁ ≟ τ₂ | τ₃ ≟ τ₄
  (τ₁ + τ₃) ≟ (.τ₁ + .τ₃) | yes refl | yes refl = yes refl
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ + τ₃) ≟ (τ₂ ➔ τ₄) = no (λ ())
  (τ₁ + τ₃) ≟ 𝓛 = no (λ ())
  (τ₁ + τ₃) ≟ Ref τ₂ = no (λ ())
  (τ₁ + τ₃) ≟ Id τ₂ = no (λ ())
  (τ₁ ➔ τ₃) ≟ unit = no (λ ())
  (τ₁ ➔ τ₃) ≟ (τ₂ × τ₄) = no (λ ())
  (τ₁ ➔ τ₃) ≟ (τ₂ + τ₄) = no (λ ())
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) with τ₁ ≟ τ₂ | τ₃ ≟ τ₄
  (τ₁ ➔ τ₃) ≟ (.τ₁ ➔ .τ₃) | yes refl | yes refl = yes refl
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ ➔ τ₃) ≟ 𝓛 = no (λ ())
  (τ₁ ➔ τ₃) ≟ Ref τ₂ = no (λ ())
  (τ₁ ➔ τ₃) ≟ Id τ₂ = no (λ ())
  𝓛 ≟ unit = no (λ ())
  𝓛 ≟ (τ₂ × τ₃) = no (λ ())
  𝓛 ≟ (τ₂ + τ₃) = no (λ ())
  𝓛 ≟ (τ₂ ➔ τ₃) = no (λ ())
  𝓛 ≟ 𝓛 = yes refl
  𝓛 ≟ Ref τ₂ = no (λ ())
  𝓛 ≟ Id τ₂ = no (λ ())
  Ref τ₁ ≟ unit = no (λ ())
  Ref τ₁ ≟ (τ₂ × τ₃) = no (λ ())
  Ref τ₁ ≟ (τ₂ + τ₃) = no (λ ())
  Ref τ₁ ≟ (τ₂ ➔ τ₃) = no (λ ())
  Ref τ₁ ≟ 𝓛 = no (λ ())
  Ref τ₁ ≟ Ref τ₂ with τ₁ ≟ τ₂
  Ref τ₁ ≟ Ref .τ₁ | yes refl = yes refl
  Ref τ₁ ≟ Ref τ₂ | no ¬p = no λ { refl → ¬p refl }
  Ref τ₁ ≟ Id τ₂ = no (λ ())
  Id τ₁ ≟ unit = no (λ ())
  Id τ₁ ≟ (τ₂ × τ₃) = no (λ ())
  Id τ₁ ≟ (τ₂ + τ₃) = no (λ ())
  Id τ₁ ≟ (τ₂ ➔ τ₃) = no (λ ())
  Id τ₁ ≟ 𝓛 = no (λ ())
  Id τ₁ ≟ Ref τ₂ = no (λ ())
  Id τ₁ ≟ Id τ₂ with τ₁ ≟ τ₂
  Id τ₁ ≟ Id .τ₁ | yes refl = yes refl
  Id τ₁ ≟ Id τ₂ | no ¬p = no λ { refl → ¬p refl }

open import Agda.Builtin.FromNat

instance
  DeBruijn : ∀ {τ Γ} → Number (τ ∈ Γ)
  DeBruijn = Syntax.DeBruijn _≟_
