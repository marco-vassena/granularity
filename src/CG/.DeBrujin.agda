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
  unit ≟ LIO τ₂ = no (λ ())
  unit ≟ Labeled τ₂ = no (λ ())
  unit ≟ Ref τ₂ = no (λ ())
  (τ₁ × τ₂) ≟ unit = no (λ ())
  (τ₁ × τ₂) ≟ (τ₃ × τ₄) with τ₁ ≟ τ₃ | τ₂ ≟ τ₄
  (τ₁ × τ₃) ≟ (.τ₁ × .τ₃) | yes refl | yes refl = yes refl
  (τ₁ × τ₃) ≟ (τ₂ × τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ × τ₃) ≟ (τ₂ × τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ × τ₂) ≟ (τ₃ + τ₄) = no (λ ())
  (τ₁ × τ₂) ≟ (τ₃ ➔ τ₄) = no (λ ())
  (τ₁ × τ₂) ≟ 𝓛 = no (λ ())
  (τ₁ × τ₂) ≟ LIO τ₃ = no (λ ())
  (τ₁ × τ₂) ≟ Labeled τ₃ = no (λ ())
  (τ₁ × τ₂) ≟ Ref τ₃ = no (λ ())
  (τ₁ + τ₂) ≟ unit = no (λ ())
  (τ₁ + τ₂) ≟ (τ₃ × τ₄) = no (λ ())
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) with τ₁ ≟ τ₂ | τ₃ ≟ τ₄
  (τ₁ + τ₃) ≟ (.τ₁ + .τ₃) | yes refl | yes refl = yes refl
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ + τ₃) ≟ (τ₂ + τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ + τ₂) ≟ (τ₃ ➔ τ₄) = no (λ ())
  (τ₁ + τ₂) ≟ 𝓛 = no (λ ())
  (τ₁ + τ₂) ≟ LIO τ₃ = no (λ ())
  (τ₁ + τ₂) ≟ Labeled τ₃ = no (λ ())
  (τ₁ + τ₂) ≟ Ref τ₃ = no (λ ())
  (τ₁ ➔ τ₂) ≟ unit = no (λ ())
  (τ₁ ➔ τ₂) ≟ (τ₃ × τ₄) = no (λ ())
  (τ₁ ➔ τ₂) ≟ (τ₃ + τ₄) = no (λ ())
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) with τ₁ ≟ τ₂ | τ₃ ≟ τ₄
  (τ₁ ➔ τ₃) ≟ (.τ₁ ➔ .τ₃) | yes refl | yes refl = yes refl
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) | yes refl | no ¬p = no λ { refl → ¬p refl }
  (τ₁ ➔ τ₃) ≟ (τ₂ ➔ τ₄) | no ¬p | r₂ = no λ { refl → ¬p refl }
  (τ₁ ➔ τ₂) ≟ 𝓛 = no (λ ())
  (τ₁ ➔ τ₂) ≟ LIO τ₃ = no (λ ())
  (τ₁ ➔ τ₂) ≟ Labeled τ₃ = no (λ ())
  (τ₁ ➔ τ₂) ≟ Ref τ₃ = no (λ ())
  𝓛 ≟ unit = no (λ ())
  𝓛 ≟ (τ₂ × τ₃) = no (λ ())
  𝓛 ≟ (τ₂ + τ₃) = no (λ ())
  𝓛 ≟ (τ₂ ➔ τ₃) = no (λ ())
  𝓛 ≟ 𝓛 = yes refl
  𝓛 ≟ LIO τ₂ = no (λ ())
  𝓛 ≟ Labeled τ₂ = no (λ ())
  𝓛 ≟ Ref τ₂ = no (λ ())
  LIO τ₁ ≟ unit = no (λ ())
  LIO τ₁ ≟ (τ₂ × τ₃) = no (λ ())
  LIO τ₁ ≟ (τ₂ + τ₃) = no (λ ())
  LIO τ₁ ≟ (τ₂ ➔ τ₃) = no (λ ())
  LIO τ₁ ≟ 𝓛 = no (λ ())
  LIO τ₁ ≟ LIO τ₂ with τ₁ ≟ τ₂
  LIO τ₁ ≟ LIO .τ₁ | yes refl = yes refl
  LIO τ₁ ≟ LIO τ₂ | no ¬p = no λ { refl → ¬p refl }
  LIO τ₁ ≟ Labeled τ₂ = no (λ ())
  LIO τ₁ ≟ Ref τ₂ = no (λ ())
  Labeled τ₁ ≟ unit = no (λ ())
  Labeled τ₁ ≟ (τ₂ × τ₃) = no (λ ())
  Labeled τ₁ ≟ (τ₂ + τ₃) = no (λ ())
  Labeled τ₁ ≟ (τ₂ ➔ τ₃) = no (λ ())
  Labeled τ₁ ≟ 𝓛 = no (λ ())
  Labeled τ₁ ≟ LIO τ₂ = no (λ ())
  Labeled τ₁ ≟ Labeled τ₂ with τ₁ ≟ τ₂
  Labeled τ₁ ≟ Labeled .τ₁ | yes refl = yes refl
  Labeled τ₁ ≟ Labeled τ₂ | no ¬p = no λ { refl → ¬p refl }
  Labeled τ₁ ≟ Ref τ₂ = no (λ ())
  Ref τ₁ ≟ unit = no (λ ())
  Ref τ₁ ≟ (τ₂ × τ₃) = no (λ ())
  Ref τ₁ ≟ (τ₂ + τ₃) = no (λ ())
  Ref τ₁ ≟ (τ₂ ➔ τ₃) = no (λ ())
  Ref τ₁ ≟ 𝓛 = no (λ ())
  Ref τ₁ ≟ LIO τ₂ = no (λ ())
  Ref τ₁ ≟ Labeled τ₂ = no (λ ())
  Ref τ₁ ≟ Ref τ₂ with τ₁ ≟ τ₂
  Ref τ₁ ≟ Ref .τ₁ | yes refl = yes refl
  Ref τ₁ ≟ Ref τ₂ | no ¬p = no λ { refl → ¬p refl }

open import Agda.Builtin.FromNat public

instance
  DeBruijn : ∀ {τ Γ} → Number (τ ∈ Γ)
  DeBruijn = Syntax.DeBruijn _≟_

open Syntax {{...}}
