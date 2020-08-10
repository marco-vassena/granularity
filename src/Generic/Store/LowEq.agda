-- Generic pointwise L-equivalence for stores and memories and their
-- properties.

-- {-# OPTIONS --allow-unsolved-metas #-}


open import Lattice hiding (_≟_)
open import Relation.Binary
open import Generic.Bijection hiding (_↦_ ; _∈_)

module Generic.Store.LowEq
  {Ty : Set}
  {Value : Ty → Set}
  {{𝑳 : Lattice}}
  (_≈⟨_⟩ⱽ_ : IProps.Relᴮ Ty Value)
  (A : Label) where

open import Generic.Store.Base Ty Value as S renaming (_⊆_ to _⊆ˢ_)
-- open import Generic.Memory.LowEq {Ty} {Value} _≈ⱽ_ A as M using (_≈⟨_⟩ᴹ_ ; _≈⟨_,_⟩ᴹ_ ; ⌞_⌟ᴹ) public

open IProps Ty Value
open import Data.Product as P

-- Here I  should make a distinction depending on the label of the cell.
-- All cells should have a label
data _≈⟨_⟩ᶜ_ : ∀ {τ} → Cell τ → Bij → Cell τ → Set where
  -- ⌞_⌟ᴵ : ∀ {τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v ⌟ᴵ ≈⟨ β ⟩ᶜ ⌞ v' ⌟ᴵ
  -- Not sure if I should make a distinction for ℓ ⋤ A ?
  -- Probably no because when we read them, we get tainted with ℓ.
  -- ⌞_⌟ˢ : ∀ {ℓ τ β} → {v v' : Value τ} → v ≈⟨ β ⟩ⱽ v' → ⌞ v , ℓ ⌟ˢ ≈⟨ β ⟩ᶜ ⌞ v' , ℓ ⌟ˢ
  -- TODO: here we need to remove the flow s
  cellᴸ : ∀ {ℓ τ β} → {v v' : Value τ} → ℓ ⊑ A → v ≈⟨ β ⟩ⱽ v' → ⌞ v , ℓ ⌟ ≈⟨ β ⟩ᶜ ⌞ v' , ℓ ⌟
  cellᴴ : ∀ {ℓ ℓ' τ β} → {v v' : Value τ} → ℓ ⋤ A → ℓ' ⋤ A → ⌞ v , ℓ ⌟ ≈⟨ β ⟩ᶜ ⌞ v' , ℓ' ⌟


-- Cells
data _≅⟨_⟩ᶜ_ {τ} (c : Cell τ) (β : Bij) : ∀ {τ'} → Cell τ' → Set where
  ⌞_⌟ : ∀ {c' : Cell τ} → c ≈⟨ β ⟩ᶜ c' → c ≅⟨ β ⟩ᶜ c'

open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------

open import Data.Product
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat renaming (_⊔_ to _⊔ᴺ_)
open import Data.Nat.Properties
open import Data.Maybe
-- open import Generic.Heap.Base 𝑯 as H

--open import Relation.Binary.PropositionalEquality as P

-- Domain inclusion between bijection and heap
_⊆ᴰ_ : Bij → Store → Set
β ⊆ᴰ Σ = ∀ {n : ℕ} → n ∈ᴰ β → n ∈ Σ

_⊆ᴿ_ : Bij → Store → Set
β ⊆ᴿ Σ = ∀ {n : ℕ} → n ∈ᴿ β → n ∈ Σ

⊆ᴰ-⊆ᴿ : ∀ {β Σ} → β ⊆ᴰ Σ → (β ⁻¹) ⊆ᴿ Σ
⊆ᴰ-⊆ᴿ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β

⊆ᴿ-⊆ᴰ : ∀ {β Σ} → β ⊆ᴿ Σ → (β ⁻¹) ⊆ᴰ Σ
⊆ᴿ-⊆ᴰ {β} ⊆ (n , x) = ⊆ (n , left-inverse-of x)
  where open Bijectionᴾ β

-- Homogeneous L-equivalence.
-- TODO: do we ever use this?
Lift-≈ : Store → Store → Bij → Set
Lift-≈ Σ₁ Σ₂ β =
  ∀ {n₁ n₂ τ} {c₁ c₂ : Cell τ} →
    (n₁ , n₂) ∈ᵗ β →
    n₁ ↦ c₁ ∈ Σ₁ → n₂ ↦ c₂ ∈ Σ₂ →
    c₁ ≈⟨ β ⟩ᶜ c₂

-- For proving properties (cf. transitivity) *heterogeneous* L-equivalence
-- is more convenient.
Lift-≅ : Store → Store → Bij → Set
Lift-≅ Σ₁ Σ₂ β =
  ∀ {n₁ n₂ τ₁ τ₂} {c₁ : Cell τ₁} {c₂ : Cell τ₂} →
    (n₁ , n₂) ∈ᵗ β →
     n₁ ↦ c₁ ∈ Σ₁ → n₂ ↦ c₂ ∈ Σ₂ →
     c₁ ≅⟨ β ⟩ᶜ c₂
  -- where open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_

-- -- TODO: update
-- -- Two heaps are A-equivalent up to bijection β iff the low addresses
-- -- related by the bijection correspond to related values in the
-- -- respective heaps. Since the domain and the range of the bijection
-- -- is indexed with the size of the (low parts of) heaps, the lookups
-- -- are safe.  To index the bijection correctly, the relation must
-- -- first introduce the heaps and then the bijection. The following
-- -- definition defines the usual infix operator as syntatic sugar.

-- Definition inspired by "Stack-based Access Control and Secure
-- Information Flow" by Banerjee and Naumann.
record _≈⟨_⟩ˢ_ (Σ₁ : Store) (β : Bij) (Σ₂ : Store) : Set where

  field dom-⊆ : β ⊆ᴰ Σ₁
        rng-⊆ : β ⊆ᴿ Σ₂
        lift-≅ : Lift-≅ Σ₁ Σ₂ β

  -- Homogeneous (same type) lifting is implied by the heterogenous lifting.
  lift-≈ : Lift-≈ Σ₁ Σ₂ β
  lift-≈ x ∈₁ ∈₂ with lift-≅ x ∈₁ ∈₂
  lift-≈ x ∈₁ ∈₂ | ⌞ ≈ⱽ ⌟ = ≈ⱽ

-- -- _≈ˢ_ : Store → Store → Set
-- -- Σ₁ ≈ˢ Σ₂ = Σ Bij⟨ Σ₁ , Σ₂ ⟩ (λ β → Σ₁ ≈⟨ β ⟩ˢ Σ₂)

module Props (𝑽 : IsEquivalenceᴮ _≈⟨_⟩ⱽ_ ) where

  open import Generic.LValue Ty Value
  -- open L.HasLabel 𝑯
  -- open import Generic.Value.HLowEq {Ty} {Value} _≈⟨_⟩ⱽ_
  -- open import Generic.Store.Lemmas 𝑯
  -- open Props 𝑽
  open import Relation.Binary.PropositionalEquality
  import Function as F

  open IsEquivalenceᴮ 𝑽 renaming
    ( Dom to ∣_∣ⱽ
    ; reflᴮ to refl-≈ⱽ
    ; symᴮ to sym-≈ⱽ
    ; transᴮ to trans-≈ⱽ
    ; wkenᴮ to wken-≈ⱽ) public


  open import Generic.Store.Valid Ty Value ∣_∣ⱽ renaming (∥_∥ᶜ to ∣_∣ᶜ)

  refl-≈ᶜ : ∀ {τ} {c : Cell τ} → c ≈⟨ ι ∣ c ∣ᶜ ⟩ᶜ c
  -- refl-≈ᶜ {c = ⌞ ≈ⱽ ⌟ᴵ} = ⌞ refl-≈ⱽ ⌟ᴵ
  -- refl-≈ᶜ {c = ⌞ ≈ⱽ ⌟ˢ} = ⌞ refl-≈ⱽ ⌟ˢ
  refl-≈ᶜ {c = ⌞ v , ℓ ⌟ } with ℓ ⊑? A
  ... | yes ℓ⊑A  = cellᴸ ℓ⊑A refl-≈ⱽ
  ... | no ℓ⋤A  = cellᴴ ℓ⋤A ℓ⋤A

  wken-≈ᶜ : ∀ {τ n m} {c₁ c₂ : Cell τ} → n ≤ m → c₁ ≈⟨ ι n ⟩ᶜ c₂ → c₁ ≈⟨ ι m ⟩ᶜ c₂
  -- wken-≈ᶜ n≤m ⌞ ≈ⱽ ⌟ᴵ = ⌞ wken-≈ⱽ n≤m ≈ⱽ ⌟ᴵ
  -- wken-≈ᶜ n≤m ⌞ ≈ⱽ ⌟ˢ = ⌞ wken-≈ⱽ n≤m ≈ⱽ ⌟ˢ
  wken-≈ᶜ n≤m (cellᴸ x x₁) = cellᴸ x (wken-≈ⱽ n≤m x₁)
  wken-≈ᶜ n≤m (cellᴴ x x₁) = cellᴴ x x₁

  wken-≅ᶜ : ∀ {τ₁ τ₂ n m} {c₁ : Cell τ₁} {c₂ : Cell τ₂} →
            n ≤ m → c₁ ≅⟨ ι n ⟩ᶜ c₂ → c₁ ≅⟨ ι m ⟩ᶜ c₂
  wken-≅ᶜ n≤m ⌞ x ⌟ = ⌞ (wken-≈ᶜ n≤m x) ⌟


  sym-≈ᶜ : ∀ {τ β} {c₁ c₂ : Cell τ} → c₁ ≈⟨ β ⟩ᶜ c₂ → c₂ ≈⟨ β ⁻¹ ⟩ᶜ c₁
  sym-≈ᶜ (cellᴸ x x₁) = cellᴸ x (sym-≈ⱽ x₁)
  sym-≈ᶜ (cellᴴ x x₁) = cellᴴ x₁ x
  -- sym-≈ᶜ ⌞ ≈ⱽ ⌟ᴵ = ⌞ sym-≈ⱽ ≈ⱽ ⌟ᴵ
  -- sym-≈ᶜ ⌞ ≈ⱽ ⌟ˢ = ⌞ sym-≈ⱽ ≈ⱽ ⌟ˢ

  trans-≈ᶜ : ∀ {τ β₁ β₂} {c₁ c₂ c₃ : Cell τ} →
               c₁ ≈⟨ β₁ ⟩ᶜ c₂ →
               c₂ ≈⟨ β₂ ⟩ᶜ c₃ →
               c₁ ≈⟨ β₂ ∘ β₁ ⟩ᶜ c₃
  trans-≈ᶜ (cellᴸ x ≈₁) (cellᴸ x₂ ≈₂) = cellᴸ x (trans-≈ⱽ ≈₁ ≈₂)
  trans-≈ᶜ (cellᴸ x ≈₁) (cellᴴ x₂ _) = ⊥-elim (x₂ x)
  trans-≈ᶜ (cellᴴ x x₂) (cellᴸ x₃ ≈₂) = ⊥-elim (x₂ x₃)
  trans-≈ᶜ (cellᴴ x _) (cellᴴ x₂ x₃) = cellᴴ x x₃
  -- trans-≈ᶜ ⌞ ≈₁ ⌟ᴵ ⌞ ≈₂ ⌟ᴵ = ⌞ trans-≈ⱽ ≈₁ ≈₂ ⌟ᴵ
  -- trans-≈ᶜ ⌞ ≈₁ ⌟ˢ ⌞ ≈₂ ⌟ˢ = ⌞ trans-≈ⱽ ≈₁ ≈₂ ⌟ˢ

  sym-≅ᶜ : ∀ {τ₁ τ₂ β} {c₁ : Cell τ₁} {c₂ : Cell τ₂} →
             c₁ ≅⟨ β ⟩ᶜ c₂ → c₂ ≅⟨ β ⁻¹ ⟩ᶜ c₁
  sym-≅ᶜ ⌞ ≈ᶜ ⌟ = ⌞ sym-≈ᶜ ≈ᶜ ⌟

  trans-≅ᶜ : ∀ {β₁ β₂ τ₁ τ₂ τ₃} {c₁ : Cell τ₁}
               {c₂ : Cell τ₂} {c₃ : Cell τ₃} →
               c₁ ≅⟨ β₁ ⟩ᶜ c₂ →
               c₂ ≅⟨ β₂ ⟩ᶜ c₃ →
               c₁ ≅⟨ β₂ ∘ β₁ ⟩ᶜ c₃
  trans-≅ᶜ ⌞ ≈₁ ⌟ ⌞ ≈₂ ⌟ = ⌞ trans-≈ᶜ ≈₁ ≈₂ ⌟

  -- TODO: Why don't I compute the bound in ∥_∥ (commented code)?  It
  -- seems I could remove the assumptions about the valid store.  No,
  -- it would not help because dom-⊆ and rng-⊆ (the doamin/range of
  -- the bijection is included in the domain of the store) would not
  -- hold in general.
  ∣_∣ˢ : Store → ℕ
  -- ∣ [] ∣ˢ = 0
  -- ∣ c ∷ Σ ∣ˢ = ∣ c ∣ᶜ ⊔ᴺ ∣ Σ ∣ˢ
  ∣_∣ˢ = ∥_∥

  -- A cell is valid for a store if the domain of its content points
  -- inside the store.
  -- Validᶜ : ∀ {s τ} → Cell s τ → Store → Set
  -- Validᶜ c Σ = ∣ c ∣ᶜ ≤ ∥ Σ ∥

  -- Validˢ : Store → Set
  -- Validˢ Σ = ∀ {τ s n} {c : Cell τ s} → n ↦ c ∈ Σ → Validᶜ c Σ

  refl-⊆ᴰ : ∀ {Σ} → ι ∣ Σ ∣ˢ ⊆ᴰ Σ
  refl-⊆ᴰ {Σ} (n , ∈ᴮ) with Id.lemma ∣ Σ ∣ˢ ∈ᴮ
  ... | refl , n< = <-∈ n<

  refl-≈ˢ : ∀ {Σ} {{validˢ : Validˢ Σ}} → Σ ≈⟨ ι ∣ Σ ∣ˢ ⟩ˢ Σ
  refl-≈ˢ {Σ} {{validˢ}} =
    record { dom-⊆ = dom-⊆
           ; rng-⊆ = rng-⊆
           ; lift-≅ = lift-≅ }
    where
          -- Use Generic lemma
          open Id ∣ Σ ∣ˢ
          dom-⊆ : ι ∣ Σ ∣ˢ ⊆ᴰ Σ
          dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          rng-⊆ : ι ∣ Σ ∣ˢ ⊆ᴿ Σ
          rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
          ... | refl , n< = <-∈ n<

          -- Here I need to know that references in the heap are valid
          -- (point to the heap) to prove that they are related by the
          -- finite identity bijection of size ∣ Σ ∣ˢ.  Intuitively if
          -- Σ = [ 0 ↦ Refˢ L 1 ] I cannot prove that Σ ≈⟨ ι 1 ⟩ Σ,
          -- because Refˢ L 1 ≈⟨ ι 1 ⟩ Refˢ L 1, because ι 1 = 0 ↔ 0,
          -- i.e., 1 is not defined in the bijection.
          -- Why ... it seems that this definition works ...
          lift-≅ : Lift-≅ Σ Σ (ι ∣ Σ ∣ˢ)
          lift-≅ {_} {_} {τ₁} {τ₂} {v₁} {v₂} x ∈₁ ∈₂ rewrite idᴾ-≡ x with inj-∈′ ∈₁ ∈₂
          ... | refl , refl = ⌞ (wken-≈ᶜ (validˢ ∈₁) refl-≈ᶜ) ⌟

  sym-≈ˢ : ∀ {β Σ₁ Σ₂} → Σ₁ ≈⟨ β ⟩ˢ Σ₂ → Σ₂ ≈⟨ β ⁻¹ ⟩ˢ Σ₁
  sym-≈ˢ {β} {Σ₁} {Σ₂} ≈ =
    record { dom-⊆ = ⊆ᴿ-⊆ᴰ {β} rng-⊆
           ; rng-⊆ = ⊆ᴰ-⊆ᴿ {β} dom-⊆
           ; lift-≅ = λ ∈ᴮ ∈₁ ∈₂ → sym-≅ᶜ (lift-≅ (right-inverse-of ∈ᴮ) ∈₂ ∈₁)
           }
    where open _≈⟨_⟩ˢ_ ≈
          open Bijectionᴾ (β ⁻¹)

  -- Where are we supposed to use wken-≈ˢ ?

  -- Define Σ₁ ⊆ᴴ Σ₂ such that Σ₂ only adds secret (H) cells
  --
  -- Add  Σ₁ ⊆ᴴ Σ₂ as an assumption
  -- Rename wken-≈ to high-extension, we probably need similar lemmas for values etc.
  --   --> How does this work for FS references? We don't know the label.
  --   --> For v : Ref n, v' : Ref n', such that v ≈⟨ ι m ⟩ v', we know n ≡ n',
  --       Then, if n <= m, v ≈⟨ ι n ⟩ v' (low allocation)
  --       Otherwise, if n > m then v ≈⟨ ι m ⟩ v' because n ≡ n' are not in the bijection (high allocation)
  --   --> How does this work for FI references? Maybe we need extra assumptions.
  --
  -- TODO: remove
  -- Maybe it's too strong Σ and Σ'
  -- It should be the smallest!
  -- The bijection decides what should be related. So I must keep the smalles
  -- otherwise I would need to relate secret (new) cells
--   wken-≈ˢ : ∀ {Σ Σ' n m} → n ≤ m → Σ ≈⟨ ι m ⟩ˢ Σ' → Σ ≈⟨ ι n ⟩ˢ Σ'
--   wken-≈ˢ {Σ} {Σ'} {n} {m} n≤m ≈ =
--     record { dom-⊆ = dom-⊆ᴰ
--            ; rng-⊆ = rng-⊆ᴿ
--            ; lift-≅ = lift-≅′  }

--     where open _≈⟨_⟩ˢ_ ≈

--           dom-⊆ᴰ : ι n ⊆ᴰ Σ
--           dom-⊆ᴰ (n , ∈₁) = dom-⊆ (_ , (ι-⊆ n≤m ∈₁))

--           rng-⊆ᴿ : ι n ⊆ᴿ Σ'
--           rng-⊆ᴿ (n , ∈₁) = rng-⊆ (_ , ι-⊆ n≤m ∈₁)

--           lift-≅′ : Lift-≅ Σ Σ' (ι n)
--           lift-≅′ {a} {b} {τ} {τ'} {v₁} {v₂} ∈ᴮ ∈₁ ∈₂ = {!!}
--           -- (a , b) ∈ᵗ ι n ⇒ a = b
--           -- a ≤? m
--           -- yes: a ≤ m ∧ b ≤ m: lift from old
--           -- no:

--           -- wken-≅ᶜ {!n≤m!} (lift-≅ (ι-⊆ n≤m ∈ᴮ) ∈₁ ∈₂)
--           -- with ι-≡ ∈ᴮ
--           -- lift-≅′ {n₁} {.n₁} {τ₁} {τ₂} {s₁} {s₂} ∈ᴮ ∈₁ ∈₂ | refl with ι-⊆ n≤m ∈ᴮ
--           -- ... | r = {!lift-≅ r ∈₁ ∈₂!}
-- -- {!lift-≅ ∈ᴮ!}


  trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} {β₁ β₂} →
               Σ₁ ≈⟨ β₁ ⟩ˢ Σ₂ →
               Σ₂ ≈⟨ β₂ ⟩ˢ Σ₃ →
               Σ₁ ≈⟨ β₂ ∘ β₁ ⟩ˢ Σ₃
  trans-≈ˢ {Σ₁} {Σ₂} {Σ₃} {β₁ = β₁} {β₂} ≈₁ ≈₂ =
    record { dom-⊆ = dom-⊆ᴰ
           ; rng-⊆ = rng-⊆ᴿ
           ; lift-≅ = lift-≅′ }
    where open _≈⟨_⟩ˢ_

          dom-⊆ᴰ : (β₂ ∘ β₁) ⊆ᴰ Σ₁
          dom-⊆ᴰ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = dom-⊆ ≈₁ (b , ab∈)

          rng-⊆ᴿ : (β₂ ∘ β₁) ⊆ᴿ Σ₃
          rng-⊆ᴿ (n , ∈ᴮ) with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) = rng-⊆ ≈₂ (b , bc∈) -- rng-⊆ ≈₁ (b , bc∈)

          lift-≅′ : Lift-≅ Σ₁ Σ₃ (β₂ ∘ β₁)
          lift-≅′ {a} {c} {τ} {v₁} {v₃} ∈ᴮ ∈₁ ∈₃ with split-∈ᵗ {β₁ = β₁} {β₂} ∈ᴮ
          ... | (b , ab∈ , bc∈) with rng-⊆ ≈₁ (_ , ab∈) | dom-⊆ ≈₂ (_ , bc∈)
          ... | τ₂ , c₂ , ∈₂ | τ₂' , c₂' , ∈₂' with inj-∈′ ∈₂ ∈₂'
          ... | refl , refl = trans-≅ᶜ (lift-≅ ≈₁ ab∈ ∈₁ ∈₂) (lift-≅ ≈₂ bc∈ ∈₂' ∈₃)

  -- This lemma constructs the double dashed (||) edged of the square
  -- by using symmetry and transitivity of L-equvialence. The
  -- bijection of this edge is obtained by composing the other
  -- bijection as the diagram below shows.
  --
  --        β₁
  --   Σ₁ ------ Σ₁'
  --   |         ||
  -- β |         || β' = β₂ ∘ β ∘ β₁⁻¹
  --   |         ||
  --   Σ₂ ------ Σ₂'
  --        β₂
  --
  square-≈ˢ : ∀ {Σ₁ Σ₁' Σ₂ Σ₂' β β₁ β₂} →
                Σ₁ ≈⟨ β ⟩ˢ Σ₂ →
                Σ₁ ≈⟨ β₁ ⟩ˢ Σ₁' →
                Σ₂ ≈⟨ β₂ ⟩ˢ Σ₂' →
                Σ₁' ≈⟨ β₂ ∘ β ∘ (β₁ ⁻¹) ⟩ˢ Σ₂'
  square-≈ˢ {β₁ = β₁} Σ₁≈Σ₂ Σ₁≈Σ₁' Σ₂≈Σ₂' =
    let Σ₁'≈Σ₁ = sym-≈ˢ Σ₁≈Σ₁'
        Σ₁'≈Σ₂ = trans-≈ˢ Σ₁'≈Σ₁ Σ₁≈Σ₂ in
        trans-≈ˢ Σ₁'≈Σ₂ Σ₂≈Σ₂'

--------------------------------------------------------------------------------

  -- TODO: remove
  -- Safe bijection-indexed extension: Σ₁ ⊆⟨ β ⟩ Σ₂
  -- _⊆⟨_⟩ˢ′_ : Store → Bij → Store → Set
  -- Σ₁ ⊆⟨ β ⟩ˢ′ Σ₂ = ∀ {n₁ n₂ s₁ s₂ τ₁ τ₂} {c₁ : Cell s₁ τ₁} {c₂ : Cell s₂ τ₂} →
  --                   (n₁ , n₂) ∈ᵗ β → n₁ ↦ c₁ ∈ Σ₁ → n₂ ↦ c₂ ∈ Σ₂

  -- TODO: remove
  -- Store-⊆ : Bij → Store → Store → Set
  -- Store-⊆ β Σ₁ Σ₂ = ∀ {n₁ n₂ τ} {c : Cell τ} → (n₁ , n₂) ∈ᵗ β → n₁ ↦ c ∈ Σ₁ → n₂ ↦ c ∈ Σ₂

  -- record _⊆⟨_⟩ˢ_ (Σ₁ : Store) (β : Bij) (Σ₂ : Store) : Set where
  --   field store-⊆ : Store-⊆ β Σ₁ Σ₂
  --         -- Intuitively this should follow from store-⊆, but it is hard to prove it constructively
  --         store-≤ : ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥

  -- refl-⊆ˢ : ∀ {Σ} → Σ ⊆⟨ ι ∥ Σ ∥ ⟩ˢ Σ
  -- refl-⊆ˢ {Σ} = record { store-⊆ = store-⊆ ; store-≤ = ≤-refl }
  --   where store-⊆ : Store-⊆ (ι ∥ Σ ∥) Σ Σ
  --         store-⊆ ∈-ι ∈₁ rewrite Id.idᴾ-≡ ∣ Σ ∣ˢ ∈-ι = ∈₁

  -- trans-⊆ˢ : ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ⊆⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂ → Σ₂ ⊆⟨ ι ∥ Σ₂ ∥ ⟩ˢ Σ₃ → Σ₁ ⊆⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₃
  -- trans-⊆ˢ {Σ₁} {Σ₂} {Σ₃} ⊆₁ ⊆₂  = record { store-⊆ = store-⊆ ; store-≤ = ≤-trans S₁.store-≤ S₂.store-≤ }
  --   where module S₁ = _⊆⟨_⟩ˢ_ ⊆₁
  --         module S₂ = _⊆⟨_⟩ˢ_ ⊆₂

  --         store-⊆ : Store-⊆ (ι ∥ Σ₁ ∥) Σ₁ Σ₃
  --         store-⊆ {n₁} {n₂} ∈-ι ∈₁ with Id.lemma ∣ Σ₁ ∣ˢ ∈-ι
  --         ... | refl , n< = S₂.store-⊆ (ι-⊆ S₁.store-≤ ∈-ι) (S₁.store-⊆ ∈-ι ∈₁)

  -- TODO: remove
  -- snoc-⊆ˢ : ∀ {Σ₁ Σ₂ τ} {c : Cell τ} → Σ₁ ⊆⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂ → Σ₁ ⊆⟨ ι ∥ Σ₁ ∥ ⟩ˢ (Σ₂ ∷ᴿ c)
  -- snoc-⊆ˢ {Σ₁} {Σ₂} {c = c} ⊆₁ = record { store-⊆ = store-⊆ ; store-≤ = ≤-trans S₁.store-≤ snoc-≤ }
  --   where module S₁ = _⊆⟨_⟩ˢ_ ⊆₁
  --         open Id ∣ Σ₁ ∣ˢ
  --         store-⊆ : Store-⊆ (ι ∥ Σ₁ ∥) Σ₁ (Σ₂ ∷ᴿ c)
  --         store-⊆ ∈-ι ∈₁ = wken-∈ (S₁.store-⊆ ∈-ι ∈₁)

  snoc-≈ˢ : ∀ {Σ₁ Σ₂ τ} {c : Cell τ} → Σ₁ ≈⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂ → Σ₁ ≈⟨ ι ∥ Σ₁ ∥ ⟩ˢ (Σ₂ ∷ᴿ c)
  snoc-≈ˢ {Σ₁} {Σ₂} {c = c} ≈₁ = record { dom-⊆ = refl-⊆ᴰ ; rng-⊆ = rng-⊆ ; lift-≅ = lift-≅ }
    where
      postulate ≤₁ : ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥ -- TODO: extra assumption
      open Id ∣ Σ₁ ∣ˢ
      rng-⊆ : ι ∥ Σ₁ ∥ ⊆ᴿ (Σ₂ ∷ᴿ c)
      rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
      ... | refl , n< = <-∈ (≤-trans n< (≤-trans ≤₁ snoc-≤))

      module S₁ = _≈⟨_⟩ˢ_ ≈₁

      lift-≅ : Lift-≅ Σ₁ (Σ₂ ∷ᴿ c) (ι ∥ Σ₁ ∥)
      lift-≅ x ∈₁ ∈₂ with lemma x
      ... | refl , n< = S₁.lift-≅ x ∈₁ (lookup-snoc ∈₂ (≤-trans n< ≤₁))

  -- write-⊆ˢ : ∀ {Σ Σ' Σ'' n τ ℓ ℓ'} {v v' : Value τ} → ℓ ⋤ A → ℓ' ⋤ A →
  --            n ↦ ⌞ v , ℓ ⌟ ∈ Σ' → Σ'' ≔ Σ' [ n ↦ ⌞ v' , ℓ' ⌟ ] →
  --            Σ ⊆⟨ ι ∥ Σ ∥ ⟩ˢ Σ' → Σ ⊆⟨ ι ∥ Σ ∥ ⟩ˢ Σ''
  -- write-⊆ˢ {Σ} {Σ'} {Σ''} {v = v} ℓ⋤A ℓ'⋤A n∈Σ' x ⊆₁ = record { store-⊆ = store-⊆ ; store-≤ = store-≤ }
  --   where module S₁ = _⊆⟨_⟩ˢ_ ⊆₁
  --         open Id ∣ Σ ∣ˢ

  --         store-≤ : ∥ Σ ∥ ≤ ∥ Σ'' ∥
  --         store-≤ with S₁.store-≤
  --         ... | ≤₁ rewrite write-length-≡ x = ≤₁

  --         store-⊆ : Store-⊆ (ι ∥ Σ ∥) Σ Σ''
  --         store-⊆ {n₁} {n₂} {τ} {c'} ∈-ι ∈₁ with lemma ∈-ι
  --         ... | refl , n< with S₁.store-⊆ ∈-ι ∈₁
  --         ... | ∈₂ = {!∈₂!}

--          aux : n₁ ↦ c Σ' Σ'' ≔ Σ' [ n ↦ c ]
-- with <-∈ {n} {Σ''} {!!}
--           ... | _ , _ , _ , ∈₂ = {!∈₂!}


  -- TODO: remove
  -- Could be worth to add ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥ in the def of ⊆
  -- ⊆-≈ˢ : ∀ {Σ₁ Σ₂} → {{validˢ : Validˢ Σ₁}} → Σ₁ ⊆⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂ → Σ₁ ≈⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂
  -- ⊆-≈ˢ {Σ₁} {Σ₂} {{validˢ}} ⊆₁ =
  --   record { dom-⊆ = dom-⊆
  --          ; rng-⊆ = rng-⊆
  --          ; lift-≅ = lift-≅ }
  --   where

  --     open Id ∣ Σ₁ ∣ˢ
  --     dom-⊆ : ι ∣ Σ₁ ∣ˢ ⊆ᴰ Σ₁
  --     dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
  --     ... | refl , n< = <-∈ n<

  --     open _⊆⟨_⟩ˢ_ ⊆₁

  --     rng-⊆ : ι ∥ Σ₁ ∥ ⊆ᴿ Σ₂
  --     rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
  --     ... | refl , n< = <-∈ (≤-trans n< store-≤)

  --     lift-≅ : Lift-≅ Σ₁ Σ₂ (ι ∥ Σ₁ ∥)
  --     lift-≅ {n₁} {n₂} {τ₁} {τ₂} {c₁} {c₂} x ∈₁ ∈₂ with idᴾ-≡ x
  --     ... | refl with store-⊆ x ∈₁
  --     ... | ∈₂′ with inj-∈′ ∈₂ ∈₂′
  --     ... | refl , refl = ⌞ (wken-≈ᶜ (validˢ ∈₁) refl-≈ᶜ) ⌟

  writeᴴ-≈ˢ : ∀ {Σ Σ' n τ ℓ ℓ'} {v v' : Value τ} {{validˢ : Validˢ Σ}} →
              ℓ ⋤ A → ℓ' ⋤ A → n ↦ ⌞ v , ℓ ⌟ ∈ Σ → Σ' ≔ Σ [ n ↦ ⌞ v' , ℓ' ⌟ ] →
              Σ ≈⟨ ι ∥ Σ ∥ ⟩ˢ Σ'
  writeᴴ-≈ˢ {Σ} {Σ'} {n} {v = v} {{validˢ}} ℓ⋤A ℓ'⋤A n∈Σ w =
    record { dom-⊆ = refl-⊆ᴰ ; rng-⊆ = rng-⊆ ; lift-≅ = lift-≅ }
    where
      open Id ∣ Σ ∣ˢ
      rng-⊆ : ι ∥ Σ ∥ ⊆ᴿ Σ'
      rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
      ... | refl , n< with write-length-≡ w
      ... | eq = <-∈ (≤-trans n< (≤-reflexive (sym eq)))

      lift-≅ : Lift-≅ Σ Σ' (ι ∥ Σ ∥)
      lift-≅ {n₁} {n₂} ∈ᴮ ∈₁ ∈₂ with lemma ∈ᴮ
      ... | refl , _  with n ≟ n₁

       -- The written cell is secret
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | yes refl with inj-∈′ ∈₁ n∈Σ
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | yes refl | refl , refl with inj-∈′ ∈₂ (write-∈ w)
      ... | refl , refl = ⌞ (cellᴴ ℓ⋤A ℓ'⋤A) ⌟

      -- Identical cells are looked up, use reflexivity.
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | no n₁≠n with write-only-one w n₁≠n ∈₁ ∈₂
      lift-≅ {n₁} {.n₁} ∈ᴮ ∈₁ ∈₂ | refl , _ | no n₁≠n | refl , refl = ⌞ (wken-≈ᶜ (validˢ ∈₁) refl-≈ᶜ) ⌟


  -- write-⊆ˢ {Σ} {Σ'} {Σ''} {v = v} ℓ⋤A ℓ'⋤A n∈Σ' x ⊆₁ = record { store-⊆ = store-⊆ ; store-≤ = store-≤ }
  --   where module S₁ = _⊆⟨_⟩ˢ_ ⊆₁
  --         open Id ∣ Σ ∣ˢ

  --         store-≤ : ∥ Σ ∥ ≤ ∥ Σ'' ∥
  --         store-≤ with S₁.store-≤
  --         ... | ≤₁ rewrite write-length-≡ x = ≤₁

  --         store-⊆ : Store-⊆ (ι ∥ Σ ∥) Σ Σ''
  --         store-⊆ {n₁} {n₂} {τ} {c'} ∈-ι ∈₁ with lemma ∈-ι
  --         ... | refl , n< with S₁.store-⊆ ∈-ι ∈₁
  --         ... | ∈₂ = {!∈₂!}


  trans-≈ˢ-ι : ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ≈⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₂ → Σ₂ ≈⟨ ι ∥ Σ₂ ∥ ⟩ˢ Σ₃ → Σ₁ ≈⟨ ι ∥ Σ₁ ∥ ⟩ˢ Σ₃
  trans-≈ˢ-ι {Σ₁} {Σ₂} {Σ₃} ≈₁ ≈₂ =
     record { dom-⊆ = dom-⊆
            ; rng-⊆ = rng-⊆
            ; lift-≅ = lift-≅ }
     where
       open Id ∣ Σ₁ ∣ˢ
       dom-⊆ : ι ∣ Σ₁ ∣ˢ ⊆ᴰ Σ₁
       dom-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
       ... | refl , n< = <-∈ n<

       -- TODO: Extra arguments
       postulate ≤₁ : ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥
       postulate ≤₂ : ∥ Σ₂ ∥ ≤ ∥ Σ₃ ∥

       open Data.Nat.Properties
       rng-⊆ : ι ∥ Σ₁ ∥ ⊆ᴿ Σ₃
       rng-⊆ (n , ∈ᴮ) with lemma ∈ᴮ
       rng-⊆ (n , ∈ᴮ) | refl , n< = <-∈ (≤-trans n< (≤-trans ≤₁ ≤₂))

       module S₁ =  _≈⟨_⟩ˢ_ ≈₁
       module S₂ = _≈⟨_⟩ˢ_ ≈₂

       -- Can be obtained from ≤
       postulate ⊆₁ : Σ₁ ⊆ˢ Σ₂
       postulate ⊆₂ : Σ₂ ⊆ˢ Σ₃
       postulate ⊆₃ : Σ₁ ⊆ˢ Σ₃

       lift-≅ : Lift-≅ Σ₁ Σ₃ (ι ∥ Σ₁ ∥)
       lift-≅ {n₁} {n₃} {τ₁} {τ₃} {c₁} {c₃} x ∈₁ ∈₃ with idᴾ-≡ x
       ... | refl with ⊆₁ ∈₁
       ... | c₂ , ∈₂ with ⊆₂ ∈₂
       ... | c₃' , ∈₃' with S₁.lift-≅ (ι-⊆ ≤-refl x) ∈₁ ∈₂ | S₂.lift-≅ (ι-⊆ ≤₁ x) ∈₂ ∈₃
       ... | c₁≈c₂ | c₂≈c₃ with  trans-≅ᶜ c₁≈c₂ c₂≈c₃
       ... | c₁≈c₃ rewrite (absorb-ι ≤₁) = c₁≈c₃
