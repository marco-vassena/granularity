{-# OPTIONS --allow-unsolved-metas #-}

-- TODO: split generic bij from homogeneous in two modules
-- Generic bij requires decidability (to create singleton bijs)


module Generic.Bijection where

open import Generic.PMap hiding (∅)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Product as P
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Category.Monad
open import Level
open RawMonadPlus {zero} {M = Maybe} monadPlus hiding (∅)

-- If and only if
_⇔_ : ∀ (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

infixl 1 _⇔_

-- Bijection property
IsB : ∀ {A B} (f : A ⇀ B) (g : B ⇀ A) → Set
IsB f g = ∀ {a b} → f a ≡ just b ⇔ g b ≡ just a


-- A bijection is a pair of partial maps between two sets, where these
-- maps are each other inverse.
record Bij (A B : Set) : Set where
  field  to : A ⇀ B
         back : B ⇀ A
         isB : IsB to back

sym-IsB : ∀ {A B : Set} {f : A ⇀ B} {g : B ⇀ A} →
            IsB f g → IsB g f
sym-IsB x = swap x

symᴮ : ∀ {A B} → Bij A B → Bij B A
symᴮ β = record { to = B.back ; back = B.to ; isB = sym-IsB B.isB }
  where module B = Bij β

-- Homogeneous Bijection
Bijᴴ : (A : Set) → Set
Bijᴴ A = Bij A A

-- A pair of values from A and B are in the bijection iff they are
-- mutually related under their respective mapping.
_↔_∈_ : ∀ {A B} → A → B → Bij A B → Set
a ↔ b ∈ β =  (a ↦ b ∈ᴾ to) × (b ↦ a ∈ᴾ back)
  where open Bij β

_∈_ : ∀ {A B} → A × B → Bij A B → Set
(a , b) ∈ β = a ↔ b ∈ β

-- Empty bijection
∅ : ∀ {A B} → Bij A B
∅ = record { to = λ _ → nothing ;
             back = λ _ → nothing ;
             isB = (λ ()) , λ () }

-- Singleton bijection
⟨_↔_⟩ : ∀ {A B} → A → B → Bij A B
⟨ a ↔ b ⟩ = record { to = {!_[_↦_]ᴾ!} ; back = {!!} ; isB = {!!} }

-- Reverse bijection
flip : ∀ {A B} → Bij A B → Bij B A
flip β = record { to = back ; back = to ; isB = swap isB}
  where open Bij β

flip↔ : ∀ {A B β} {a : A} {b : B} → a ↔ b ∈ β → b ↔ a ∈ (flip β)
flip↔ ( eq₁ , eq₂ ) = eq₂ , eq₁

-- β₁ ▻ β₂ denotes that β₂ is disjoint from β₁, i.e., β₂ doesn't
-- relate elements already related in β₁.
_▻_ : ∀ {A} → (β₁ β₂ : Bijᴴ A) → Set
_▻_ {A} β₁ β₂ = B₁.to ▻ᴾ B₂.to × B₁.back ▻ᴾ B₂.back
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- Partial maps remain related under composition
IsB-∣ : ∀ {A : Set} (f₁ g₁ f₂ g₂ : A ⇀ A) → Set
IsB-∣ f₁ g₁ f₂ g₂ = ∀ {a b} → (f₁ a ∣ f₂ a) ≡ just b → (g₁ b ∣ g₂ b) ≡ just a

isB-∣ : ∀ {A : Set} {f₁ g₁ f₂ g₂ : A ⇀ A} →
          IsB f₁ g₁ → IsB f₂ g₂ →
          f₁ ▻ᴾ f₂ → g₁ ▻ᴾ g₂ →
          IsB-∣ f₁ g₁ f₂ g₂
isB-∣ {_} {f₁} {g₁} {f₂} {g₂} isB₁ isB₂ ▻₁ ▻₂ {a} {b} eq
  with f₁ a | f₂ a | g₁ b | g₂ b | isB₁ {a} {b} | isB₂ {a} {b} | ▻₁ a | ▻₂ b
... | just x | ma₂ | mb₁ | mb₂ | peq₁ | peq₂ | p₁ | p₂
  rewrite proj₁ peq₁ eq = refl
... | nothing | ma₂ | mb₁ | mb₂ | peq₁ | peq₂ | p₁ | p₂
  rewrite proj₁ peq₂ eq | is-just-nothing mb₁ p₂ = refl

-- Property that denotes that the composition of two bijections is a
-- bijection.
IsB-∘ : ∀ {A} (β₁ β₂ : Bijᴴ A) → Set
IsB-∘ β₁ β₂ = IsB (λ x → B₁.to x ∣ B₂.to x) (λ x → B₁.back x ∣ B₂.back x)
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- If two bijections are disjoint, then their composition is a
-- bijection.
isB-∘ : ∀ {A} (β₁ β₂ : Bijᴴ A) → β₁ ▻ β₂ → IsB-∘ β₁ β₂
isB-∘ {A} β₁ β₂ (to-▻ , back-▻)
  = isB-∣ {A} {B₁.to} {B₁.back} {B₂.to} {B₂.back} B₁.isB B₂.isB to-▻ back-▻ ,
    isB-∣ {_} {B₁.back} {B₁.to} {B₂.back} {B₂.to} B₁′.isB B₂′.isB back-▻ to-▻
  where module B₁ = Bij β₁
        module B₂ = Bij β₂
        module B₁′ = Bij (symᴮ β₁)
        module B₂′ = Bij (symᴮ β₂)

_∘′_ : ∀ {A B} → (β₁ β₂ : Bij A B) → Bij A  B
β₁ ∘′ β₂ = record { to = λ x → B₁.to x ∣ B₂.to x ;
                    back = λ x → B₁.back x ∣ B₂.back x ;
                    isB = {!!} }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂


-- TODO we can compose non-homogeneous bijection right?
-- Are bijections defined over two or one type?
-- Composition of homogeneous bijections
_∘_ : ∀ {A} → (β₁ β₂ : Bijᴴ A) {{β₁▻β₂ : β₁ ▻ β₂}} → Bijᴴ A
_∘_ {A} β₁ β₂ {{ to-▻ , back-▻ }} =
  record { to   = λ x → B₁.to x ∣ B₂.to x ;
           back = λ x → B₁.back x ∣ B₂.back x ;
           isB = isB-∘ β₁ β₂ (to-▻ , back-▻) }
  where module B₁ = Bij β₁
        module B₂ = Bij β₂

-- Adding one entry to the bijection is a special case of composition.
-- TODO: better symbol?
_#_ : ∀ {A} → Bijᴴ A → A × A → Bijᴴ A
β # x = {!β ∘ ?!}


-- TODO: remove
-- module Ops {A B : Set}
--   {{ _≟ᴬ_ : Decidable (_≡_ {A = A}) }}
--   {{ _≟ᴮ_ : Decidable (_≡_ {A = B}) }} where

--   module AB = PMapUtil A B {{_≟ᴬ_}}
--   module BA = PMapUtil B A {{_≟ᴮ_}}

--   -- TODO: it doesn't seem this op for now. We will need it to add
--   -- single entries.

--   -- Actually, we can define this in terms of Bijection composition (see above)

--   -- Add a new mapping to the bijection.
--   -- TODO: should we assume/require that they are not in the mapping already?
--   -- I won't add it until it comes out in the proof
--   _⋃_ : A × B → Bij A B → Bij A B
--   (a , b) ⋃ β = record { to = to AB.[ a ↦ b ]ᴾ ;
--                          back = back BA.[ b ↦ a ]ᴾ ;
--                          isB = {!!} }
--     where open Bij β

module AddressBij where

  open import Data.Nat

  -- A bijection between addresses (natural numbers)
  Bijᴬ : Set
  Bijᴬ = Bijᴴ ℕ

  instance
    _≟ᴺ_ : (n₁ n₂ : ℕ) → Dec (n₁ ≡ n₂)
    _≟ᴺ_ = _≟_

  -- TODO remove
  -- open Ops {ℕ} {ℕ} {{_≟ᴺ_}} public

  -- Identity bijection
  ι : Bijᴬ
  ι = record { to = just ; back = just ; isB = sym , sym}