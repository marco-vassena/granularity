open import Lattice

module Generic.Store.Base {{𝑳 : Lattice}} (Ty : Set) (Value : Ty → Set) where

open import Data.Nat hiding (_≟_)
open import Data.Product

open import Generic.Calculus using (Flow; S; I)

-- A tagged memory cell can store either:
--
-- 1) An unlabeled value for a flow-insesitive reference (I), whose
--    label is stored in the immutable label of the reference
--
-- 2) An explicitly labeled value for a flow-sensitive reference (S),
--    the label in the cell determines its sensitivity and it may
--    increase during the execution.
--
-- TODO: remove Flow not needed. We always need to store a label
-- to be able to compare the cell content.
-- data Cell (τ : Ty) : Set where
--   -- ⌞_⌟ᴵ : Value τ → Cell τ I
--   -- ⌞_⌟ˢ : Value τ × Label → Cell τ S
--   ⌞_⌟ : Value τ × Label → Cell τ

Cell : Ty → Set
Cell τ = Value τ × Label

-- A store is a linear list of memory cells.
data Store : Set where
  [] : Store
  _∷_ : ∀ {τ} → Cell τ → Store → Store

-- Empty store
∅ : Store
∅ = []

-- TODO: Should not need this
-- Function extensionality (used for low-equivalence of stores)
--postulate store-≡ : Extensionality L.zero L.zero

--------------------------------------------------------------------------------
-- TODO : update description
-- Container operations (read and write) reified as dependent types.
-- Since these operations are partial, it is customary in Agda to
-- exploit dependent types to encode only the well-defined behaviour,
-- i.e., reading and writing to valid addresses.

-- Lookup e n Σ is the proof that the n-th cell of the container M
-- contains labeled value e: M[ n ] = c
data Lookup {τ} (c : Cell τ) : ℕ → Store → Set where
  Here : ∀ {Σ} → Lookup c 0 (c ∷ Σ)
  There : ∀ {Σ n τ'} {c' : Cell τ'} → Lookup c n Σ → Lookup c (suc n) (c' ∷ Σ)

-- Sytactic sugar for Lookup
_↦_∈_ : ∀ {τ} → ℕ → Cell τ → Store → Set
_↦_∈_ n c Σ = Lookup c n Σ

_∈_ :  ℕ → Store → Set
n ∈ Σ = ∃ (λ τ → P.Σ (Cell τ) (λ c → n ↦ c ∈ Σ))
  where import Data.Product as P

open import Relation.Nullary

_∉_ : ℕ → Store → Set
n ∉ Σ = ¬ (n ∈ Σ)


-- Extracts the value from a flow-insensitive cell
-- _↦_∈ᴵ_ : ∀ {τ} → ℕ → Value τ → Store → Set
-- _↦_∈ᴵ_ n v Σ = Lookup ⌞ v ⌟ᴵ n Σ

-- Extracts the value and the label from a flow-sensitive cell
-- _↦_∈ˢ_ : ∀ {τ} → ℕ → (Value τ × Label) → Store → Set
-- _↦_∈ˢ_ n x Σ = Lookup ⌞ x ⌟ˢ n Σ

_⊆_ : Store → Store → Set
Σ ⊆ Σ' = ∀ {τ n} {c : Cell τ} → n ↦ c ∈ Σ → P.Σ (Cell τ) (λ c' → n ↦ c' ∈ Σ')
  where import Data.Product as P

trans-⊆ : ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ⊆ Σ₂ → Σ₂ ⊆ Σ₃ → Σ₁ ⊆ Σ₃
trans-⊆ ⊆₁ ⊆₂ ∈₁ = ⊆₂ (proj₂ (⊆₁ ∈₁))

_⊆′_ : Store → Store → Set
Σ ⊆′ Σ' = ∀ {n} → n ∈ Σ → n ∈ Σ'

⊆-⊆′ : ∀ {Σ Σ'} → Σ ⊆ Σ' → Σ ⊆′ Σ'
⊆-⊆′ ⊆₁ (_ , _ , ∈₁) with ⊆₁ ∈₁
... | _ , ∈₂ = _ , _ , ∈₂

cons-∈ : ∀ {Σ τ n} {c : Cell τ} → n ∈ Σ → n ∈ (c ∷ Σ)
cons-∈ (_ , _ , Here) = _ , _ , Here
cons-∈ {c = c} (τ , c' , There x) with cons-∈ (τ , c' , x)
... | (τ' , c'' , x') = τ' , c'' , There x'

open import Data.Empty

-- foo : ∀ {n} → n ∈ [] → suc n ∈ []
-- foo (_ , _ , ())

open import Relation.Binary.PropositionalEquality

⊥-∉[] : ∀ {n} → n ∈ [] → ⊥
⊥-∉[] (_ , _ , ())

-- []⊆ : ∀ {Σ} → Σ ⊆′ [] → Σ ≡ []
-- []⊆ {[]} ⊆₁ = refl
-- []⊆ {c ∷ Σ₁} ⊆₁ = ⊥-elim (⊥-∉[] (⊆₁ (_ , c , Here)))
--   where aux : ∀ {τ} {c : Cell τ} → 1 ∈ (c ∷ []) → ⊥
--         aux (_ , _ , There ())

-- Write v n C₁ C₂ is the proof that updating container C₁ with v at
-- position n gives container C₂: C₂ ≔ C₁ [ n ↦ v ]
data Write {τ} (c : Cell τ) : ℕ → Store → Store → Set where
  Here : ∀ {Σ} {c' : Cell τ} → Write c 0 (c' ∷ Σ) (c ∷  Σ)
  There : ∀ {Σ Σ' τ' n} {c' : Cell τ'} → Write c n Σ Σ' → Write c (suc n) (c' ∷ Σ) (c' ∷ Σ')

-- TODO: shortcuts for S and I?
-- Syntactic sugar for Write
_≔_[_↦_] : ∀ {τ} → Store → Store → ℕ → Cell τ → Set
_≔_[_↦_] Σ' Σ n c = Write c n Σ Σ'

-- _≔_[_↦_]ᴵ : ∀ {τ} → Store → Store → ℕ → Value τ → Set
-- _≔_[_↦_]ᴵ Σ' Σ n v = Σ' ≔ Σ [ n ↦ ⌞ v ⌟ᴵ ]

-- _≔_[_↦_]ˢ : ∀ {τ} → Store → Store → ℕ → (Value τ × Label) → Set
-- _≔_[_↦_]ˢ Σ' Σ n x = Σ' ≔ Σ [ n ↦ ⌞ x ⌟ˢ ]

-- snoc
_∷ᴿ_ : ∀ {τ} → Store → Cell τ → Store
[] ∷ᴿ c  = c ∷ []
(c₁ ∷ Σ) ∷ᴿ c = c₁ ∷ (Σ ∷ᴿ c)

-- ∥ C ∥ denotes the length of container C.
∥_∥ : Store → ℕ
∥ [] ∥  = 0
∥ _ ∷ Σ ∥ = suc ∥ Σ ∥

infix 1 ∥_∥

<-∈ : ∀ {n} {Σ : Store} → n < ∥ Σ ∥ → n ∈ Σ
<-∈ {Σ = []} ()
<-∈ {zero} {Σ = c ∷ Σ} (s≤s x) = _ , c , Here
<-∈ {suc n} {Σ = c ∷ Σ} (s≤s x) with <-∈ x
... | _ , _  , n∈Σ = _ , _ , There n∈Σ

∈-<  : ∀ {n} {Σ : Store} → n ∈ Σ → n < ∥ Σ ∥
∈-< (_ , _ , Here) = s≤s z≤n
∈-< (_ , _ , There x) = s≤s (∈-< (_ , _ , x))

-- tail-⊆′ : ∀ {Σ₁ Σ₂ τ₁ τ₂} {c₁ : Cell τ₁} {c₂ : Cell τ₂} → (c₁ ∷ Σ₁) ⊆′ (c₂ ∷ Σ₂) → Σ₁ ⊆′ Σ₂
-- tail-⊆′ {c₁ = c₁} {c₂} ⊆₁ x with cons-∈ {c = c₁} x
-- ... | x' with ⊆₁ x'
-- ... | y' with ∈-< y'
-- tail-⊆′ {Σ₂ = Σ₂} {c₁ = c₁} {c₂} ⊆₁ x | x' | proj₃ , proj₄ , y' | s≤s n<Σ₂ with ∈-< x | ∈-< x'
-- ... | a | (s≤s b) =  <-∈ {Σ = Σ₂} {!!}

-- _++ˢ_ : Store → Store → Store
-- [] ++ˢ Σ' = Σ'
-- (c ∷ Σ) ++ˢ Σ' = c ∷ (Σ ++ˢ Σ')

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

suc-snoc : ∀ {τ} {c : Cell τ} Σ → ∥ Σ ∷ᴿ c ∥ ≡ suc ∥ Σ ∥
suc-snoc [] = refl
suc-snoc (x ∷ Σ) = cong suc (suc-snoc Σ)

-- Lemma snoc
snoc-≤ : ∀ {Σ τ} {c : Cell τ} → ∥ Σ ∥ ≤ ∥ Σ ∷ᴿ c ∥
snoc-≤ {Σ} {c = c} rewrite suc-snoc {c = c} Σ = ≤-step ≤-refl

-- TODO: rename snoc-∈
wken-∈ : ∀ {n τ τ' Σ} {c : Cell τ} {c' : Cell τ'} → n ↦ c ∈ Σ → n ↦ c ∈ (Σ ∷ᴿ c')
wken-∈ Here = Here
wken-∈ (There x) = There (wken-∈ x)

wken-∈′ : ∀ {n τ Σ} {c : Cell τ} → n ∈ Σ → n ∈ (Σ ∷ᴿ c)
wken-∈′ (_ , _ , ∈₁) = (_ , _ , wken-∈ ∈₁)

pred-∈ : ∀ {n τ Σ} {c : Cell τ} → suc n ∈ (c ∷ Σ) → n ∈ Σ
pred-∈ (_ , _ , There x) = _ , _ , x

write-length-≡ : ∀ {Σ Σ' n τ} {c : Cell τ} → Σ' ≔ Σ [ n ↦ c ] → ∥ Σ' ∥ ≡ ∥ Σ ∥
write-length-≡ Here = refl
write-length-≡ (There x) = cong suc (write-length-≡ x)

-- Lemmas
-- TODO: Probably not needed this one in the end
≤-⊆ : ∀ {Σ₁ Σ₂} → ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥ → Σ₁ ⊆′ Σ₂
≤-⊆ {[]} {Σ₂} z≤n ()
≤-⊆ {v₁ ∷ Σ₁} {[]} () x
≤-⊆ {v₁ ∷ Σ₁} {v₂ ∷ Σ₂} (s≤s n≤n') (τ , .v₁ , Here) = _ , _ , Here
≤-⊆ {v₁ ∷ Σ₁} {v₂ ∷ Σ₂} (s≤s n≤n') (τ , c , There x) with ≤-⊆ n≤n'(τ , c , x)
... | (τ' , c' , x') =  τ' , c' , (There x')

open import Data.Sum

≰-∉ : ∀ {Σ₁ Σ₂} → ∥ Σ₁ ∥ ≰ ∥ Σ₂ ∥ → ∃ (λ n → n ∈ Σ₁ × n ∉ Σ₂)
≰-∉ {[]} {Σ₂} ≰ = ⊥-elim (≰ z≤n)
≰-∉ {x ∷ Σ₁} {[]} ≰ = 0 , (_ , _ , Here) , ⊥-∉[]
≰-∉ {x ∷ Σ₁} {x₁ ∷ Σ₂} ≰ with ≰-∉ {Σ₁} {Σ₂} (λ ≤₁ → ≰ (s≤s ≤₁) )
... | n , (_ , _ , ∈₁) , ∉₂ = suc n , (_ , _ , There ∈₁) , (λ ∈₂ → ∉₂ (pred-∈ ∈₂) )

⊆-≤ : ∀ {Σ₁ Σ₂} → Σ₁ ⊆′ Σ₂ →  ∥ Σ₁ ∥ ≤ ∥ Σ₂ ∥
⊆-≤ {Σ₁} {Σ₂} ⊆ with ∥ Σ₁ ∥ ≤? ∥ Σ₂ ∥
⊆-≤ {Σ₁} {Σ₂} ⊆ | yes p = p
⊆-≤ {Σ₁} {Σ₂} ⊆ | no ¬p with ≰-∉ ¬p
... | n , ∈₁ , ∉₂ = ⊥-elim (∉₂ (⊆ ∈₁))

pred-≢ : ∀ {n n'} → suc n ≢ suc n' → n ≢ n'
pred-≢ {n} {.n} ¬p refl = ⊥-elim (¬p refl)

open import Relation.Binary.HeterogeneousEquality as H
open import Data.Product as P

-- For heterogeneous values.
inj-∈′ : ∀ {n τ₁ τ₂} {Σ : Store} {c₁ : Cell τ₁} {c₂ : Cell τ₂} →
        n ↦ c₁ ∈ Σ → n ↦ c₂ ∈ Σ → P.Σ (τ₁ ≡ τ₂) (λ {refl → c₁ ≡ c₂})
inj-∈′ Here Here = refl , refl
inj-∈′ (There x) (There y) with inj-∈′ x y
... | refl , refl = refl , refl

-- TODO: haven't we proved this already somewhere?
inj-∈ : ∀ {n τ} {Σ : Store} {c₁ c₂ : Cell τ} →
        n ↦ c₁ ∈ Σ → n ↦ c₂ ∈ Σ → c₁ ≡ c₂
inj-∈ x y with inj-∈′ x y
... | refl , eq = eq

-- inj-∈-snoc : ∀ {n τ₁ τ₂ τ₃} {Σ : Store} {c₁ : Cell τ₁} {c₂ : Cell τ₂} {c₃ : Cell τ₃} →
--              n ↦ c₁ ∈ Σ → n ↦ c₂ ∈ Σ → P.Σ (τ₁ ≡ τ₂) (λ {refl → c₁ ≡ c₂})
-- inj-∈-snoc

lookup-∈ : ∀ {Σ n τ} {c : Cell τ} → n ↦ c ∈ Σ → n ∈ Σ
lookup-∈ Here = _ , _ , Here
lookup-∈ (There x) with lookup-∈ x
... | _ , _ , ∈₁ = _ , _ , There ∈₁

write-only-one : ∀ {Σ Σ' n τ} {c : Cell τ} → Σ' ≔ Σ [ n ↦ c ] →
                   (∀ {n' τ' τ''} {c' : Cell τ'} {c'' : Cell τ''}
                     → n ≢ n' → n' ↦ c' ∈ Σ → n' ↦ c'' ∈ Σ' → P.Σ (τ' ≡ τ'') (λ { refl → c' ≡ c''}))
write-only-one Here n≠n' Here Here = ⊥-elim (n≠n' refl)
write-only-one (There w) n≠n' Here Here = refl , refl
write-only-one Here n≠n' (There ∈₁) (There ∈₂) with inj-∈′ ∈₁ ∈₂
... | refl , refl  = refl , refl
write-only-one (There w) n≠n' (There ∈₁) (There ∈₂) with write-only-one w (pred-≢ n≠n') ∈₁ ∈₂
... | refl , refl = refl , refl

write-only-one′ : ∀ {Σ Σ' n n' τ τ' τ''} {c : Cell τ}  {c' : Cell τ'} {c'' : Cell τ''} →
                    Σ' ≔ Σ [ n ↦ c ] →
                    n ≢ n' →
                    n' ↦ c' ∈ Σ →
                    n' ↦ c'' ∈ Σ'
                    → P.Σ (τ' ≡ τ'') (λ { refl → c' ≡ c''})
write-only-one′ Here n≠n' Here Here = ⊥-elim (n≠n' refl)
write-only-one′ Here n≠n' (There ∈₁) (There ∈₂) with inj-∈′ ∈₁ ∈₂
... | refl , refl =  refl , refl
write-only-one′ (There w) n≠n' Here Here = refl , refl
write-only-one′ (There w) n≠n' (There ∈₁) (There ∈₂) with write-only-one′ w (pred-≢ n≠n') ∈₁ ∈₂
... | refl , refl = refl , refl


-- TODO: better switch name in write-∈ ?

write-∈ : ∀ {Σ Σ' τ n} {c : Cell τ} → Σ' ≔ Σ [ n ↦ c ] → n ↦ c ∈ Σ'
write-∈ Here = Here
write-∈ (There x) = There (write-∈ x)

write-∈′ : ∀ {Σ Σ' τ n} {c : Cell τ} → Σ' ≔ Σ [ n ↦ c ] → n  ∈ Σ
write-∈′ Here = _ , _ , Here
write-∈′ (There x) with write-∈′ x
... | _ , _ , y = _ , _ , There y

write-∈′′ : ∀ {Σ Σ' τ n n'} {c : Cell τ} → Σ' ≔ Σ [ n ↦ c ] → n' ∈ Σ' → n' ∈ Σ
write-∈′′ Here (_ , _ , Here) = _ , _ , Here
write-∈′′ (There w) (_ , _ , Here) = _ , _ , Here
write-∈′′ Here (_ , _ , There x) = _ , _ , There x
write-∈′′ (There w) (_ , _ , There x) with write-∈′′ w (_ , _ , x)
... | _ , _ , y =  _ , _ , There y

n≮0 : ∀ {n} → n ≮ 0
n≮0 {n} ()

lookup-snoc : ∀ {Σ n τ τ'} {c : Cell τ} {c' : Cell τ'} → n ↦ c ∈ (Σ ∷ᴿ c') → n < ∥ Σ ∥ → n ↦ c ∈ Σ
lookup-snoc {[]} ∈₁ <₁ = ⊥-elim (n≮0 <₁)
lookup-snoc {x ∷ Σ₁} Here <₁ = Here
lookup-snoc {x ∷ Σ₁} (There ∈₁) (s≤s <₁) = There (lookup-snoc ∈₁ <₁)

∉-oob : ∀ {Σ} → ∥ Σ ∥ ∈ Σ → ⊥
∉-oob {[]} (_ , _ , ())
∉-oob {_ ∷ Σ₁} (_ , _ , There x) = ∉-oob (_ , _ , x)

last-∈ : ∀ {τ} {c : Cell τ} Σ → ∥ Σ ∥ ↦ c ∈ (Σ ∷ᴿ c)
last-∈ [] = Here
last-∈ (x ∷ Σ₁) = There (last-∈ Σ₁)

last-∈′ : ∀ {τ} {c : Cell τ} Σ → ∥ Σ ∥ ∈ (Σ ∷ᴿ c)
last-∈′ Σ = _ , _ , last-∈ Σ

last-≡ : ∀ {Σ τ τ'} {c : Cell τ} {c' : Cell τ'} → ∥ Σ ∥ ↦ c' ∈ (Σ ∷ᴿ c) → P.Σ (τ ≡ τ') (λ { refl → c ≡ c' })
last-≡ {[]} Here = refl , refl
last-≡ {_ ∷ Σ₁} (There x) with last-≡ x
... | refl , refl = refl , refl
