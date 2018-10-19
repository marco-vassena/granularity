module CG.Types where

-- Types τ
data Ty : Set where
  unit : Ty                      -- Unit type
  _×_ : (τ₁ τ₂ : Ty) → Ty        -- Pair
  _+_ : (τ₁ τ₂ : Ty) → Ty        -- Sum
  _➔_ : (τ₁ τ₂ : Ty) → Ty        -- Function
  𝓛 : Ty                        -- Label
  LIO : Ty → Ty                  -- LIO computation
  Labeled : Ty → Ty              -- Labeled value
  Ref :  Ty → Ty                 -- Labeled mutable reference

infixr 3 _➔_
infixr 3 _×_
infixr 3 _+_

Bool : Ty
Bool = unit + unit

-- Context (list of types)
open import Generic.Context Ty public
