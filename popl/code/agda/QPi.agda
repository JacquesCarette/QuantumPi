module QPi where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float) renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.Vec using (Vec; []; _∷_; _++_; map; concat; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax using (U; O; I; _+ᵤ_; _×ᵤ_)
  renaming (_⟷₁_ to _⟷_)
open import PiTagless using (Pi)
open import GenericPi using (GenericPi)
open import Amalgamation using (TList; cons₁; cons₂; nil)
open import StatesAndEffects using (StEffPi; arr; _>>>>_)
  renaming (zero to kzero; assertZero to bzero; _***_ to _****_)
open import Instances using (Fwd)
  renaming (evalTL₁ to evalPi; evalSE to evalArr)
open import Tests using (show) 

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  30 _⇔_
infixr 10 _>>>_
infixr 30 _***_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

𝟚 : U
𝟚 = I +ᵤ I

-- Arrow combinators

data _⇔_ : U → U → Set where
  arrZ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
  arrϕ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
  -- multiplicative structure
  unite⋆   : t ×ᵤ I ⇔ t
  uniti⋆   : t ⇔ t ×ᵤ I
  swap⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  -- composition
  id⇔    : t ⇔ t
  _>>>_  : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _***_  : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
  inv    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
  -- states and effects
  zero        : I ⇔ 𝟚
  assertZero  : 𝟚 ⇔ I

---------------------------------------------------------------------------
-- Semantics

private
  variable
    c c₁ c₂ c₃ c₄ c₅ c₆ : t₁ ⟷ t₂

private
  variable
    d d₁ d₂ d₃ d₄ d₅ d₆ : t₁ ⇔ t₂

piz pih : (t₁ ⟷ t₂) → TList t₁ t₂
piz c = cons₁ c nil
pih c = cons₂ c nil

pizA pihA : (t₁ ⟷ t₂) → StEffPi t₁ t₂
pizA = arr ∘ piz
pihA = arr ∘ pih

embed : (t₁ ⇔ t₂) → StEffPi t₁ t₂
embed (arrZ c) = pizA c
embed (arrϕ c) = pihA c
embed unite⋆ = pizA _⟷_.unite⋆
embed uniti⋆ = pizA _⟷_.uniti⋆
embed swap⋆ = pizA _⟷_.swap⋆
embed assocl⋆ = pizA _⟷_.assocl⋆
embed assocr⋆ = pizA _⟷_.assocr⋆
embed id⇔ = pizA _⟷_.id⟷₁
embed (d₁ >>> d₂) = embed d₁ >>>> embed d₂ 
embed (d₁ *** d₂) = embed d₁ **** embed d₂ 
embed (inv d) = {!!}
embed zero = kzero
embed assertZero = bzero

-- Example

xgate had zgate : 𝟚 ⇔ 𝟚
xgate = arrZ _⟷_.swap₊ 
had = arrϕ _⟷_.swap₊
zgate = had >>> xgate >>> had

plus minus : I ⇔ 𝟚 
plus = zero >>> had
minus = plus >>> zgate 

ex1 = show (evalArr (embed minus) (λ tt → 1.0))


