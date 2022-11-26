module QPi where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float) renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.List using (List; _∷_; []; map)
open import Data.Vec using (Vec; []; _∷_; _++_; map; concat; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax using (U; O; I; _+ᵤ_; _×ᵤ_; 𝟚)
  renaming (_⟷₁_ to _⟷_)
open import Amalgamation using (cons₁; cons₂; nil)
open import StatesAndEffects using (StEffPi; arr; _>>>>_; invSE)
  renaming (zero to kzero; assertZero to bzero; _***_ to _****_)
open import Instances using (evalSE)
open import Tests using (show) 

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  30 _⇔_
infixr 10 _>>>_
infixr 30 _***_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

pattern 𝕋 = inj₁ tt
pattern 𝔽 = inj₂ tt

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

pizA pihA : (t₁ ⟷ t₂) → StEffPi t₁ t₂
pizA c = arr (cons₁ c nil)
pihA c = arr (cons₂ c nil)

embed : (t₁ ⇔ t₂) → StEffPi t₁ t₂
embed (arrZ c) = pizA c
embed (arrϕ c) = pihA c
embed unite⋆ = pizA PiSyntax.unite⋆
embed uniti⋆ = pizA PiSyntax.uniti⋆
embed swap⋆ = pizA PiSyntax.swap⋆
embed assocl⋆ = pizA PiSyntax.assocl⋆
embed assocr⋆ = pizA PiSyntax.assocr⋆
embed id⇔ = pizA PiSyntax.id⟷₁
embed (d₁ >>> d₂) = embed d₁ >>>> embed d₂ 
embed (d₁ *** d₂) = embed d₁ **** embed d₂ 
embed (inv d) = invSE (embed d)
embed zero = kzero
embed assertZero = bzero

---------------------------------------------------------------------------
-- Examples

xgate had zgate : 𝟚 ⇔ 𝟚
xgate = arrZ PiSyntax.swap₊ 
had = arrϕ PiSyntax.swap₊
zgate = had >>> xgate >>> had

cx cz : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cx = arrZ PiSyntax.cx
cz = id⇔ *** had >>> cx >>> id⇔ *** had

plus minus : I ⇔ 𝟚 
plus = zero >>> had
minus = plus >>> zgate

assertPlus assertMinus : 𝟚 ⇔ I
assertPlus = had >>> assertZero
assertMinus = zgate >>> assertPlus

--

ex1 = show (evalSE (embed minus) (λ tt → 1.0))

amp : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 
amp = had *** had *** had >>>
      xgate *** xgate *** xgate >>>
      id⇔ *** id⇔ *** had >>>
      arrZ PiSyntax.ccx >>>
      id⇔ *** id⇔ *** had >>>
      xgate *** xgate *** xgate >>>
      had *** had *** had

u : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
u = id⇔ *** id⇔ *** id⇔

repeat : ℕ → (t ⇔ t) → (t ⇔ t)
repeat 0 c = id⇔
repeat 1 c = c
repeat (suc n) c = c >>> repeat n c

grover₃ : I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 
grover₃ = 
  plus *** plus *** plus >>>
  repeat 3 (u >>> amp) 
  

---------------------------------------------------------------------------
---------------------------------------------------------------------------
