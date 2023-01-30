{-# OPTIONS --without-K #-}

-- Examples of QPi that are based on discarding information (and are thus
-- not reversible). Right now, postulate the existence of 'discard'.

module QPi.Measurement where

open import Pi.Types using (U; I; _×ᵤ_; 𝟚)
open import Pi.Language as Π using (_⟷_)
import Pi.Terms as ΠT

open import QPi.Syntax
open import QPi.Terms using (copyZ; copyϕ; map3***; plus; amp; repeat; u)
open import QPi.Equivalences using (_≡_)
---------------------------------------------------------------------------

private
  variable
    t t₁ t₂ : U

---------------------------------------------------------------------------

-- postulate measurement
postulate
  discard : t ⇔ I
  discardL : (d : t₁ ⇔ t₂) → d >>> discard ≡ discard

fst : (t₁ ×ᵤ t₂) ⇔ t₁
fst = (id⇔ *** discard) >>> unite⋆r

snd : (t₁ ×ᵤ t₂) ⇔ t₂
snd = swap⋆ >>> fst

measureZ measureϕ : 𝟚 ⇔ 𝟚
measureZ = copyZ >>> fst
measureϕ = copyϕ >>> fst

grover₃ : I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
grover₃ = map3*** plus >>>
          repeat 3 (u >>> amp) >>>
          map3*** measureZ

---------------------------------------------------------------------------
---------------------------------------------------------------------------
