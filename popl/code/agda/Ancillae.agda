{-# OPTIONS --without-K --exact-split --safe #-}

-- Define a sub-language of PiSyntax that is provably inhabited
-- This is used later to define ancillae (thus the name).

module Ancillae where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)

open import Pi.Types using (U; I; _+ᵤ_; _×ᵤ_; ⟦_⟧; enum)
open import PiSyntax using (_⟷_; id⟷; uniti⋆l; uniti⋆r; assocr⋆; !⟷; 𝟚)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ : U

-------------------------------------------------------------------------------------
-- Ancillae

-- This is the type of non-trivial Ancillas
data Anc : Set where
  Two : Anc
  _×ₙ_ : Anc → Anc → Anc

N : Set
N = Maybe Anc

-- Inject N into U
N⇒U : N → U
N⇒U nothing = I
N⇒U (just Two) = I +ᵤ I
N⇒U (just (x ×ₙ y)) = N⇒U (just x) ×ᵤ N⇒U (just y)

enumN : (n : N) → List ⟦ N⇒U n ⟧
enumN n = enum (N⇒U n)

-- Combining ancillas, i.e. product of ancillas
a* : N → N → N
a* (just x) (just y) = just (x ×ₙ y)
a* (just x) nothing = just x
a* nothing (just x) = just x
a* nothing nothing = nothing

-- "unpack" a product of ancillas (including none) into a proper product
unpack : (n₁ n₂ : N) → N⇒U (a* n₁ n₂) ⟷ N⇒U n₁ ×ᵤ N⇒U n₂
unpack (just x) (just y) = id⟷
unpack (just x) nothing = uniti⋆r
unpack nothing (just x) = uniti⋆l
unpack nothing nothing = uniti⋆l

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
