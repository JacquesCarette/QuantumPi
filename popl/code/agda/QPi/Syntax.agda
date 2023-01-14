{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Syntax where

open import Pi.Types using (U; I; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; !⟷)
--open import CommMonoid using (CMStructure; CMon; module Build)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  10 _⇔_
infixr 30 _>>>_
infixr 40 _***_

private
  variable
    t t₁ t₂ t₃ t₄ : U

{--
-- Set things up
  CM : CMStructure
  CM = CMon U I _×ᵤ_

  module M = Build CM
--}
  
data _⇔_ : U → U → Set where
  arrZ        : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
  arrϕ        : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
  unite⋆l   : I ×ᵤ t ⇔ t
  uniti⋆l   : t ⇔ I ×ᵤ t
  swap⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  id⇔         : t ⇔ t
  _>>>_       : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _***_       : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
  zero        : I ⇔ 𝟚
  assertZero  : 𝟚 ⇔ I

{--
pattern unite⋆l = mult M.unite⋆
pattern uniti⋆l = mult M.uniti⋆
pattern swap⋆   = mult M.swap⋆
pattern assocl⋆ = mult M.assocl⋆
pattern assocr⋆ = mult M.assocr⋆
--}

-- These are right-biased
unite⋆r : {t : U} → t ×ᵤ I ⇔  t
unite⋆r = swap⋆ >>> unite⋆l

uniti⋆r : {t : U} → t ⇔ t ×ᵤ I
uniti⋆r =  uniti⋆l >>> swap⋆ 

inv : t₁ ⇔ t₂ → t₂ ⇔ t₁
inv (arrZ c) = arrZ (!⟷ c)
inv (arrϕ c) = arrϕ (!⟷ c)
inv (unite⋆l) = uniti⋆l
inv (uniti⋆l) = unite⋆l
inv (swap⋆) = swap⋆
inv (assocl⋆) = assocr⋆
inv (assocr⋆) = assocl⋆
inv id⇔ = id⇔
inv (d₁ >>> d₂) = inv d₂ >>> inv d₁
inv (d₁ *** d₂) = inv d₁ *** inv d₂
inv zero = assertZero
inv assertZero = zero

---------------------------------------------------------------------------
