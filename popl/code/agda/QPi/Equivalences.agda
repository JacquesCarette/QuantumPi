{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Equivalences where

open import Pi.Types using (U)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷)
import Pi.Terms as ΠT
open import Pi.Equivalences
open import QPi.Syntax
open import QPi.Terms using (ctrlZ; one; copyZ; copyϕ; X; Z;
  H; minus; plus; cx; cz)

---------------------------------------------------------------------------
-- Some of the equations

infix 10 _≡_

private
  variable
    t t₁ t₂ t₃ : U
    c c₁ c₂ c₃ : t₁ ⟷ t₂
    d d₁ d₂ d₃ d₄ : t₁ ⇔ t₂


data _≡_ : {t₁ t₂ : U} → (t₁ ⇔ t₂) → (t₁ ⇔ t₂) → Set where
  classicalZ  : (c₁ ⟷₂ c₂) → (arrZ c₁ ≡ arrZ c₂)
  classicalϕ  : (c₁ ⟷₂ c₂) → (arrϕ c₁ ≡ arrϕ c₂)
  -- arrow axioms
  arrZidL   : arrZ (id⟷ {t}) ≡ id⇔ 
  arrZidR   : id⇔  ≡ arrZ (id⟷ {t})
  arrϕidL   : arrϕ (id⟷ {t}) ≡ id⇔ 
  arrϕidR   : id⇔  ≡ arrϕ (id⟷ {t})
  arrZL    : (arrZ (c₁ ◎ c₂)) ≡ (arrZ c₁ >>> arrZ c₂)
  arrZR    : (arrZ c₁ >>> arrZ c₂) ≡ (arrZ (c₁ ◎ c₂))
  arrϕL    : (arrϕ (c₁ ◎ c₂)) ≡ (arrϕ c₁ >>> arrϕ c₂)
  arrϕR    : (arrϕ c₁ >>> arrϕ c₂) ≡ (arrϕ (c₁ ◎ c₂))
  -- 
  assoc>>>l : (d₁ >>> (d₂ >>> d₃)) ≡ ((d₁ >>> d₂) >>> d₃)
  assoc>>>r : ((d₁ >>> d₂) >>> d₃) ≡ (d₁ >>> (d₂ >>> d₃))
  assocl***l : ((d₁ *** (d₂ *** d₃)) >>> assocl⋆) ≡ (assocl⋆ >>> ((d₁ *** d₂) *** d₃))
  assocl***r : (assocl⋆ >>> ((d₁ *** d₂) *** d₃)) ≡ ((d₁ *** (d₂ *** d₃)) >>> assocl⋆)
  assocr***l : (assocr⋆ >>> (d₁ *** (d₂ *** d₃))) ≡ (((d₁ *** d₂) *** d₃) >>> assocr⋆)
  assocr***r : (((d₁ *** d₂) *** d₃) >>> assocr⋆) ≡ (assocr⋆ >>> (d₁ *** (d₂ *** d₃)))
  idl>>>l   : (id⇔ >>> d) ≡ d
  idl>>>r   : d ≡ (id⇔ >>> d)
  idr>>>l   : (d >>> id⇔) ≡ d
  idr>>>r   : d ≡ (d >>> id⇔)
  linv>>>l  : (d >>> inv d) ≡ id⇔
  linv>>>r  : id⇔ ≡ (d >>> inv d)
  rinv>>>l  : (inv d >>> d) ≡ id⇔
  rinv>>>r  : id⇔ ≡ (inv d >>> d)
  unitel⋆≡r : (unite⋆r >>> d₂) ≡ ((d₂ *** d₁) >>> unite⋆r)
  uniter⋆≡r : ((d₂ *** d₁) >>> unite⋆r) ≡ (unite⋆r >>> d₂)
  unitil⋆≡r : (uniti⋆r >>> (d₂ *** d₁)) ≡ (d₂ >>> uniti⋆r)
  unitir⋆≡r : (d₂ >>> uniti⋆r) ≡ (uniti⋆r >>> (d₂ *** d₁))
  swapl⋆≡ : (swap⋆ >>> (d₁ *** d₂)) ≡ ((d₂ *** d₁) >>> swap⋆)
  swapr⋆≡ : ((d₂ *** d₁) >>> swap⋆) ≡ (swap⋆ >>> (d₁ *** d₂))
  id≡     : d ≡ d
  trans≡  : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
  -- congruence; functor
  cong≡  : (d₁ ≡ d₃) → (d₂ ≡ d₄) → ((d₁ >>> d₂) ≡ (d₃ >>> d₄))
  cong***  : (d₁ ≡ d₃) → (d₂ ≡ d₄) → ((d₁ *** d₂) ≡ (d₃ *** d₄))
  homL*** : ((d₁ *** d₂) >>> (d₃ *** d₄)) ≡ ((d₁ >>> d₃) *** (d₂ >>> d₄))
  homR*** : ((d₁ >>> d₃) *** (d₂ >>> d₄)) ≡ ((d₁ *** d₂) >>> (d₃ *** d₄))
  -- execution equations
  e1L : zero >>> assertZero ≡ id⇔
  e2L : (zero *** id⇔) >>> ctrlZ c ≡ zero *** id⇔
  e3L : (one *** id⇔) >>> ctrlZ c ≡ one *** arrZ c
  -- complementarity
  C : ((copyZ *** id⇔) >>> (id⇔ *** (inv copyϕ)) >>>
        (id⇔ *** copyϕ) >>> ((inv copyZ) *** id⇔))
      ≡ id⇔

---------------------------------------------------------------------------

