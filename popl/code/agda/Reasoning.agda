{-# OPTIONS --without-K --safe #-}

module Reasoning where

open import PiSyntax
  renaming (_⟷₁_ to _⟷_; id⟷₁ to id⟷; !⟷₁ to !⟷)
open import PiReasoning
open import QPi
  renaming (assocl⋆ to assoclA⋆; assocr⋆ to assocrA⋆;
            unite⋆ to uniteA⋆; uniti⋆ to unitiA⋆;
            swap⋆ to swapA⋆)

---------------------------------------------------------------------------
-- Some of the equations

private
  variable
    t₁ t₂ t₃ : U
    c₁ c₂ c₃ : t₁ ⟷ t₂
    d d₁ d₂ d₃ : t₁ ⇔ t₂

copyZ copyϕ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyZ = unitiA⋆ >>> (id⇔ *** zero) >>> (arrZ PiSyntax.cx)
copyϕ = arrϕ swap₊ >>> copyZ >>> (arrϕ swap₊ *** arrϕ swap₊)

data _≡_ : {t₁ t₂ : U} → (t₁ ⇔ t₂) → (t₁ ⇔ t₂) → Set where
  classicalZ  : (c₁ ⟷₂ c₂) → (arrZ c₁ ≡ arrZ c₂)
  classicalH  : (c₁ ⟷₂ c₂) → (arrϕ c₁ ≡ arrϕ c₂)
  -- 
  assoc>>>l : (d₁ >>> (d₂ >>> d₃)) ≡ ((d₁ >>> d₂) >>> d₃)
  assoc>>>r : ((d₁ >>> d₂) >>> d₃) ≡ (d₁ >>> (d₂ >>> d₃))
  assocl***l : ((d₁ *** (d₂ *** d₃)) >>> assoclA⋆) ≡ (assoclA⋆ >>> ((d₁ *** d₂) *** d₃))
  assocl***r : (assoclA⋆ >>> ((d₁ *** d₂) *** d₃)) ≡ ((d₁ *** (d₂ *** d₃)) >>> assoclA⋆)
  assocr***l : (assocrA⋆ >>> (d₁ *** (d₂ *** d₃))) ≡ (((d₁ *** d₂) *** d₃) >>> assocrA⋆)
  assocr***r : (((d₁ *** d₂) *** d₃) >>> assocrA⋆) ≡ (assocrA⋆ >>> (d₁ *** (d₂ *** d₃)))
  idl>>>l   : (id⇔ >>> d) ≡ d
  idl>>>r   : d ≡ (id⇔ >>> d)
  idr>>>l   : (d >>> id⇔) ≡ d
  idr>>>r   : d ≡ (d >>> id⇔)
  linv>>>l  : (d >>> inv d) ≡ id⇔
  linv>>>r  : id⇔ ≡ (d >>> inv d)
  rinv>>>l  : (inv d >>> d) ≡ id⇔
  rinv>>>r  : id⇔ ≡ (inv d >>> d)
  unitel⋆≡r : (uniteA⋆ >>> d₂) ≡ ((d₂ *** d₁) >>> uniteA⋆)
  uniter⋆≡r : ((d₂ *** d₁) >>> uniteA⋆) ≡ (uniteA⋆ >>> d₂)
  unitil⋆≡r : (unitiA⋆ >>> (d₂ *** d₁)) ≡ (d₂ >>> unitiA⋆)
  unitir⋆≡r : (d₂ >>> unitiA⋆) ≡ (unitiA⋆ >>> (d₂ *** d₁))
  swapl⋆≡ : (swapA⋆ >>> (d₁ *** d₂)) ≡ ((d₂ *** d₁) >>> swapA⋆)
  swapr⋆≡ : ((d₂ *** d₁) >>> swapA⋆) ≡ (swapA⋆ >>> (d₁ *** d₂))
  id≡     : d ≡ d
  trans≡  : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
  -- complementarity
  C : ((copyZ *** id⇔) >>> (id⇔ *** (inv copyϕ)) >>>
      (id⇔ *** copyϕ) >>> ((inv copyZ) *** id⇔)) ≡ id⇔

-- Equational reasoning

infixr 10 _≡⟨_⟩_
infix  15 _≡∎

_≡⟨_⟩_ : (d₁ : t₁ ⇔ t₂) → (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_ ≡⟨ e₁ ⟩ e₂ = trans≡ e₁ e₂ 

_≡∎ : (d : t₁ ⇔ t₂) → d ≡ d
_≡∎ t = id≡

---------------------------------------------------------------------------
--

{--
hadInv : (had >>> had) ≡ id⇔
hadInv = {!  linv>>>l !} 

minusZ≡plus : (minus >>> zgate) ≡ plus
minusZ≡plus =
  (minus >>> zgate)
    ≡⟨ id≡ ⟩
  ((plus >>> (had >>> xgate >>> had)) >>> (had >>> xgate >>> had))
    ≡⟨ {!!} ⟩
  (plus >>> (had >>> xgate >>> (had >>> had) >>> (xgate >>> had)))
    ≡⟨ {!!} ⟩
  (plus >>> (had >>> (xgate >>> xgate) >>> had))
    ≡⟨ {!!} ⟩
  (plus >>> (had >>> had))
    ≡⟨ {!!} ⟩
  plus ≡∎
--}

---------------------------------------------------------------------------

