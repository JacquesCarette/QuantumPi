{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Reasoning where

open import Pi.Types using (U)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷)
import Pi.Terms as ΠT
open import PiReasoning
open import QPi.Syntax
open import QPi using (ctrlZ; one; copyZ; copyϕ; xgate; zgate;
  had; minus; plus; cx; cz; measureϕ; measureZ)

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
  unitel⋆≡r : (unite⋆ >>> d₂) ≡ ((d₂ *** d₁) >>> unite⋆)
  uniter⋆≡r : ((d₂ *** d₁) >>> unite⋆) ≡ (unite⋆ >>> d₂)
  unitil⋆≡r : (uniti⋆ >>> (d₂ *** d₁)) ≡ (d₂ >>> uniti⋆)
  unitir⋆≡r : (d₂ >>> uniti⋆) ≡ (uniti⋆ >>> (d₂ *** d₁))
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

-- Equational reasoning

infixr 10 _≡⟨_⟩_
infix  15 _≡∎

_≡⟨_⟩_ : (d₁ : t₁ ⇔ t₂) → (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_ ≡⟨ e₁ ⟩ e₂ = trans≡ e₁ e₂ 

_≡∎ : (d : t₁ ⇔ t₂) → d ≡ d
_≡∎ t = id≡

---------------------------------------------------------------------------
-- Example proofs

xInv : (xgate >>> xgate) ≡ id⇔
xInv = trans≡ arrZR (trans≡ (classicalZ linv◎l) arrZidL)  

hadInv : (had >>> had) ≡ id⇔
hadInv = trans≡ arrϕR (trans≡ (classicalϕ linv◎l) arrϕidL)  

minusZ≡plus : (minus >>> zgate) ≡ plus
minusZ≡plus =
  (minus >>> zgate)
    ≡⟨ id≡ ⟩
  ((plus >>> had >>> xgate >>> had) >>> had >>> xgate >>> had)
    ≡⟨ trans≡ (trans≡ (cong≡ (trans≡ assoc>>>l assoc>>>l) id≡) assoc>>>r) (cong≡ id≡ assoc>>>l) ⟩ 
  (((plus >>> had) >>> xgate) >>> (had >>> had) >>> xgate >>> had)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ hadInv id≡) idl>>>l) ⟩
  (((plus >>> had) >>> xgate) >>> xgate >>> had)
    ≡⟨ trans≡ assoc>>>r (cong≡ id≡ assoc>>>l) ⟩
  ((plus >>> had) >>> (xgate >>> xgate) >>> had)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ xInv id≡) idl>>>l) ⟩
  ((plus >>> had) >>> had)
    ≡⟨ trans≡ (trans≡ assoc>>>r (cong≡ id≡ hadInv)) idr>>>l ⟩ 
  plus ≡∎

oneMinusPlus : ((one *** minus) >>> cz) ≡ (one *** plus)
oneMinusPlus =
  (one *** minus) >>> (id⇔ *** had) >>> cx >>> (id⇔ *** had)
    ≡⟨ trans≡ assoc>>>l (cong≡ homL*** id≡) ⟩ 
  ((one >>> id⇔) *** (minus >>> had)) >>> cx >>> (id⇔ *** had)
    ≡⟨ cong≡ (cong*** idr>>>l id≡) id≡ ⟩ 
  (one *** (minus >>> had))>>> cx >>> (id⇔ *** had)
    ≡⟨ cong≡ (cong*** idl>>>r idr>>>r) id≡ ⟩ 
  ((id⇔ >>> one) *** ((minus >>> had) >>> id⇔)) >>> cx >>> (id⇔ *** had)
    ≡⟨ trans≡ (cong≡ homR*** id≡) assoc>>>r ⟩ 
  (id⇔ *** (minus >>> had)) >>> (one *** id⇔) >>> cx >>> (id⇔ *** had)
    ≡⟨ cong≡ id≡ (trans≡ assoc>>>l (cong≡ e3L id≡)) ⟩ 
  (id⇔ *** (minus >>> had)) >>> (one *** xgate) >>> (id⇔ *** had)
    ≡⟨ cong≡ id≡ (trans≡ homL*** (cong*** idr>>>l id≡)) ⟩ 
  (id⇔ *** (minus >>> had)) >>> (one *** (xgate >>> had))
    ≡⟨ trans≡ homL*** (cong*** idl>>>l assoc>>>r ) ⟩ 
  one *** (minus >>> had >>> xgate >>> had)
    ≡⟨ cong*** id≡ minusZ≡plus  ⟩ 
  (one *** plus) ≡∎


xcxA : id⇔ *** xgate >>> cx ≡ cx >>> id⇔ *** xgate
xcxA =
  id⇔ *** xgate >>> cx
    ≡⟨ {!!} ⟩ 
  arrZ ((id⟷ Π.⊗ Π.swap₊) Π.◎ ΠT.cx)
    ≡⟨ classicalZ xcx ⟩
  arrZ (ΠT.cx Π.◎ (id⟷ Π.⊗ Π.swap₊))
    ≡⟨ {!!} ⟩
  cx >>> id⇔ *** xgate ≡∎


zhcx : ((id⇔ *** zgate) >>> (id⇔ *** had) >>> cx) ≡
       (cz >>> (id⇔ *** had) >>> (id⇔ *** xgate))
zhcx =
  ((id⇔ *** zgate) >>> (id⇔ *** had) >>> cx)
    ≡⟨ trans≡ assoc>>>l (cong≡ (trans≡ homL*** (cong*** idl>>>l id≡)) id≡) ⟩
  (id⇔ *** ((had >>> xgate >>> had) >>> had)) >>> cx
    ≡⟨ {!!} ⟩
  id⇔ *** (had >>> xgate) >>> cx
    ≡⟨ {!!} ⟩
  (cz >>> (id⇔ *** had) >>> (id⇔ *** xgate)) ≡∎


measure : measureϕ ≡ (had >>> measureZ >>> had)
measure =
  measureϕ
    ≡⟨ {!!} ⟩
  (had >>> measureZ >>> had) ≡∎

---------------------------------------------------------------------------

