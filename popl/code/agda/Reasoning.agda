{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Reasoning where

open import Pi.Types using (U)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷)
import Pi.Terms as ΠT
open import Pi.Equivalences
open import Pi.DefinedEquiv using (xcx)
open import QPi.Syntax
open import QPi.Terms using (ctrlZ; one; copyZ; copyϕ; X; Z;
  H; minus; plus; cx; cz)
open import QPi.Measurement using (measureϕ; measureZ)

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

infixr 10 _；_
_；_ : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_；_ = trans≡

-- Equational reasoning

infixr 10 _≡⟨_⟩_
infix  15 _≡∎

_≡⟨_⟩_ : (d₁ : t₁ ⇔ t₂) → (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_ ≡⟨ e₁ ⟩ e₂ = trans≡ e₁ e₂ 

_≡∎ : (d : t₁ ⇔ t₂) → d ≡ d
_≡∎ t = id≡

---------------------------------------------------------------------------
-- Example proofs

xInv : (X >>> X) ≡ id⇔
xInv =
  X >>> X                  ≡⟨ arrZR ⟩
  arrZ (Π.swap₊ ◎ Π.swap₊) ≡⟨ classicalZ linv◎l ⟩
  arrZ id⟷                 ≡⟨ arrZidL ⟩
  id⇔                      ≡∎

hadInv : (H >>> H) ≡ id⇔
hadInv = trans≡ arrϕR (trans≡ (classicalϕ linv◎l) arrϕidL)  

minusZ≡plus : (minus >>> Z) ≡ plus
minusZ≡plus =
  (minus >>> Z)
    ≡⟨ id≡ ⟩
  ((plus >>> H >>> X >>> H) >>> H >>> X >>> H)
    ≡⟨ ((cong≡ (assoc>>>l ； assoc>>>l) id≡) ； assoc>>>r) ； (cong≡ id≡ assoc>>>l) ⟩ 
  (((plus >>> H) >>> X) >>> (H >>> H) >>> X >>> H)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ hadInv id≡) idl>>>l) ⟩
  (((plus >>> H) >>> X) >>> X >>> H)
    ≡⟨ trans≡ assoc>>>r (cong≡ id≡ assoc>>>l) ⟩
  ((plus >>> H) >>> (X >>> X) >>> H)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ xInv id≡) idl>>>l) ⟩
  ((plus >>> H) >>> H)
    ≡⟨ trans≡ (trans≡ assoc>>>r (cong≡ id≡ hadInv)) idr>>>l ⟩ 
  plus ≡∎

oneMinusPlus : ((one *** minus) >>> cz) ≡ (one *** plus)
oneMinusPlus =
  (one *** minus) >>> (id⇔ *** H) >>> cx >>> (id⇔ *** H)
    ≡⟨ trans≡ assoc>>>l (cong≡ homL*** id≡) ⟩ 
  ((one >>> id⇔) *** (minus >>> H)) >>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ (cong*** idr>>>l id≡) id≡ ⟩ 
  (one *** (minus >>> H))>>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ (cong*** idl>>>r idr>>>r) id≡ ⟩ 
  ((id⇔ >>> one) *** ((minus >>> H) >>> id⇔)) >>> cx >>> (id⇔ *** H)
    ≡⟨ trans≡ (cong≡ homR*** id≡) assoc>>>r ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** id⇔) >>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ id≡ (trans≡ assoc>>>l (cong≡ e3L id≡)) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** X) >>> (id⇔ *** H)
    ≡⟨ cong≡ id≡ (trans≡ homL*** (cong*** idr>>>l id≡)) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** (X >>> H))
    ≡⟨ trans≡ homL*** (cong*** idl>>>l assoc>>>r ) ⟩ 
  one *** (minus >>> H >>> X >>> H)
    ≡⟨ cong*** id≡ minusZ≡plus  ⟩ 
  (one *** plus) ≡∎


xcxA : id⇔ *** X >>> cx ≡ cx >>> id⇔ *** X
xcxA =
  id⇔ *** X >>> cx
    ≡⟨ {!!} ⟩ 
  arrZ ((id⟷ Π.⊗ Π.swap₊) Π.◎ ΠT.cx)
    ≡⟨ classicalZ xcx ⟩
  arrZ (ΠT.cx Π.◎ (id⟷ Π.⊗ Π.swap₊))
    ≡⟨ {!!} ⟩
  cx >>> id⇔ *** X ≡∎


zhcx : ((id⇔ *** Z) >>> (id⇔ *** H) >>> cx) ≡
       (cz >>> (id⇔ *** H) >>> (id⇔ *** X))
zhcx =
  ((id⇔ *** Z) >>> (id⇔ *** H) >>> cx)
    ≡⟨ trans≡ assoc>>>l (cong≡ (trans≡ homL*** (cong*** idl>>>l id≡)) id≡) ⟩
  (id⇔ *** ((H >>> X >>> H) >>> H)) >>> cx
    ≡⟨ {!!} ⟩ 
  id⇔ *** (H >>> X) >>> cx
    ≡⟨ {!!} ⟩
  (cz >>> (id⇔ *** H) >>> (id⇔ *** X)) ≡∎


measure : measureϕ ≡ (H >>> measureZ >>> H)
measure =
  measureϕ
    ≡⟨ {!!} ⟩
  (H >>> measureZ >>> H) ≡∎

---------------------------------------------------------------------------

