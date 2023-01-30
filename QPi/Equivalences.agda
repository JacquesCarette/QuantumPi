{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Equivalences where

open import Pi.Types using (U; _×ᵤ_)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷; _⊗_)
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
  arrZidL  : arrZ (id⟷ {t}) ≡ id⇔ 
  arrZidR  : id⇔  ≡ arrZ (id⟷ {t})
  arrϕidL  : arrϕ (id⟷ {t}) ≡ id⇔ 
  arrϕidR  : id⇔  ≡ arrϕ (id⟷ {t})
  arrZL    : (arrZ (c₁ ◎ c₂)) ≡ (arrZ c₁ >>> arrZ c₂)
  arrZR    : (arrZ c₁ >>> arrZ c₂) ≡ (arrZ (c₁ ◎ c₂))
  arrϕL    : (arrϕ (c₁ ◎ c₂)) ≡ (arrϕ c₁ >>> arrϕ c₂)
  arrϕR    : (arrϕ c₁ >>> arrϕ c₂) ≡ (arrϕ (c₁ ◎ c₂))
  arrZL*   : (arrZ (c₁ ⊗ c₂)) ≡ (arrZ c₁ *** arrZ c₂)
  arrZR*   : (arrZ c₁ *** arrZ c₂) ≡ (arrZ (c₁ ⊗ c₂))
  arrϕL*   : (arrϕ (c₁ ⊗ c₂)) ≡ (arrϕ c₁ *** arrϕ c₂)
  arrϕR*   : (arrϕ c₁ *** arrϕ c₂) ≡ (arrϕ (c₁ ⊗ c₂))
  -- monoidal coherence
  assoc>>>l   : (d₁ >>> (d₂ >>> d₃)) ≡ ((d₁ >>> d₂) >>> d₃)
  assoc>>>r   : ((d₁ >>> d₂) >>> d₃) ≡ (d₁ >>> (d₂ >>> d₃))
  assocl***l  : ((d₁ *** (d₂ *** d₃)) >>> assocl⋆) ≡ (assocl⋆ >>> ((d₁ *** d₂) *** d₃))
  assocl***r  : (assocl⋆ >>> ((d₁ *** d₂) *** d₃)) ≡ ((d₁ *** (d₂ *** d₃)) >>> assocl⋆)
  assocr***l  : (assocr⋆ >>> (d₁ *** (d₂ *** d₃))) ≡ (((d₁ *** d₂) *** d₃) >>> assocr⋆)
  assocr***r  : (((d₁ *** d₂) *** d₃) >>> assocr⋆) ≡ (assocr⋆ >>> (d₁ *** (d₂ *** d₃)))
  idl>>>l     : (id⇔ >>> d) ≡ d
  idl>>>r     : d ≡ (id⇔ >>> d)
  idr>>>l     : (d >>> id⇔) ≡ d
  idr>>>r     : d ≡ (d >>> id⇔)
  -- other combinators ok; not just swap; but not zero/assertZero
  linv>>>l    : (swap⋆ >>> inv swap⋆) ≡ id⇔ {t₁ ×ᵤ t₂}
  linv>>>r    : id⇔ {t₁ ×ᵤ t₂} ≡ (swap⋆ >>> inv swap⋆)  
  rinv>>>l    : (inv swap⋆  >>> swap⋆ ) ≡ id⇔ {t₁ ×ᵤ t₂}
  rinv>>>r    : id⇔ {t₁ ×ᵤ t₂} ≡ (inv swap⋆  >>> swap⋆ )
  unitel⋆≡r   : (unite⋆r >>> d₂) ≡ ((d₂ *** d₁) >>> unite⋆r)
  uniter⋆≡r   : ((d₂ *** d₁) >>> unite⋆r) ≡ (unite⋆r >>> d₂)
  unitil⋆≡r   : (uniti⋆r >>> (d₂ *** d₁)) ≡ (d₂ >>> uniti⋆r)
  unitir⋆≡r   : (d₂ >>> uniti⋆r) ≡ (uniti⋆r >>> (d₂ *** d₁))
  swapl⋆≡     : (swap⋆ >>> (d₁ *** d₂)) ≡ ((d₂ *** d₁) >>> swap⋆)
  swapr⋆≡     : ((d₂ *** d₁) >>> swap⋆) ≡ (swap⋆ >>> (d₁ *** d₂))
  id≡         : d ≡ d
  trans≡      : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
  -- congruence; functor
  cong≡        : (d₁ ≡ d₃) → (d₂ ≡ d₄) → ((d₁ >>> d₂) ≡ (d₃ >>> d₄))
  cong***      : (d₁ ≡ d₃) → (d₂ ≡ d₄) → ((d₁ *** d₂) ≡ (d₃ *** d₄))
  homL***      : ((d₁ *** d₂) >>> (d₃ *** d₄)) ≡ ((d₁ >>> d₃) *** (d₂ >>> d₄))
  homR***      : ((d₁ >>> d₃) *** (d₂ >>> d₄)) ≡ ((d₁ *** d₂) >>> (d₃ *** d₄))
  id***id      : {t₁ t₂ : U} → (id⇔ {t₁} *** id⇔ {t₂}) ≡ id⇔
  split***-id  : {t₁ t₂ : U} → (id⇔ {_×ᵤ_ t₁ t₂}) ≡ (id⇔ *** id⇔)
  -- execution equations
  e1L : zero >>> assertZero ≡ id⇔
  e1R : id⇔ ≡ zero >>> assertZero
  e2L : (zero *** id⇔) >>> ctrlZ c ≡ zero *** id⇔
  e2R : zero *** id⇔ ≡ (zero *** id⇔) >>> ctrlZ c
  e3L : (one *** id⇔) >>> ctrlZ c ≡ one *** arrZ c
  e3R : one *** arrZ c ≡ (one *** id⇔) >>> ctrlZ c
  -- complementarity
  C   : ((copyZ *** id⇔) >>> assocr⋆ >>> (id⇔ *** (inv copyϕ)) >>>
        (id⇔ *** copyϕ) >>> assocl⋆ >>> ((inv copyZ) *** id⇔))
        ≡ id⇔
  C˘  : id⇔ ≡ ((copyZ *** id⇔) >>> assocr⋆ >>> (id⇔ *** (inv copyϕ)) >>>
        (id⇔ *** copyϕ) >>> assocl⋆ >>> ((inv copyZ) *** id⇔))

---------------------------------------------------------------------------

-- _≡_ should be an equivalence relation, so invertible. It's syntactically
-- so close, may as well finish it.
!≡ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⇔ t₂} → c₁ ≡ c₂ → c₂ ≡ c₁
!≡ (classicalZ x) = classicalZ (!⟷₂ x)
!≡ (classicalϕ x) = classicalϕ (!⟷₂ x)
!≡ arrZidL = arrZidR
!≡ arrZidR = arrZidL
!≡ arrϕidL = arrϕidR
!≡ arrϕidR = arrϕidL
!≡ arrZL = arrZR
!≡ arrZR = arrZL
!≡ arrϕL = arrϕR
!≡ arrϕR = arrϕL
!≡ arrZL* = arrZR*
!≡ arrZR* = arrZL*
!≡ arrϕL* = arrϕR*
!≡ arrϕR* = arrϕL*
!≡ assoc>>>l = assoc>>>r
!≡ assoc>>>r = assoc>>>l
!≡ assocl***l = assocl***r
!≡ assocl***r = assocl***l
!≡ assocr***l = assocr***r
!≡ assocr***r = assocr***l
!≡ idl>>>l = idl>>>r
!≡ idl>>>r = idl>>>l
!≡ idr>>>l = idr>>>r
!≡ idr>>>r = idr>>>l
!≡ linv>>>l = linv>>>r
!≡ linv>>>r = linv>>>l
!≡ rinv>>>l = rinv>>>r
!≡ rinv>>>r = rinv>>>l
!≡ unitel⋆≡r = uniter⋆≡r
!≡ uniter⋆≡r = unitel⋆≡r
!≡ unitil⋆≡r = unitir⋆≡r
!≡ unitir⋆≡r = unitil⋆≡r
!≡ swapl⋆≡ = swapr⋆≡
!≡ swapr⋆≡ = swapl⋆≡
!≡ id≡ = id≡
!≡ (trans≡ x x₁) = trans≡ (!≡ x₁) (!≡ x)
!≡ (cong≡ x x₁) = cong≡ (!≡ x) (!≡ x₁)
!≡ (cong*** x x₁) = cong*** (!≡ x) (!≡ x₁)
!≡ homL*** = homR***
!≡ homR*** = homL***
!≡ id***id = split***-id
!≡ split***-id = id***id
!≡ e1L = e1R
!≡ e1R = e1L
!≡ e2L = e2R
!≡ e2R = e2L
!≡ e3L = e3R
!≡ e3R = e3L
!≡ C = C˘
!≡ C˘ = C
