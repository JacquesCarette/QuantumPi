module Deutsch where

open import Data.Float
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.List

open import Pi.Types using (U; I; 𝟚; _×ᵤ_; 𝔽; 𝕋)
open import Pi.Language using (_⟷_; id⟷; swap₊; _⊕_; _⊗_; dist; factor; !⟷)
open import Pi.Equivalences using (_⟷₂_; assoc◎r)
open import Reasoning 
open import QPi.Syntax
open import QPi.Terms
open import QPi.Measurement using (measureZ; discard)
open import QPi.Execute using (run; ket)
open import QPi.Equivalences
open import QPi.TermReasoning

------------------------------------------------------------------------------------
-- Circuit for Deutsch and its NF 

private
  variable
    t₁ t₂ : U
    c : t₁ ⟷ t₂

-- Regular Deutsch circuit for f = id

deutsch : I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚
deutsch =
      zero *** one
  >>> H *** H 
  >>> cx
  >>> H *** id⇔

deutschNF : I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚
deutschNF =
      zero *** zero
  >>> id⇔ *** H
  >>> X *** id⇔
  >>> swap⋆ >>> cz >>> swap⋆

-- The two circuits are extensionally equivalent

test1 = run deutsch (ket (tt , tt))
{--
((𝕋 , 𝔽) , 0.7071067811865479) ∷
((𝕋 , 𝕋) , -0.7071067811865477) ∷ []
--}

test2 = run deutschNF (ket (tt , tt))
{--
((𝕋 , 𝔽) , 0.7071067811706745) ∷
((𝕋 , 𝕋) , -0.7071067812024211) ∷ []
--}

------------------------------------------------------------------------------------
-- Proof of equivalence

cxS czS : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 
cxS = swap⋆ >>> cx >>> swap⋆
czS = swap⋆ >>> cz >>> swap⋆

oneH : one >>> H ≡ minus
oneH = begin
  (zero >>> X) >>> H
    ≡⟨ assoc>>>r ⟩
  zero >>> X >>> H
    ≡⟨ id⟩◎⟨ (idl>>>r ◯ (!≡ hadInv ⟩◎⟨id) ◯ assoc>>>r) ⟩ 
  zero >>> H >>> H >>> X >>> H
    ≡⟨ assoc>>>l ⟩
  plus >>> Z ∎

minusH : minus >>> H ≡ one
minusH = begin
  minus >>> H
    ≡⟨ (!≡ oneH) ⟩◎⟨id ⟩
  (one >>> H) >>> H
    ≡⟨ assoc>>>r ◯ id⟩◎⟨ hadInv ⟩
  one >>> id⇔
    ≡⟨ idr>>>l ⟩
  one ∎

czcx : czS ≡ H *** id⇔ >>> cxS >>> H *** id⇔
czcx = begin
  swap⋆ >>> cz >>> swap⋆
    ≡⟨ id⟩◎⟨ (assoc>>>l ⟩◎⟨id) ◯ id⟩◎⟨ trans≡ assoc>>>r assoc>>>r ⟩
  swap⋆ >>> id⇔ *** H >>> cx >>> id⇔ *** H >>> swap⋆
    ≡⟨ assoc>>>l ◯ swapl⋆≡ ⟩◎⟨id ◯ assoc>>>r ⟩ 
  H *** id⇔ >>> swap⋆ >>> cx >>> id⇔ *** H >>> swap⋆ 
    ≡⟨ id⟩◎⟨ id⟩◎⟨ id⟩◎⟨ swapr⋆≡ ⟩ 
  H *** id⇔ >>> swap⋆ >>> cx >>> swap⋆ >>> H *** id⇔
    ≡⟨ id⟩◎⟨ (trans≡ assoc>>>l assoc>>>l ◯ assoc>>>r ⟩◎⟨id) ⟩ 
  H *** id⇔ >>> cxS >>> H *** id⇔ ∎

invCx : inv cx ≡ cx
invCx = classicalZ assoc◎r

invCopyZ : inv copyZ ≡ cx >>> (id⇔ *** assertZero) >>> unite⋆r
invCopyZ = assoc>>>r ◯ invCx ⟩◎⟨id 

invCopyϕ : inv copyϕ ≡
           (H *** H) >>> cx >>> (id⇔ *** assertZero) >>> unite⋆r >>> H
invCopyϕ = begin
  inv copyϕ
    ≡⟨ pullʳ (invCopyZ ⟩◎⟨id) ⟩
  (H *** H) >>> (cx >>> (id⇔ *** assertZero) >>> unite⋆r) >>> H 
    ≡⟨ id⟩◎⟨ (pullʳ assoc>>>r) ⟩
  (H *** H) >>> cx >>> (id⇔ *** assertZero) >>> unite⋆r >>> H ∎

cxexp : copyZ *** id⇔ >>> assocr⋆ >>> id⇔ *** inv copyϕ ≡ cx
cxexp = begin
  copyZ *** id⇔ >>> assocr⋆ >>> id⇔ *** inv copyϕ
    ≡⟨ {!!} ⟩
  cx ∎

pmcx : plus *** minus >>> cx ≡ minus *** minus
pmcx = begin
  plus *** minus >>> cx
    ≡⟨ {!!} ⟩ 
  minus *** minus ∎

mpcxS : minus *** plus >>> cxS ≡ minus *** minus
mpcxS = begin
  minus *** plus >>> cxS
    ≡⟨ {!!} ⟩
  minus *** minus ∎

eq1 : deutsch ≡ one *** minus
eq1 = begin
  zero *** one >>> H *** H >>> cx >>> H *** id⇔
    ≡⟨ assoc>>>l ◯ (homL*** ◯ cong*** id≡ oneH) ⟩◎⟨id ⟩ 
  plus *** minus >>> cx >>> H *** id⇔ 
    ≡⟨ assoc>>>l ◯ pmcx ⟩◎⟨id ⟩
  minus *** minus >>> H *** id⇔     
    ≡⟨ homL*** ◯ cong*** minusH idr>>>l ⟩
  one *** minus ∎

eq2 : deutschNF ≡ one *** minus 
eq2 = begin
  zero *** zero >>> id⇔ *** H >>> X *** id⇔ >>> czS
    ≡⟨ id⟩◎⟨ (assoc>>>l ◯ (homL*** ◯ cong*** idl>>>l idr>>>l) ⟩◎⟨id) ⟩ 
  zero *** zero >>> X *** H >>> czS
    ≡⟨ assoc>>>l ◯ (homL*** ⟩◎⟨id) ⟩
  one *** plus >>> czS
    ≡⟨ id⟩◎⟨ czcx ⟩ 
  one *** plus >>> H *** id⇔ >>> cxS >>> H *** id⇔
    ≡⟨ assoc>>>l ◯ (homL*** ◯ cong*** oneH idr>>>l) ⟩◎⟨id ⟩ 
  minus *** plus >>> cxS >>> H *** id⇔ 
    ≡⟨ assoc>>>l ◯ mpcxS ⟩◎⟨id ⟩ 
  minus *** minus >>> H *** id⇔ 
    ≡⟨ homL*** ◯ cong*** minusH idr>>>l ⟩ 
  one *** minus ∎

eq : deutsch ≡ deutschNF
eq = trans≡ eq1 (!≡ eq2)

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

L1 L2 L3 : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 

L1 = copyZ *** id⇔ >>>
     assocr⋆ >>>
     id⇔ *** inv copyϕ >>>
     id⇔ *** copyϕ >>>
     assocl⋆ >>>
     inv copyZ *** id⇔

L2 = uniti⋆r *** id⇔ >>>
     (id⇔ *** zero) *** id⇔ >>>
     cx *** id⇔ >>>
     assocr⋆ >>>
     id⇔ *** H *** H >>> 
     id⇔ *** cx >>>
     id⇔ *** id⇔ *** assertZero >>>
     id⇔ *** unite⋆r >>> 
     id⇔ *** H >>>
     id⇔ *** H >>> 
     id⇔ *** uniti⋆r >>> 
     id⇔ *** id⇔ *** zero >>> 
     id⇔ *** cx >>>
     id⇔ *** H *** H >>>
     assocl⋆ >>>
     cx *** id⇔ >>>
     (id⇔ *** assertZero) *** id⇔ >>>
     unite⋆r *** id⇔

L3 = uniti⋆r *** id⇔ >>>
     (id⇔ *** zero) *** id⇔ >>>
     cx *** id⇔ >>>
     assocr⋆ >>>
     id⇔ *** H *** H >>> 
     id⇔ *** cx >>>
     id⇔ *** id⇔ *** assertZero >>>
     id⇔ *** id⇔ *** zero >>> 
     id⇔ *** cx >>>
     id⇔ *** H *** H >>>
     assocl⋆ >>>
     cx *** id⇔ >>>
     (id⇔ *** assertZero) *** id⇔ >>>
     unite⋆r *** id⇔




{--

cx : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 
cx = id *** copyϕ >>> assocl >>> inv copyZ *** id

zero *** plus >>> inv copyϕ ≡ plus
zero *** plus >>> inv copyZ ≡ zero

pmcx  : plus  *** minus >>> cx  ≡ minus *** minus
mpcxS : minus *** plus  >>> cxS ≡ minus *** minus

copyZ = uniti⋆r >>> (id⇔ *** zero) >>> cx
copyϕ = H >>> copyZ >>> (H *** H)

--}
