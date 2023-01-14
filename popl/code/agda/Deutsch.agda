module Deutsch where

open import Data.Float
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.List

open import Pi.Types using (U; I; 𝟚; _×ᵤ_; 𝔽; 𝕋)
open import Pi.Language using (_⟷_; !⟷)
open import Pi.Equivalences using (_⟷₂_)
open import Reasoning using (hadInv)
open import QPi.Syntax using (_⇔_; id⇔; swap⋆; unite⋆r; _***_; _>>>_; zero; inv)
open import QPi.Terms using (one; X; H; Z; cx; cz; plus; minus)
open import QPi.Measurement using (measureZ; discard)
open import QPi.Execute using (run; ket)
open import QPi.Equivalences
open import QPi.TermReasoning

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

czS : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
czS = swap⋆ >>> cz >>> swap⋆

deutschNF : I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚
deutschNF =
      zero *** zero
  >>> id⇔ *** H
  >>> X *** id⇔
  >>> czS

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

cxS : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cxS = swap⋆ >>> cx >>> swap⋆ 

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

pmcx : plus *** minus >>> cx ≡ minus *** minus
pmcx = {!!}

mpcxS : minus *** plus >>> cxS ≡ minus *** minus
mpcxS = {!!}

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
