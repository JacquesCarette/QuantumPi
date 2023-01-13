module Deutsch where

open import Data.Float
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.List

open import Pi.Types using (U; I; 𝟚; _×ᵤ_; 𝔽; 𝕋)
open import Reasoning using (hadInv)
open import QPi.Syntax using (_⇔_; id⇔; swap⋆; unite⋆r; _***_; _>>>_; zero)
open import QPi.Terms using (one; X; H; Z; cx; cz; plus; minus)
open import QPi.Measurement using (measureZ; discard)
open import QPi.Execute using (run; ket)
open import QPi.Equivalences
open import QPi.TermReasoning

-- Regular Deutsch circuit for f = id

deutsch : I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚
-- deutsch : I ×ᵤ I ⇔ 𝟚
deutsch =
      zero *** one
  >>> H *** H 
  >>> cx
  >>> H *** id⇔
--  >>> measureZ *** discard >>> unite⋆r
  
deutschNF : I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚
-- deutschNF : I ×ᵤ I ⇔ 𝟚 
deutschNF =
      zero *** zero
  >>> id⇔ *** H
  >>> X *** id⇔
  >>> swap⋆ >>> cz >>> swap⋆
--  >>> measureZ *** discard >>> unite⋆r

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

oneH : one >>> H ≡ minus
oneH = begin
  (zero >>> X) >>> H
    ≡⟨ assoc>>>r ⟩
  zero >>> X >>> H
    ≡⟨ id⟩◎⟨ (idl>>>r ◯ (!≡ hadInv ⟩◎⟨id) ◯ assoc>>>r) ⟩ 
  zero >>> H >>> H >>> X >>> H
    ≡⟨ assoc>>>l ⟩
  plus >>> Z ∎

Hminus : minus >>> H ≡ one
Hminus = begin
  minus >>> H
    ≡⟨ (!≡ oneH) ⟩◎⟨id ⟩
  (one >>> H) >>> H
    ≡⟨ assoc>>>r ◯ id⟩◎⟨ hadInv ◯ idr>>>l ⟩
  one ∎

pmcx : plus *** minus >>> cx ≡ minus *** minus
pmcx = begin
  plus *** minus >>> cx
    ≡⟨ {!!} ⟩
  minus *** minus ∎

eq1 : deutsch ≡ one *** minus
eq1 = begin
  zero *** one >>> H *** H >>> cx >>> H *** id⇔
    ≡⟨ assoc>>>l ◯ (homL*** ◯ cong*** id≡ oneH) ⟩◎⟨id ⟩ 
  plus *** minus >>> cx >>> H *** id⇔
    ≡⟨ assoc>>>l ◯ pmcx ⟩◎⟨id ⟩
  minus *** minus >>> H *** id⇔
    ≡⟨ homL*** ◯ cong*** Hminus idr>>>l ⟩
  one *** minus ∎

pocz : plus *** one >>> cz ≡ minus *** one
pocz = begin
  plus *** one >>> cz
    ≡⟨ {!!} ⟩
  minus *** one ∎

eq2 : deutschNF ≡ one *** minus
eq2 = begin
  zero *** zero >>> id⇔ *** H >>> X *** id⇔ >>> swap⋆ >>> cz >>> swap⋆
    ≡⟨ assoc>>>l ◯ (homL*** ◯ cong*** idr>>>l id≡) ⟩◎⟨id ⟩ 
  zero *** plus >>> X *** id⇔ >>> swap⋆ >>> cz >>> swap⋆
    ≡⟨ assoc>>>l ◯ (homL*** ◯ cong*** id≡ idr>>>l) ⟩◎⟨id ⟩
  one *** plus >>> swap⋆ >>> cz >>> swap⋆
    ≡⟨ assoc>>>l ◯ swapr⋆≡ ⟩◎⟨id ◯ assoc>>>r ⟩
  swap⋆ >>> plus *** one >>> cz >>> swap⋆
    ≡⟨ id⟩◎⟨ (assoc>>>l ◯ pocz ⟩◎⟨id) ⟩
  swap⋆ >>> minus *** one >>> swap⋆
    ≡⟨ id⟩◎⟨ swapr⋆≡ ⟩
  swap⋆ >>> swap⋆ >>> one *** minus
    ≡⟨ assoc>>>l ◯ {!rinv>>>l!} ⟩◎⟨id ⟩ 
  id⇔ >>> one *** minus
    ≡⟨ idl>>>l ⟩ 
  one *** minus ∎
        
