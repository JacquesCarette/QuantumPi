module Deutsch where

open import Data.Float
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.List

open import Pi.Types using (U; I; 𝟚; _×ᵤ_; 𝔽; 𝕋)
open import QPi.Syntax using (_⇔_; id⇔; swap⋆; unite⋆r; _***_; _>>>_; zero)
open import QPi.Terms using (one; X; H; cx; cz)
open import QPi.Measurement using (measureZ; discard)
open import QPi.Execute using (showAll)

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

test1 = showAll deutsch
test2 = showAll deutschNF

{--

(tt , tt) ,

((𝕋 , 𝔽) , 0.7071067811706745) ∷
((𝕋 , 𝕋) , -0.7071067812024211)

--}

