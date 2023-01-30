{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Terms where

open import Data.Nat using (ℕ; zero; suc)

open import Pi.Types using (U; I; _×ᵤ_; 𝟚)
open import Pi.Language as Π using (_⟷_)
import Pi.Terms as ΠT

open import QPi.Syntax

---------------------------------------------------------------------------

private
  variable
    t t₁ t₂ : U

---------------------------------------------------------------------------
-- Infrastructure for examples

repeat : ℕ → (t ⇔ t) → (t ⇔ t)
repeat 0 c = id⇔
repeat 1 c = c
repeat (suc n@(suc _)) c = c >>> repeat n c

map3*** : (t₁ ⇔ t₂) → ((t₁ ×ᵤ t₁ ×ᵤ t₁) ⇔ (t₂ ×ᵤ t₂ ×ᵤ t₂))
map3*** f = f *** f *** f

map4*** : (t₁ ⇔ t₂) → ((t₁ ×ᵤ t₁ ×ᵤ t₁ ×ᵤ t₁) ⇔ (t₂ ×ᵤ t₂ ×ᵤ t₂  ×ᵤ t₂))
map4*** f = f *** f *** f *** f

---------------------------------------------------------------------------
-- Examples

-- Basic gates, states, and effects

X H Z : 𝟚 ⇔ 𝟚
X = arrZ Π.swap₊ 
H = arrϕ Π.swap₊
Z = H >>> X >>> H

ctrlZ : (t ⟷ t) → 𝟚 ×ᵤ t ⇔ 𝟚 ×ᵤ t
ctrlZ c = arrZ (ΠT.ctrl c)

cx cz : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cx = ctrlZ Π.swap₊ 
cz = id⇔ *** H >>> cx >>> id⇔ *** H

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = arrZ ΠT.ccx

one plus minus : I ⇔ 𝟚 
one = zero >>> X
plus = zero >>> H
minus = plus >>> Z

assertOne assertPlus assertMinus : 𝟚 ⇔ I
assertOne = X >>> assertZero
assertPlus = H >>> assertZero
assertMinus = Z >>> assertPlus

{--

showAll X
(𝕋 , (𝔽 , 1) ∷ []) ∷
(𝔽 , (𝕋 , 1) ∷ []) ∷
[]

showAll H
(𝕋 , (𝕋 , 0.7071067811706743) ∷ (𝔽 , 0.707106781202421) ∷ []) ∷
(𝔽 , (𝕋 , 0.707106781202421) ∷ (𝔽 , -0.7071067811706743) ∷ []) ∷
[]

showAll cx
((𝕋 , 𝕋) , ((𝕋 , 𝔽) , 1) ∷ []) ∷
((𝕋 , 𝔽) , ((𝕋 , 𝕋) , 1) ∷ []) ∷
((𝔽 , 𝕋) , ((𝔽 , 𝕋) , 1) ∷ []) ∷
((𝔽 , 𝔽) , ((𝔽 , 𝔽) , 1) ∷ []) ∷
[]

--}

-- Classical structures

copyZ copyϕ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyZ = uniti⋆r >>> (id⇔ *** zero) >>> cx
copyϕ = H >>> copyZ >>> (H *** H)

-- Simon

cxGroup : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
cxGroup = Π.id⟷

simon : I ×ᵤ I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
simon = map4*** zero >>>
        H *** H *** id⇔ *** id⇔ >>>
        arrZ cxGroup >>>
        H *** H *** id⇔ *** id⇔ 

-- Grover

amp : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 
amp = map3*** H >>>
      map3*** X >>>
      id⇔ *** id⇔ *** H >>>
      ccx >>>
      id⇔ *** id⇔ *** H >>>
      map3*** X >>>
      map3*** H

u : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
u = id⇔ *** id⇔ *** id⇔

-- Complex numbers
-- ctrl S

ctrlS : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ctrlS = (id⇔ *** id⇔ *** H) >>>
        ccx >>>
        (id⇔ *** id⇔ *** H) >>>
        ccx

{--
showAll ctrlS
((𝔽 , 𝔽 , 𝔽) , ((𝔽 , 𝔽 , 𝔽) , 1.0000000000000004) ∷ []) ∷
((𝔽 , 𝔽 , 𝕋) , ((𝔽 , 𝔽 , 𝕋) , 1.0000000000000004) ∷ []) ∷
((𝔽 , 𝕋 , 𝔽) , ((𝔽 , 𝕋 , 𝔽) , 1.0000000000000004) ∷ []) ∷
((𝔽 , 𝕋 , 𝕋) , ((𝔽 , 𝕋 , 𝕋) , 1.0000000000000004) ∷ []) ∷
((𝕋 , 𝔽 , 𝔽) , ((𝕋 , 𝔽 , 𝔽) , 1.0000000000000004) ∷ []) ∷
((𝕋 , 𝔽 , 𝕋) , ((𝕋 , 𝔽 , 𝕋) , 1.0000000000000004) ∷ []) ∷
((𝕋 , 𝕋 , 𝔽) , ((𝕋 , 𝕋 , 𝕋) , 1.0000000000000004) ∷ []) ∷
((𝕋 , 𝕋 , 𝕋) , ((𝕋 , 𝕋 , 𝔽) , -1.0000000000000002) ∷ []) ∷
[]

--}

---------------------------------------------------------------------------
---------------------------------------------------------------------------
