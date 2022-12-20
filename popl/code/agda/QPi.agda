{-# OPTIONS --without-K #-}

module QPi where

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

xgate had zgate : 𝟚 ⇔ 𝟚
xgate = arrZ Π.swap₊ 
had = arrϕ Π.swap₊
zgate = had >>> xgate >>> had

ctrlZ : (t ⟷ t) → 𝟚 ×ᵤ t ⇔ 𝟚 ×ᵤ t
ctrlZ c = arrZ (ΠT.ctrl c)

cx cz : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cx = ctrlZ Π.swap₊ 
cz = id⇔ *** had >>> cx >>> id⇔ *** had

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = arrZ ΠT.ccx

one plus minus : I ⇔ 𝟚 
one = zero >>> xgate
plus = zero >>> had
minus = plus >>> zgate

assertOne assertPlus assertMinus : 𝟚 ⇔ I
assertOne = xgate >>> assertZero
assertPlus = had >>> assertZero
assertMinus = zgate >>> assertPlus

{--

showAll xgate
(𝕋 , (𝔽 , 1) ∷ []) ∷
(𝔽 , (𝕋 , 1) ∷ []) ∷
[]

showAll had
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
copyϕ = had >>> copyZ >>> (had *** had)

-- Simon

cxGroup : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
cxGroup = Π.id⟷

simon : I ×ᵤ I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
simon = map4*** zero >>>
        had *** had *** id⇔ *** id⇔ >>>
        arrZ cxGroup >>>
        had *** had *** id⇔ *** id⇔ 

-- postulate measurement

postulate
  discard : t ⇔ I

fst : (t₁ ×ᵤ t₂) ⇔ t₁
fst = (id⇔ *** discard) >>> unite⋆r

snd : (t₁ ×ᵤ t₂) ⇔ t₂
snd = swap⋆ >>> fst

measureZ measureϕ : 𝟚 ⇔ 𝟚
measureZ = copyZ >>> fst
measureϕ = copyϕ >>> fst

-- Grover

amp : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 
amp = map3*** had >>>
      map3*** xgate >>>
      id⇔ *** id⇔ *** had >>>
      ccx >>>
      id⇔ *** id⇔ *** had >>>
      map3*** xgate >>>
      map3*** had

u : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
u = id⇔ *** id⇔ *** id⇔

grover₃ : I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
grover₃ = map3*** plus >>>
          repeat 3 (u >>> amp) >>>
          map3*** measureZ
  
-- Complex numbers
-- ctrl S

ctrlS : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ctrlS = (id⇔ *** id⇔ *** had) >>>
        ccx >>>
        (id⇔ *** id⇔ *** had) >>>
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
