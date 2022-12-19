{-# OPTIONS --without-K #-}

module QPi where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float)
  renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; _∨_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.List using (List; _∷_; []; map; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pi.Types using (U; O; I; _+ᵤ_; _×ᵤ_; ⟦_⟧; enum; _≟_; 𝟚; 𝔽; 𝕋)
open import PiSyntax as Π using (_⟷_)
open import ArrowsOverAmalg using (arr₁; arr₂)
open import StatesAndEffects using (_↭_; arr; _>>>>_; invSE)
  renaming (zero to kzero; assertZero to bzero; _***_ to _****_)
open import Instances using (evalSE)
open import FloatUtils using (vec; mat; tooSmall)

open import QPi.Syntax

---------------------------------------------------------------------------
-- Semantics

private
  variable
    t t₁ t₂ : U
    c c₁ c₂ c₃ c₄ c₅ c₆ : t₁ ⟷ t₂
    d d₁ d₂ d₃ d₄ d₅ d₆ : t₁ ⇔ t₂

private
  pizA : (t₁ ⟷ t₂) → t₁ ↭ t₂
  pizA c = arr (arr₁ c)

embed : (t₁ ⇔ t₂) → t₁ ↭ t₂
embed (arrZ c) = pizA c
embed (arrϕ c) = arr (arr₂ c)
embed unite⋆ = pizA Π.unite⋆r
embed uniti⋆ = pizA Π.uniti⋆r
embed swap⋆ = pizA Π.swap⋆
embed assocl⋆ = pizA Π.assocl⋆
embed assocr⋆ = pizA Π.assocr⋆
embed id⇔ = pizA Π.id⟷
embed (d₁ >>> d₂) = embed d₁ >>>> embed d₂ 
embed (d₁ *** d₂) = embed d₁ **** embed d₂ 
embed (inv d) = invSE (embed d)
embed zero = kzero
embed assertZero = bzero

---------------------------------------------------------------------------
-- Infrastructure for examples

K : U → Set
K t = vec ⟦ t ⟧

show : {t : U} → K t → List (⟦ t ⟧ × Float)
show {t} v =
  foldr (λ i r → let a = v i in if tooSmall a then r else (i , a) ∷ r)
        [] 
        (enum t)

ket : mat ⟦ t ⟧
ket v w = if v ≟ w then 1.0 else 0.0

-- show {𝟚 ×ᵤ 𝟚} (ket (𝕋 , 𝔽))

run : (t₁ ⇔ t₂) → K t₁ → List (⟦ t₂ ⟧ × Float)
run c v = show (evalSE (embed c) v)

g : {t₁ t₂ : U} → (t₁ ⇔ t₂) → List (⟦ t₁ ⟧ × List (⟦ t₂ ⟧ × Float))
g {t₁} {t₂} c = map (λ v → (v , run c (ket v))) (enum t₁)

--

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
ctrlZ c = arrZ (Π.ctrl c)

cx cz : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cx = ctrlZ Π.swap₊ 
cz = id⇔ *** had >>> cx >>> id⇔ *** had

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = arrZ Π.ccx

one plus minus : I ⇔ 𝟚 
one = zero >>> xgate
plus = zero >>> had
minus = plus >>> zgate

assertOne assertPlus assertMinus : 𝟚 ⇔ I
assertOne = xgate >>> assertZero
assertPlus = had >>> assertZero
assertMinus = zgate >>> assertPlus

{--

g xgate
(𝕋 , (𝔽 , 1) ∷ []) ∷
(𝔽 , (𝕋 , 1) ∷ []) ∷
[]

g had
(𝕋 , (𝕋 , 0.7071067811706743) ∷ (𝔽 , 0.707106781202421) ∷ []) ∷
(𝔽 , (𝕋 , 0.707106781202421) ∷ (𝔽 , -0.7071067811706743) ∷ []) ∷
[]

g cx
((𝕋 , 𝕋) , ((𝕋 , 𝔽) , 1) ∷ []) ∷
((𝕋 , 𝔽) , ((𝕋 , 𝕋) , 1) ∷ []) ∷
((𝔽 , 𝕋) , ((𝔽 , 𝕋) , 1) ∷ []) ∷
((𝔽 , 𝔽) , ((𝔽 , 𝔽) , 1) ∷ []) ∷
[]

--}

-- Classical structures

copyZ copyϕ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyZ = uniti⋆ >>> (id⇔ *** zero) >>> cx
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
fst = (id⇔ *** discard) >>> unite⋆

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
