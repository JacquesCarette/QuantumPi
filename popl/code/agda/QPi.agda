{-# OPTIONS --without-K #-}

module QPi where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float; _≤ᵇ_; _<ᵇ_)
  renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; _∨_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.List using (List; _∷_; []; map; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax using (U; O; I; _+ᵤ_; _×ᵤ_; 𝟚; 𝔽; 𝕋; ⟦_⟧; enum)  
  renaming (_⟷₁_ to _⟷_)
open import ArrowsOverAmalg using (arr₁; arr₂)
open import StatesAndEffects using (StEffPi; arr; _>>>>_; invSE)
  renaming (zero to kzero; assertZero to bzero; _***_ to _****_)
open import Instances using (evalSE)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  10 _⇔_
infixr 30 _>>>_
infixr 40 _***_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-- Arrow combinators

data _⇔_ : U → U → Set where
  arrZ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
  arrϕ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
  -- multiplicative structure
  unite⋆   : t ×ᵤ I ⇔ t
  uniti⋆   : t ⇔ t ×ᵤ I
  swap⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  -- composition
  id⇔    : t ⇔ t
  _>>>_  : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _***_  : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
  inv    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
  -- states and effects
  zero        : I ⇔ 𝟚
  assertZero  : 𝟚 ⇔ I

---------------------------------------------------------------------------
-- Semantics

private
  variable
    c c₁ c₂ c₃ c₄ c₅ c₆ : t₁ ⟷ t₂

private
  variable
    d d₁ d₂ d₃ d₄ d₅ d₆ : t₁ ⇔ t₂

pizA piϕA : (t₁ ⟷ t₂) → StEffPi t₁ t₂
pizA c = arr (arr₁ c)
piϕA c = arr (arr₂ c)

embed : (t₁ ⇔ t₂) → StEffPi t₁ t₂
embed (arrZ c) = pizA c
embed (arrϕ c) = piϕA c
embed unite⋆ = pizA PiSyntax.unite⋆r
embed uniti⋆ = pizA PiSyntax.uniti⋆r
embed swap⋆ = pizA PiSyntax.swap⋆
embed assocl⋆ = pizA PiSyntax.assocl⋆
embed assocr⋆ = pizA PiSyntax.assocr⋆
embed id⇔ = pizA PiSyntax.id⟷₁
embed (d₁ >>> d₂) = embed d₁ >>>> embed d₂ 
embed (d₁ *** d₂) = embed d₁ **** embed d₂ 
embed (inv d) = invSE (embed d)
embed zero = kzero
embed assertZero = bzero

---------------------------------------------------------------------------
-- Infrstructure for examples

K : U → Set
K t = ⟦ t ⟧ → Float

tooSmall : Float → Bool
tooSmall a = ((0.0 ≤ᵇ a) ∧ (a <ᵇ 0.01)) ∨ ((a ≤ᵇ 0.0) ∧ (-0.01 <ᵇ a))

show : {t : U} → K t → List (⟦ t ⟧ × Float)
show {t} v =
  foldr (λ i r → let a = v i in if tooSmall a then r else (i , a) ∷ r)
        [] 
        (enum t)

_≟_ : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → Bool
_≟_ {I} tt tt = true
_≟_ {t₁ +ᵤ t₂} (inj₁ v) (inj₁ w) = v ≟ w
_≟_ {t₁ +ᵤ t₂} (inj₁ v) (inj₂ w) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ v) (inj₁ w) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ v) (inj₂ w) = v ≟ w
_≟_ {t₁ ×ᵤ t₂} (v₁ , w₁) (v₂ , w₂) = v₁ ≟ v₂ ∧ w₁ ≟ w₂

ket : ⟦ t ⟧ → K t
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
repeat (suc n) c = c >>> repeat n c

map3*** : (t₁ ⇔ t₂) → ((t₁ ×ᵤ t₁ ×ᵤ t₁) ⇔ (t₂ ×ᵤ t₂ ×ᵤ t₂))
map3*** f = f *** f *** f

map4*** : (t₁ ⇔ t₂) → ((t₁ ×ᵤ t₁ ×ᵤ t₁ ×ᵤ t₁) ⇔ (t₂ ×ᵤ t₂ ×ᵤ t₂  ×ᵤ t₂))
map4*** f = f *** f *** f *** f

---------------------------------------------------------------------------
-- Examples

-- Basic gates, states, and effects

xgate had zgate : 𝟚 ⇔ 𝟚
xgate = arrZ PiSyntax.swap₊ 
had = arrϕ PiSyntax.swap₊
zgate = had >>> xgate >>> had
  
cx cz : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cx = arrZ PiSyntax.cx
cz = id⇔ *** had >>> cx >>> id⇔ *** had

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = arrZ PiSyntax.ccx

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
cxGroup = PiSyntax.id⟷₁

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
