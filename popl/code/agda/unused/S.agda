module S where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float) renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.Vec using (Vec; []; _∷_; _++_; map; concat; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 40 _+ᵤ_ _×ᵤ_
infix 30 _⟷_ _⇔_
infixr 10 _◎_ _>>>_
infixr 20 _⊕_
infixr 30 _⊗_ _***_

---------------------------------------------------------------------------
-- Finite types 

data U : Set where
  O : U
  I : U
  _+ᵤ_ : U → U → U
  _×ᵤ_ : U → U → U

𝟚 : U
𝟚 = I +ᵤ I

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

---------------------------------------------------------------------------
-- Combinators for type isomorphisms between finite types

data _⟷_  : U → U → Set where
  -- (+,0) monoid
  unite₊   : t +ᵤ O ⟷  t
  uniti₊   : t ⟷  t +ᵤ O
  swap₊    : t₁ +ᵤ t₂ ⟷  t₂ +ᵤ t₁
  assocl₊  : t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊  : (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  -- (*,1) monoid
  unite⋆   : t ×ᵤ I ⟷  t
  uniti⋆   : t ⟷ t ×ᵤ I
  swap⋆    : t₁ ×ᵤ t₂ ⟷  t₂ ×ᵤ t₁
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  -- distributivity
  absorbr   : O ×ᵤ t ⟷ O
  factorzl  : O ⟷  O ×ᵤ t
  dist      : (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor    : {t₁ t₂ t₃ : U} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  -- composition
  id⟷  : t ⟷  t
  _◎_   : (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  inv   : (t₁ ⟷ t₂) → (t₂ ⟷ t₁)

private
  variable
    c c₁ c₂ c₃ c₄ c₅ c₆ : t₁ ⟷ t₂

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

private
  variable
    d d₁ d₂ d₃ d₄ d₅ d₆ : t₁ ⇔ t₂


---------------------------------------------------------------------------
-- Semantics

⟦_⟧ : U → Set
⟦ O ⟧ = ⊥
⟦ I ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

pattern F = inj₂ tt
pattern T = inj₁ tt

∣_∣ : U → ℕ
∣ O ∣  = 0
∣ I ∣ = 1
∣  t₁ +ᵤ t₂ ∣ = ∣ t₁ ∣ + ∣ t₂ ∣
∣ t₁ ×ᵤ t₂ ∣ = ∣ t₁ ∣ * ∣ t₂ ∣

enum : (t : U) → Vec ⟦ t ⟧ ∣ t ∣
enum O = []
enum I = tt ∷ []
enum (t₁ +ᵤ t₂) = map inj₁ (enum t₁) ++ map inj₂ (enum t₂)
enum (t₁ ×ᵤ t₂) = concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (enum t₂)) (enum t₁))

𝒱 : (t : U) → Set
𝒱 t = ⟦ t ⟧ → Float

show : {t : U} → 𝒱 t → Vec (⟦ t ⟧ × Float) ∣ t ∣
show {t} k = map (λ v → (v , k v)) (enum t) 

_≟_ : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → Bool
_≟_ {O} () v₂
_≟_ {I} tt tt = true
_≟_ {t₁ +ᵤ t₂} (inj₁ v₁) (inj₁ v₂) = v₁ ≟ v₂
_≟_ {t₁ +ᵤ t₂} (inj₁ _) (inj₂ _) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ _) (inj₁ _) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ v₁) (inj₂ v₂) = v₁ ≟ v₂
_≟_ {t₁ ×ᵤ t₂} (v₁ , v₂) (w₁ , w₂) = v₁ ≟ w₁ ∧ v₂ ≟ w₂

● : 𝒱 t
● _ = 0.0

∣_⟩ : ⟦ t ⟧ → 𝒱 t
∣ v ⟩ v' = if v ≟ v' then 1.0 else 0.0

_*⟩_ : Float → 𝒱 t → 𝒱 t
s *⟩ k = λ v → s *f k v

_⟨+⟩_ : 𝒱 t → 𝒱 t → 𝒱 t
k₁ ⟨+⟩ k₂ = λ v → k₁ v +f k₂ v

_⟨*⟩_ : 𝒱 t₁ → 𝒱 t₂ → 𝒱 (t₁ ×ᵤ t₂)
k₁ ⟨*⟩ k₂ = λ (v₁ , v₂) → k₁ v₁ *f k₂ v₂ 

private
  variable
    v v₁ v₂ v₃ v₄ v₅ v₆ : ⟦ t ⟧
    k k₁ k₂ k₃ k₄ k₅ k₆ : 𝒱 t

evalF : (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
evalB : (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧ 

evalF unite₊ (inj₁ v) = v
evalF uniti₊ v = inj₁ v
evalF swap₊ (inj₁ v) = inj₂ v
evalF swap₊ (inj₂ v) = inj₁ v
evalF assocl₊ (inj₁ v) = inj₁ (inj₁ v)
evalF assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
evalF assocl₊ (inj₂ (inj₂ v)) = inj₂ v
evalF assocr₊ (inj₁ (inj₁ v)) = inj₁ v
evalF assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
evalF assocr₊ (inj₂ v) = inj₂ (inj₂ v)
evalF unite⋆ (v , tt) = v
evalF uniti⋆ v = (v , tt)
evalF swap⋆ (v₁ , v₂) = (v₂ , v₁)
evalF assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
evalF assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
evalF dist (inj₁ v₁ , v) = inj₁ (v₁ , v)
evalF dist (inj₂ v₂ , v) = inj₂ (v₂ , v)
evalF factor (inj₁ (v₁ , v)) = (inj₁ v₁ , v)
evalF factor (inj₂ (v₂ , v)) = (inj₂ v₂ , v)
evalF id⟷ v = v
evalF (c₁ ◎ c₂) v = evalF c₂ (evalF c₁ v)
evalF (c₁ ⊕ c₂) (inj₁ v) = inj₁ (evalF c₁ v)
evalF (c₁ ⊕ c₂) (inj₂ v) = inj₂ (evalF c₂ v)
evalF (c₁ ⊗ c₂) (v₁ , v₂) = (evalF c₁ v₁ , evalF c₂ v₂)
evalF (inv c) v = evalB c v

evalB uniti₊ (inj₁ v) = v 
evalB unite₊ v = inj₁ v
evalB swap₊ (inj₂ v) = inj₁ v
evalB swap₊ (inj₁ v) = inj₂ v
evalB assocl₊ (inj₁ (inj₁ v)) = inj₁ v
evalB assocl₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
evalB assocl₊ (inj₂ v) = inj₂ (inj₂ v)
evalB assocr₊ (inj₁ v) = inj₁ (inj₁ v)
evalB assocr₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
evalB assocr₊ (inj₂ (inj₂ v)) = inj₂ v
evalB uniti⋆ (v , tt) = v
evalB unite⋆ v = (v , tt)
evalB swap⋆ (v₁ , v₂) = (v₂ , v₁)
evalB assocl⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
evalB assocr⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
evalB dist (inj₁ (v₁ , v)) = (inj₁ v₁ , v)
evalB dist(inj₂ (v₂ , v)) = (inj₂ v₂ , v)
evalB factor (inj₁ v₁ , v) = inj₁ (v₁ , v)
evalB factor (inj₂ v₂ , v) = inj₂ (v₂ , v)
evalB id⟷ v = v
evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
evalB (c₁ ⊕ c₂) (inj₁ v) = inj₁ (evalB c₁ v)
evalB (c₁ ⊕ c₂) (inj₂ v) = inj₂ (evalB c₂ v)
evalB (c₁ ⊗ c₂) (v₁ , v₂) = (evalB c₁ v₁ , evalB c₂ v₂)
evalB (inv c) v = evalF c v

evalAF : Float → (t₁ ⇔ t₂) → ⟦ t₁ ⟧ → 𝒱 t₂
evalAB : Float → (t₁ ⇔ t₂) → ⟦ t₂ ⟧ → 𝒱 t₁
evalASF : Float → (t₁ ⇔ t₂) → 𝒱 t₁ → 𝒱 t₂
evalASB : Float → (t₁ ⇔ t₂) → 𝒱 t₂ → 𝒱 t₁

evalAF ϕ (arrZ c) v₁ = ∣ evalF c v₁ ⟩
evalAF ϕ (arrϕ c) v₁ = {!!}
evalAF ϕ unite⋆ (v₁ , tt) = ∣ v₁ ⟩
evalAF ϕ uniti⋆ v₁ = ∣ (v₁ , tt) ⟩
evalAF ϕ swap⋆ (v₁ , v₂) = ∣ (v₂ , v₁) ⟩
evalAF ϕ assocl⋆ (v₁ , (v₂ , v₃)) = ∣ ((v₁ , v₂) , v₃) ⟩ 
evalAF ϕ assocr⋆ ((v₁ , v₂) , v₃) = ∣ (v₁ , (v₂ , v₃)) ⟩ 
evalAF ϕ id⇔ v₁ = ∣ v₁ ⟩
evalAF ϕ (d₁ >>> d₂) v₁ = evalASF ϕ d₂ (evalAF ϕ d₁ v₁)
evalAF ϕ (d₁ *** d₂) (v₁ , v₂) = evalAF ϕ d₁ v₁ ⟨*⟩ evalAF ϕ d₂ v₂
evalAF ϕ (inv d) v₂ = evalAB ϕ d v₂
evalAF ϕ zero tt = ∣ F ⟩ 
evalAF ϕ assertZero F = ∣ tt ⟩
evalAF ϕ assertZero T = ●

evalAB ϕ (arrZ c) v₂ = ∣ evalB c v₂ ⟩
evalAB ϕ (arrϕ c) v₂ = {!!}
evalAB ϕ unite⋆ v₂ = ∣ (v₂ , tt) ⟩ 
evalAB ϕ uniti⋆ (v₂ , tt) = ∣ v₂ ⟩
evalAB ϕ swap⋆ (v₁ , v₂) = ∣ (v₂ , v₁) ⟩
evalAB ϕ assocl⋆ ((v₁ , v₂) , v₃) = ∣ (v₁ , (v₂ , v₃)) ⟩
evalAB ϕ assocr⋆ (v₁ , (v₂ , v₃)) = ∣ ((v₁ , v₂) , v₃) ⟩
evalAB ϕ id⇔ v₂ = ∣ v₂ ⟩
evalAB ϕ (d₁ >>> d₂) v₃ = evalASB ϕ d₁ (evalAB ϕ d₂ v₃)
evalAB ϕ (d₁ *** d₂) (v₃ , v₄) = evalAB ϕ d₁ v₃ ⟨*⟩ evalAB ϕ d₂ v₄
evalAB ϕ (inv d) v₁ = evalAF ϕ d v₁
evalAB ϕ zero F = ∣ tt ⟩
evalAB ϕ zero T = ●
evalAB ϕ assertZero tt = ∣ F ⟩

evalASF {t₁} {t₂} ϕ c k₁ = foldr _ _⟨+⟩_ ● (map (λ v₁ → k₁ v₁ *⟩ (evalAF ϕ c v₁)) (enum t₁))

evalASB {t₁} {t₂} ϕ c k₂ = foldr _ _⟨+⟩_ ● (map (λ v₂ → k₂ v₂ *⟩ (evalAB ϕ c v₂)) (enum t₂))


---------------------------------------------------------------------------
-- Examples

ctrl : (t ⟷ t) → (𝟚 ×ᵤ t) ⟷ (𝟚 ×ᵤ t)
ctrl c = dist ◎ (id⟷ ⊗ c ⊕ id⟷) ◎ factor

cx : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
cx = ctrl swap₊

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = ctrl cx

_ : evalF cx (F , F) ≡ (F , F)
_ = refl

_ : evalF cx (T , F) ≡ (T , T)
_ = refl

--

xZ xϕ : 𝟚 ⇔ 𝟚
xZ = arrZ swap₊
xϕ = arrϕ swap₊

one plus : I ⇔ 𝟚
one = zero >>> xZ
plus = zero >>> xϕ

assertOne : 𝟚 ⇔ I
assertOne = xZ >>> assertZero

cxZ cxϕ : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cxZ = arrZ cx
cxϕ = arrϕ cx

--e1 = show (evalAF 0.0 cxZ (F , F))
--e1 = show (evalAF 0.0 cxZ (F , T))
--e1 = show (evalAF 0.0 cxZ (T , F))
--e1 = show (evalAF 0.0 cxZ (T , T))

e2 = show (evalAF 0.0 zero tt)
-- (T , 0) ∷ (F , 1) ∷ []

ccxZ : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccxZ = arrZ ccx

copyZ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyZ = uniti⋆ >>> (id⇔ *** zero) >>> cxZ

e3 = show (evalAF 0.0 copyZ F)
e4 = show (evalAF 0.0 copyZ T)

copyϕ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyϕ = xϕ >>> copyZ >>> (xϕ *** xϕ)

-- Grover

repeat : ℕ → (t ⇔ t) → (t ⇔ t)
repeat 0 c = id⇔
repeat 1 c = c
repeat (suc n) c = c >>> repeat n c

amp : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
amp = xϕ *** xϕ *** xϕ >>>
      xZ *** xZ *** xZ >>>
      id⇔ *** id⇔ *** xϕ >>>
      ccxZ >>>
      id⇔ *** id⇔ *** xϕ >>>
      xZ *** xZ *** xZ >>>
      xϕ *** xϕ *** xϕ

grover3 : I ×ᵤ I ×ᵤ I ⇔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
grover3 =  plus *** plus *** plus >>> repeat 3 amp 

---------------------------------------------------------------------------
-- Equations

postulate

  -- Classical structure Z

  CSZ1 : copyZ >>> (id⇔ *** copyZ) ≡ copyZ >>> (copyZ *** id⇔) >>> assocr⋆
  CSZ2 : copyZ >>> swap⋆ ≡ copyZ
  CSZ3 : copyZ >>> (inv copyZ) ≡ id⇔
  CSZ4 : (copyZ *** id⇔) >>> (id⇔ *** copyZ) ≡ (id⇔ *** copyZ) >>> (copyZ *** id⇔)

  -- Classical structure ϕ

  CSϕ1 : copyZ >>> (id⇔ *** copyZ) ≡ copyZ >>> (copyZ *** id⇔) >>> assocr⋆
  CSϕ2 : copyϕ >>> swap⋆ ≡ copyϕ
  CSϕ3 : copyϕ >>> (inv copyϕ) ≡ id⇔
  CSϕ4 : (copyϕ *** id⇔) >>> (id⇔ *** copyϕ) ≡ (id⇔ *** copyϕ) >>> (copyϕ *** id⇔)

  -- Execution equations

  E1 : zero >>> assertZero ≡ id⇔
  E2 : ∀ (c : t ⟷ t) → (zero *** id⇔) >>> arrZ (ctrl c) ≡ zero *** id⇔ 
  E3 : ∀ (c : t ⟷ t) → (one *** id⇔) >>> arrZ (ctrl c) ≡ one *** arrZ c

  -- Complementarity

  C : (copyZ *** id⇔) >>> (id⇔ *** (inv copyϕ)) >>> (id⇔ *** copyϕ) >>> ((inv copyZ) *** id⇔) ≡ id⇔

---------------------------------------------------------------------------

