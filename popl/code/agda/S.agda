{-# OPTIONS --without-K --exact-split #-}

open import Relation.Binary.PropositionalEquality using (_≡_)

module S where

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
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔(t₁ ×ᵤ t₂) ×ᵤ t₃
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
-- Examples

xZ xϕ : 𝟚 ⇔ 𝟚
xZ = arrZ swap₊
xϕ = arrϕ swap₊

one : I ⇔ 𝟚
one = zero >>> xZ

assertOne : 𝟚 ⇔ I
assertOne = xZ >>> assertZero

ctrl : (t ⟷ t) → (𝟚 ×ᵤ t) ⟷ (𝟚 ×ᵤ t)
ctrl c = dist ◎ (id⟷ ⊗ c ⊕ id⟷) ◎ factor

cx : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
cx = ctrl swap₊

cxZ cxϕ : 𝟚 ×ᵤ 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
cxZ = arrZ cx
cxϕ = arrϕ cx

copyZ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyZ = uniti⋆ >>> (id⇔ *** zero) >>> cxZ

copyϕ : 𝟚 ⇔ 𝟚 ×ᵤ 𝟚
copyϕ = xϕ >>> copyZ >>> (xϕ *** xϕ)


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

