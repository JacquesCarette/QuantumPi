{-# OPTIONS --without-K --exact-split --safe #-}

module ArrowsOverAmalg where

open import PiSyntax using (U; I; _+ᵤ_; _×ᵤ_; _⟷₁_; _◎_; id⟷₁;
  swap⋆; swap₊; assocl⋆; assocr⋆; unite⋆l; uniti⋆l; !⟷₁; _⊗_; ctrl; 𝟚)
open import Amalgamation using (TList; nil; cons₁; cons₂)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-------------------------------------------------------------------------------------
-- Form "Arrows" over a pairing of Pi languages.
infixr 10 _>>>_

-- We use ₁ and ₂ instead of subscripts Z and H to be
-- 1) more generic and 2) avoid the unpleasant issue that
-- Agda doesn't actually define those subscripts.
arr₁ : t₁ ⟷₁ t₂ -> TList t₁ t₂
arr₁ c = cons₁ c nil
arr₂ : t₁ ⟷₁ t₂ -> TList t₁ t₂
arr₂ c = cons₂ c nil

-- We can then lift a lot of things to this level:
idzh : TList t t
idzh = arr₁ id⟷₁

swap× : TList (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
swap× = arr₁ swap⋆
assocl× : TList  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
assocl× = arr₁ assocl⋆
assocr× : TList  ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
assocr× = arr₁ assocr⋆
unite*l : TList (I ×ᵤ t) t
unite*l = arr₁ unite⋆l
uniti*l : TList t (I ×ᵤ t)
uniti*l = arr₁ uniti⋆l
unite* : TList (t ×ᵤ I) t
unite* = arr₁ (swap⋆ ◎ unite⋆l)
uniti* : TList t (t ×ᵤ I)
uniti* = arr₁ (uniti⋆l ◎ swap⋆)

-- And we can make Arrows out of this too:
first : {t₁ t₂ t₃ : U} → TList t₁ t₂ → TList (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
first nil = nil
first (cons₁ x y) = cons₁ (x ⊗ id⟷₁) (first y)
first (cons₂ x y) = cons₂ (x ⊗ id⟷₁) (first y)

_>>>_ : {t₁ t₂ t₃ : U} → TList t₁ t₂ → TList t₂ t₃ → TList t₁ t₃
nil         >>> z = z
(cons₁ x y) >>> z = cons₁ x (y >>> z)
(cons₂ x y) >>> z = cons₂ x (y >>> z)

-- Second, as usual, is definable using the above, but that is inefficient.
-- Use a direct definition instead
second : TList t₁ t₂ → TList (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
-- second c = swap× >>> first c >>> swap×
second nil = nil
second (cons₁ x c) = cons₁ (id⟷₁ ⊗ x) (second c)
second (cons₂ x c) = cons₂ (id⟷₁ ⊗ x) (second c)

-- Warning: this is quadratic!
inv : {t₁ t₂ : U} → TList t₁ t₂ → TList t₂ t₁
inv nil          = nil
inv (cons₁ x xs) = inv xs >>> (cons₁ (!⟷₁ x) nil)
inv (cons₂ x xs) = inv xs >>> (cons₂ (!⟷₁ x) nil)

-- This is slow?  Implement directly instead
_***_ : TList t₁ t₂ → TList t₃ t₄ → TList (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
-- xs *** ys = first xs >>> second ys
nil *** nil = nil
nil *** cons₁ x ys = cons₁ (id⟷₁ ⊗ x) (nil *** ys)
nil *** cons₂ x ys = cons₂ (id⟷₁ ⊗ x) (nil *** ys)
cons₁ x xs *** nil = cons₁ (x ⊗ id⟷₁) (xs *** nil)
cons₁ x xs *** cons₁ x₁ ys = cons₁ (x ⊗ x₁) (xs *** ys)
-- Note how this makes the list longer.
cons₁ x xs *** cons₂ x₁ ys = cons₁ (x ⊗ id⟷₁) (cons₂ (id⟷₁ ⊗ x₁) (xs *** ys))
cons₂ x xs *** nil = cons₂ (x ⊗ id⟷₁) (xs *** nil)
cons₂ x xs *** cons₁ x₁ ys = cons₂ (x ⊗ id⟷₁) (cons₂ (id⟷₁ ⊗ x₁) (xs *** ys))
cons₂ x xs *** cons₂ x₁ ys = cons₂ (x ⊗ x₁) (xs *** ys)

-- Add some definitions from 5.1
X : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
X = arr₁ swap₊
CX : TList (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CX = arr₁ (ctrl swap₊)
CCX : TList (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
CCX = arr₁ (ctrl (ctrl swap₊))
H : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
H = arr₂ swap₊
Z : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
Z = H >>> X >>> H
CZ : TList (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CZ = idzh *** H >>> CX >>> idzh *** H
