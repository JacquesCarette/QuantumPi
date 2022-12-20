
{-# OPTIONS --without-K --exact-split --safe #-}

module ArrowsOverAmalg where

open import Pi.Types using (U; I; _+ᵤ_; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; _◎_; id⟷;
  swap⋆; swap₊; assocl⋆; assocr⋆; unite⋆l; uniti⋆l; !⟷; _⊗_)
open import Amalgamation using (module Build)

open Build (_⟷_) using (TList; nil; cons₁; cons₂)

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
arr₁ : t₁ ⟷ t₂ -> TList t₁ t₂
arr₁ c = cons₁ c nil
arr₂ : t₁ ⟷ t₂ -> TList t₁ t₂
arr₂ c = cons₂ c nil

-- We can then lift a lot of things to this level:
id : TList t t
id = arr₁ id⟷

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
first (cons₁ x y) = cons₁ (x ⊗ id⟷) (first y)
first (cons₂ x y) = cons₂ (x ⊗ id⟷) (first y)

_>>>_ : {t₁ t₂ t₃ : U} → TList t₁ t₂ → TList t₂ t₃ → TList t₁ t₃
nil         >>> z = z
(cons₁ x y) >>> z = cons₁ x (y >>> z)
(cons₂ x y) >>> z = cons₂ x (y >>> z)

-- Second, as usual, is definable using the above, but that is inefficient.
-- Use a direct definition instead
second : TList t₁ t₂ → TList (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
-- second c = swap× >>> first c >>> swap×
second nil = nil
second (cons₁ x c) = cons₁ (id⟷ ⊗ x) (second c)
second (cons₂ x c) = cons₂ (id⟷ ⊗ x) (second c)

-- Warning: this is quadratic!
inv : {t₁ t₂ : U} → TList t₁ t₂ → TList t₂ t₁
inv nil          = nil
inv (cons₁ x xs) = inv xs >>> (cons₁ (!⟷ x) nil)
inv (cons₂ x xs) = inv xs >>> (cons₂ (!⟷ x) nil)

-- This is slow?  Implement directly instead
_***_ : TList t₁ t₂ → TList t₃ t₄ → TList (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
-- xs *** ys = first xs >>> second ys
nil *** nil = nil
nil *** cons₁ x ys = cons₁ (id⟷ ⊗ x) (nil *** ys)
nil *** cons₂ x ys = cons₂ (id⟷ ⊗ x) (nil *** ys)
cons₁ x xs *** nil = cons₁ (x ⊗ id⟷) (xs *** nil)
cons₁ x xs *** cons₁ y ys = cons₁ (x ⊗ y) (xs *** ys)
cons₁ x xs *** cons₂ y ys = cons₁ (x ⊗ id⟷) (cons₂ (id⟷ ⊗ y) (xs *** ys))
cons₂ x xs *** nil = cons₂ (x ⊗ id⟷) (xs *** nil)
cons₂ x xs *** cons₁ y ys = cons₂ (x ⊗ id⟷) (cons₂ (id⟷ ⊗ y) (xs *** ys))
cons₂ x xs *** cons₂ y ys = cons₂ (x ⊗ y) (xs *** ys)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
