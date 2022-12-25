{-# OPTIONS --without-K --exact-split --safe #-}

-- The signature of the types involved in Linear Algebra

module LinearAlgebraSig where

record LASig : Set₁ where
  field
    vec : Set → Set
    mat : Set → Set

  linop : Set → Set
  linop t = vec t → vec t
