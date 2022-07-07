{-# OPTIONS --without-K --exact-split --safe #-}

-- The point of this module is to have one place that makes sure everything
-- still does compile

-- It is also a convenient place to give a mapping between the paper and the code.

module Everything where

-- PiSyntax gives:
-- - the representation of types (as a data-structure)
-- - the representation of combinators (ditto, i.e. as syntax)
-- - some reasoning combinators
-- - (currently) some extra combinators for Simon's problem
-- - some additional combinators (that could be in the syntax) expressible using swap
-- - proof of reversibility of the syntax
--
-- Basically: the contents of 3.1 up to the semantics
open import PiSyntax
-- PiTagless gives a representation independent version of PiSyntax.
-- So rather than providing different evaluators for the syntax, one can instead provide
-- instances (as records).
-- The reversibility constraint is packed separately, as some instances are only
-- "externally" reversible.
open import PiTagless
-- PiBij gives part of the semantics (Figure 2) of Pi in Rig Groupoids (i.e. the
-- initial instance, in FinSet and Bijections).
-- TODO: actually interpret it?
open import PiBij
-- Unitary implements (most of?) Definition 6 of Section 4.2
open import Unitary
-- PiZ give an instance of Pi where the "values" are Real-valued vectors indexed by
--  [an enumeration of] a type (t : U).
-- The combinators are then representation of linear actions from vectors to vectors,
--  aka matrices.
open import PiZ
-- PiH gives an instance of Pi where the "values" are again Real-valued vectors indexed by
--  [an enumeration of] a type (t : U). But this time the action is conjugated by R, i.e.
-- "rotated". The result is still matrices, but in a different basis.
open import PiH
open import PiExamples
open import GenericList
open import ArrowsOverPair
open import StatesAndEffects
open import Instances
open import Simon
open import Tests
