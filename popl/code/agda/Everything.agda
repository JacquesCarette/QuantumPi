{-# OPTIONS --without-K --exact-split #-}
-- Can't use --safe as QPi isn't.

module Everything where

-- The point of this module is to have one place that makes sure everything
-- still does compile

-- It is also a convenient place to give a mapping between the paper and the code.

------------------------------------------------------------------------------------
-- Syntactic constructions

-- - Pi.Types gives the representation of types (as a data-structure)
-- - Pi.Language gives the representation of combinators (ditto, i.e. as syntax)
--     and some additional combinators (that could be in the syntax) expressible using swap
--     and the proof of reversibility of the syntax
-- - Pi.Reasoning gives some reasoning combinators
-- - Pi.Terms gives some extra combinators (ctrl, cx, ccx)
-- - Pi.Equivalences gives a (syntactic) language of Pi term equivalences
-- - Pi.DefinedEquiv defines some extra equivalences (on items from Pi.Terms)

-- Basically: the contents of 3.1 up to the semantics
open import Pi.Types
open import Pi.Language
open import Pi.Reasoning
open import Pi.Terms
open import Pi.Equivalences
open import Pi.DefinedEquiv

-- PiTagless gives a representation independent version of PiSyntax.
-- So rather than providing different evaluators for the syntax, one can instead provide
-- instances (as records).
-- The reversibility constraint is packed separately, as some instances are only
-- "externally" reversible.
open import PiTagless

-- Syntactic arrow constructions parameterized by evaluators in the tagless style
open import Amalgamation
open import ArrowsOverAmalg
open import Arrows.Terms -- some examples
open import Ancillae -- Defined PiSyntax sub-language for ancillaes
open import StatesAndEffects

-- Example written in the syntax (before any explicit rotation or unitaries)
open import Simon

------------------------------------------------------------------------------------
-- Utilities useful in various places below
open import FloatUtils

------------------------------------------------------------------------------------
-- Two semantics for Pi rotated with respect to each other 

-- Unitary implements (most of?) Definition 6 of Section 4.2
open import Unitary

-- Interpretation over arbitrary basis of Unitary
open import GenericPi

-- PiZ give an instance of Pi where the "values" are Real-valued vectors indexed by
--  [an enumeration of] a type (t : U).
-- The combinators are then representation of linear actions from vectors to vectors,
--  aka matrices.
open import PiZ
-- PiH gives an instance of Pi where the "values" are again Real-valued vectors indexed by
--  [an enumeration of] a type (t : U). But this time the action is conjugated by R, i.e.
-- "rotated". The result is still matrices, but in a different basis.
open import PiH

------------------------------------------------------------------------------------
-- Instantiate generic semantics for full language

open import Instances

------------------------------------------------------------------------------------
-- Examples

open import Tests
open import TestsSlow

------------------------------------------------------------------------------------
-- QPi and reasoning

open import QPi.Syntax
open import QPi
open import Reasoning

------------------------------------------------------------------------------------
-- Not currently used, but maybe should be
open import IAmalgamation
------------------------------------------------------------------------------------
