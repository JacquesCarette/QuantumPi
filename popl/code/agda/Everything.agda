{-# OPTIONS --without-K --exact-split #-}
-- Can't use --safe as QPi isn't.

module Everything where

-- The point of this module is to have one place that makes sure everything
-- still does compile

-- It is also a convenient place to give a mapping between the paper and the code.

------------------------------------------------------------------------------------
-- Preparatory constructions

-- Set up the combinators that come with a commutative monoid. We'll end up
-- using this 3 times, so it is worth the abstraction.
open import CommMonoid

------------------------------------------------------------------------------------
-- Syntactic constructions

-- - Pi.Types gives the representation of types (as a data-structure)
-- - Pi.Language gives the representation of combinators (ditto, i.e. as syntax)
--     and some additional combinators (that could be in the syntax) expressible using swap
--     and the proof of reversibility of the syntax
-- - Pi.Equation gives some syntax for presenting Pi in equational style
-- - Pi.Terms gives some extra combinators (ctrl, cx, ccx)
-- - Pi.Equivalences gives a (syntactic) language of Pi term equivalences
-- - Pi.TermReasoning gives a syntax for doing equational reasoning over Pi terms
-- - Pi.DefinedEquiv defines some extra equivalences (on items from Pi.Terms)

-- Basically: the contents of 3.1 up to the semantics
open import Pi.Types
open import Pi.Language
open import Pi.Equational
open import Pi.Terms
open import Pi.Equivalences
open import Pi.TermReasoning
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
open import SPi.Terms
open import SPi.Complementarity

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
-- QPi: Syntax, semantics, execution, terms, measurement and reasoning

open import QPi.Syntax
open import QPi.Semantics
open import QPi.Execute
open import QPi.Terms
open import QPi.Measurement
open import QPi.Equivalences
open import Reasoning

------------------------------------------------------------------------------------
-- Not currently used, but maybe should be
open import IAmalgamation
------------------------------------------------------------------------------------
