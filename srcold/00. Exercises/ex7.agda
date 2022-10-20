{-# OPTIONS --allow-unsolved-metas #-}
-- AGDA IN PADOVA 2022
-- Exercise sheet 9

-- CONSTRUCTIVE ZERMELO--FRAENKEL in AGDA

open import Data.Nat


-- THE BASICS OF "SETS AS TREES"

data V : Set₁ where
  sup : {I : Set} → (I → V) → V

emptySet : V
emptySet = sup {⊥} (λ ())
  where
  data ⊥ : Set where
-- as a tree: *

-- pair x y = "{x,y}" (a set which has typically two elements)
pair : V → V → V
pair x y = sup {𝟚} λ { left → x ; right → y }
  where
  data 𝟚 : Set where
    left  : 𝟚
    right : 𝟚
-- as tree:        *
--                / \
--               x   y

-- singleton x = "{x}" (a set which contains precisely one element)
singleton : V → V
-- singleton x = pair x x
singleton x = sup {𝟙} λ { * → x }
  where
  data 𝟙 : Set where
    * : 𝟙
-- as a tree:    *
--               |
--               x

-- natural numbers in set theory:
-- 0 := ∅ = {}
-- 1 := { 0 } = { {} }
-- 2 := { 0, 1 } = { {}, {{}} }
-- 3 := { 0, 1, 2 } = { {}, {{}}, {{},{{}}} }
-- succ(n) = n ∪ {n}

-- EXERCISE: Implement union of sets.
_∪_ : V → V → V
_∪_ = {!!}

-- next(x) = x ∪ {x}
next : V → V
next x = x ∪ singleton x

fromℕ : ℕ → V
fromℕ zero    = emptySet
fromℕ (suc n) = next (fromℕ n)

N : V
N = sup {ℕ} fromℕ

-- EXERCISE: Define the "big union" operator,
-- i.e. union X = { x | ∃M. x ∈ M ∧ M ∈ X }.
union : V → V
union = {!!}

-- EXERCISE: Try, but fail, to define the powerset operator.
powerset : V → V
powerset = {!!}

-- EXERCISE: Define the Kuratowski pairing operation, ⟨ x , y ⟩ = { {x}, {x,y} }.
⟨_,_⟩ : V → V → V
⟨ x , y ⟩ = {!!}

-- EXERCISE: Define a relation _≈_ on V expressing that two trees denote the
-- same set. For instance, while "pair x x" is not propositionally equal to
-- "singleton x", they should be related by _≈_. See also the next exercise.

-- EXERCISE: Define a relation _∈_ on V expressing that the first set is an
-- element of the second. There are several ways to solve this exercise and
-- the preceding one; one possible solution employs mutual recursion,
-- another one doesn't.


-- EXPLORING THE SET-THEORETIC UNIVERSE V

-- EXERCISE: Verify the "axiom of extensionality": Sets x and y which have
-- the same elements in the sense that any set a is an element of x iff
-- it is an element of y are equal in the sense that they are related by _≈_.
-- ext : (x y : V) → ((a : V) → a ∈ x → a ∈ y) → ((a : V) → a ∈ y → a ∈ x) → x ≈ y
-- ext = ?

-- EXERCISE: Verify that ⟨ x , y ⟩ ≈ ⟨ x' , y' ⟩ if and only if x ≈ x'
-- and y ≈ y'.

-- EXERCISE: Add "{-# OPTIONS --type-in-type #-}" to the top of this development.
-- This option collapses Agda's universe hierarchy, yielding an inconsistent system.
-- Now define the Russell set of all those sets which do not contain themselves,
-- and obtain a contradiction.

-- EXERCISE: Define a predicate "IsTransitive" expressing that a set is transitive.
-- (Recall that a set x is transitive iff whenever a ∈ b ∈ x, then already a ∈ x.)

-- EXERCISE: Define a predicate "IsOrdinal" expressing that a set is an "ordinal number",
-- meaning a set which is transitive and whose elements are all transitive.

-- EXERCISE: Show that N is an ordinal number.


-- ON CHOICE

-- EXERCISE: Show that V verifies the axiom of dependent choice.


-- SET-THEORETIC LANGUAGE

-- EXERCISE: Define a datatype (or family of datatypes, parameterized by the context)
-- of set-theoretic formulas such as:
--
--   ∃x. ∀y. (x ∈ y → ⊥)
--   ∀x. ∀y. ∃z. (x ∈ z ∧ y ∈ z)

-- EXERCISE: Define an evaluation function mapping such formulas to the type of their witnesses.
-- For instance, the type "eval (EXISTS (FORALL (NOT (var vzero ∈ var (vsucc vzero)))))"
-- (or with a similar notation) should be inhabited, as there indeed is an empty set.

