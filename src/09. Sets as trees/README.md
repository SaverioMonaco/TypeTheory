## Sets as trees: introduction to one of the most important models of CZF and to the connection between set theory and type theory
-- SETS AS TREES

-- In predicative mathematics, we don't have the powerset operation.
-- P({a,b}) = { ∅, {a}, {b}, {a,b} }

-- Goal: define an Agda type V of sets accompanied by functions as
-- emptySet  : V             ∅
-- pair      : V → V → V     pair x y = {x,y}
-- singleton : V → V         singleton x = {x}
-- _∪_       : V → V → V
-- powerset  : V → V         we will fail to implement this function!

-- for instance, the type "eval '∃x. ∀y. ¬(y ∈ x)'" should be inhabited.

{-
  ∅:      *
       
  {x,y}:     *
            / \
           x   y

  {{x}, y, {a,b}}:       *
                       / | \
                      *  y  *
                      |    / \
                      x   a   b
-}

-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : ... : Setω : ...

data V : Set₁ where
  sup : {I : Set} → (I → V) → V   -- "sup" is short for "supremum"

-- Recall that this data empty is empty, even though it doesn't look like it on
-- first sight
data Weird : Set where
  succ : Weird → Weird

-- The definition of V also seems fishy in that regard: The constructor "sup"
-- returns a fresh element of V for every family of elements of V.
-- But in the beginning, there are no such families to start with! Or are they?
emptySet : V
emptySet = sup {⊥} empty-function
  where
  data ⊥ : Set where
  empty-function : ⊥ → V
  empty-function ()

-- pair x y = {x,y}
pair : V → V → V
pair x y = sup {𝟚} f
  where

  data 𝟚 : Set where
    left  : 𝟚
    right : 𝟚

  f : 𝟚 → V
  f left  = x
  f right = y

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Goal: define a value N : V which deserves the name "set of all natural numbers"
-- natural numbers in set theory:
-- 0 := ∅ = {}
-- 1 := { 0 } = { {} }
-- 2 := { 0, 1 } = { {}, {{}} }
-- 3 := { 0, 1, 2 } = { 0, 1, {0,1} } = { {}, {{}}, {{},{{}}} } = succ(2)
-- succ(n) := n ∪ {n}

-- next(x) = x ∪ {x}
{-
  x:     *                next x:  *
       / | \                     / | \     \
     ..........               ..........    x
-}
next : V → V
next x@(sup {I} f) = sup {J} g
  where

  data J : Set where
    old : I → J
    new : J

  g : J → V
  g (old i) = f i
  g new     = x

fromℕ : ℕ → V
fromℕ zero     = emptySet
fromℕ (succ n) = next (fromℕ n)

-- N as a tree:    *
--              / /  \  \
--             0  1   2  3  4 ...
N : V
N = sup {ℕ} fromℕ

