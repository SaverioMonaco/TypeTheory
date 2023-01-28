-- Here we define the Bool type, which is a type
-- that has 2 elements in it:
-- - true
-- - false
-- Despite the name of he elements, this type is
-- alone quite generic and far from our conception
-- of the booleans we know.
-- After adding the rules about booleans (AND, OR, ...)
-- they can be treated as booleans
data Bool : Set where
  true  : Bool
  false : Bool

----------------------------
-- >> EXERCISE 1:
-- Implement AND function
----------------------------
_&&_ : Bool → Bool → Bool
-- We just fill all possible cases: (4)
true  && b  = b     -- true AND b is true iff b is true
false && b  = false -- false AND anything else is false

----------------------------
-- >> EXERCISE 2:
-- Implement OR function
----------------------------
_||_ : Bool → Bool → Bool
-- Just as the AND case, we cover all scenarios
true  || b = true
false || b = b

----------------------------
-- >> EXERCISE 3:
-- Implement a function "is-tautology?" which checks whether
-- a given input function is constantly true. For instance if f x = x
-- then " is-tautology f" should evaluate to "false"
----------------------------
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f false && f true
-- Given the function f, if we evaluate f true and f false
-- and both results are true, then the function should be
-- evaluated to true

----------------------------
-- >> EXERCISE 4:
-- Implement a function "is-tautology?" which checks whether
-- a given input function of two arguments is constantly true.
-- For instance if f x y = true,then "is-tautology f" should be
-- evaluated to "true"
---------------------------
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (f true true && f false false) && (f false true && f true false)

-- What are those "tautologies" actually?
-- If we consider any function f that takes a Bool as argument (for is-tautology₁) or
-- any function g that takes two Bools as arguments (for is-tautology₂)
-- we can verify if that given function gives always true.
-- You can imagine NOT as a function, but of course is not a tautology since
-- NOT true = false
-- Or you can even imagine AND or OR as functions (with two arguments), those two
-- are not tautologies neither since they can give false as a result.

-- This is of course a tautology
f₁ : Bool → Bool
f₁ a = true

-- The negation function is not a tautology
¬ : Bool → Bool
¬ true  = false
¬ false = true

-- [ Ctrl+C Ctrl+N ]
-- >> is-tautology₁ f₁
-- true
-- >> is-tautology₁ ¬
-- false

-- Now we move on to functions with two arguments:

-- This is a tautology, it always gives true regardless of the two
-- boolean arguments
g₁ : Bool → Bool → Bool
g₁ a b = true

-- AND function, this is not a tautology
and : Bool → Bool → Bool
and true b  = b
and false b = false

-- [ Ctrl+C Ctrl+N ]
-- >> is-tautology₂ g₁
-- true
-- >> is-tautology₂ and
-- false

data Comparison : Set where
  greater : Comparison
  less    : Comparison
  equal   : Comparison

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_<_ : (a : ℕ) → (b : ℕ) → Bool
zero < zero     = false
zero < (succ b) = true
(succ a) < zero = false
(succ a) < (succ b) = a < b

one = succ zero
two = succ one
three = succ two
four = succ three
five = succ four

compare : ℕ → ℕ → Comparison
compare x y with x < y | y < x
...            | true  | _     = less
...            | _     | true  = greater
...            | false | false = equal


