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
true || b = true
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
