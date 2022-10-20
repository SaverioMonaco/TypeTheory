-- Exercise 1:
-- Look at it after LAB1

-----------------
---[ GENERAL ]---
-----------------
-- Set ℕ type, type of the natural elements:
data ℕ : Set where -- ℕ = \bN
  -- base element
  zero : ℕ
  -- function succ is a generic function from
  -- ℕ → ℕ, in our conception
  -- succ zero              → 1
  -- succ (succ zero)       → 2
  -- succ (succ (succ zero) → 3
  succ : ℕ → ℕ
  
-- For quicker testing
one   = succ zero
two   = succ one
three = succ two
four  = succ three
five  = succ four
six   = succ five
seven = succ six
eight = succ seven
nine  = succ eight
ten   = succ nine

------------------
---[ BOOLEANS ]---
------------------

-- Set Bool type:
-- this type only has two elements, true and false
-- starting from the data Bool, we can define functions such as
-- AND, ¬ and so on...
data Bool : Set where
  false : Bool
  true  : Bool

-- AND function:
_&&_ : Bool → Bool → Bool
-- false \w anything else is always false
false && b     = false
-- true and false is false
true  && false = false
-- only scenario where AND is true
true  && true  = true

---[ Exercise 1 ]---
-- Implement boolean "or":
-- "false || true" → "true"
-- "true  || true" → "true"
_||_ : Bool → Bool → Bool
-- true \w anything else is true
true  || b     = true
-- anything \w true is true
b     || true  = true
-- only scenario which OR is false
false || false = false

---[ Exercise 2 ]---
-- Implement a function "is-tautology?" which checks whether
-- a given input function is constantly true. For instance if f x = x
-- then " is-tautology f" should evaluate to "false"
-- INPUT:       function from Bool to Bool
-- OUTPUT:         |              Bool (tautology is either true or false)
--                 |              |       
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f false && f true

---[ Exercise 3 ]---
-- Implement a function "is-tautology?" which checks whether
-- a given input function of two arguments is constantly true.
-- For instance if f x y = true,then "is-tautology f" should be
-- evaluated to "true"
-- INPUT:       function from Bool×Bool to Bool
-- OUTPUT:         |                      Bool (tautology is either true or false)
--                 |                      |     
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (f true true && f true false) && (f false true && f false false)

-------------------------
---[ NATURAL NUMBERS ]---
-------------------------
-- Addition
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

---[ Exercise 4 ]---
-- Define the function "half" which divides its input by two.
-- For instance " half (succ (succ (succ (succ zero))))" should be "succ (succ zero)"
-- and "half (succ (succ (succ zero)))" should be "succ zero" (so we round down).
half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero -- half 1 = 0.5 → 0
half (succ (succ n)) = succ (half n)

---[ Exercise 5 ]---
-- Define (cut-off) subtraction. For instance "succ zero - succ zero" (1-1)
-- and "succ zero - succ (succ zero)" (1-2) should both be "zero".
_-_ : ℕ → ℕ → ℕ
zero - zero = zero
zero - n    = zero
n    - zero = n
succ a - succ b = a - b

---[ Exercise 6 ]---
-- Define multiplication and exponentiation.
_×_ : ℕ → ℕ → ℕ
a × zero = zero
zero × a = zero
succ a × b = (a × b) + b

_^_ : ℕ → ℕ → ℕ
a ^ zero = succ zero
a ^ succ b = (a ^ b) × a

---[ Exercise 7 ]---
-- Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" is true
-- while "eq? zero (succ zero)" is false
eq? : ℕ → ℕ → Bool
eq? zero     zero     = true
eq? zero     (succ b) = false
eq? (succ a) zero     = false
eq? (succ a) (succ b) = eq? a b

---[ Exercise 8 ]---
-- Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second. For instance
-- "≤ zero zero" is true while "≤ (succ zero) zero" is false
≤? : ℕ → ℕ → Bool
≤? zero zero = true
≤? zero (succ b) = true
≤? (succ a) zero = false
≤? (succ a) (succ b) = ≤? a b

---[ Exercise 9 ]---
-- Define a function "even?" which determines whether its input is even.
-- We build even? recursively from zero where each time it is true then false
-- even? zero = true
-- even? succ zero = false
-- even? succ (succ zero) = true
-- ...
¬_ : Bool → Bool
¬ true  = false
¬ false = true

even? : ℕ → Bool
even? zero = true
even? (succ n) = ¬ even? n
