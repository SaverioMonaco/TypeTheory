data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Addition
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)

------------------------------------------
-- >> EXERCISE 1
-- Define the function "half" which divides its input in two.
-- >> half (succ (succ (succ (succ zero)))) = succ (succ zero)
-- >> half (succ (succ (succ zero))) = succ zero (round down)
------------------------------------------
half : ℕ → ℕ
half zero = zero
half (succ zero) = succ zero
half (succ a) = succ (half a)

------------------------------------------
-- >> EXERCISE 2
-- Define (cut-off) subtraction. For instance "succ zero - succ zero" (1-1)
-- and "succ zero - succ (succ zero)" (1-2) should both be "zero".
------------------------------------------
_-_ : ℕ → ℕ → ℕ
zero - zero = zero
zero - b    = zero
a - zero    = a
succ a - succ b  = a - b

------------------------------------------
-- >> EXERCISE 3
-- Define multiplication and exponentiation.
------------------------------------------
_×_ : ℕ → ℕ → ℕ
zero × b = zero
a × zero = zero
a × (succ zero) = a
(succ zero) × b = b
(succ a) × b = (a × b) + b

_^_ : ℕ → ℕ → ℕ
a ^ zero = succ zero
a ^ succ b = (a ^ b) × a

------------------------------------------
-- >> EXERCISE 4
-- Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" is true
-- while "eq? zero (succ zero)" is false
------------------------------------------

-- First we need to define true and false
data Bool : Set where
  true  : Bool
  false : Bool

eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (succ b) = false
eq? (succ a) zero = false
eq? (succ a) (succ b) = eq? a b

------------------------------------------
-- >> EXERCISE 5
-- Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second. For instance
-- "≤ zero zero" is true while "≤ (succ zero) zero" is false
------------------------------------------
≤? : ℕ → ℕ → Bool
≤? zero zero = true
≤? zero (succ b) = true
≤? (succ a) zero = false
≤? (succ a) (succ b) = ≤? a b

------------------------------------------
-- >> EXERCISE 6
-- Define a function "even?" which determines whether its input is even.
-- We build even? recursively from zero where each time it is true then false
-- even? zero = true
-- even? succ zero = false
-- even? succ (succ zero) = true
------------------------------------------
¬ : Bool → Bool
¬ true  = false
¬ false = true

even? : ℕ → Bool
even? zero = true
even? (succ a) = ¬ (even? a)
