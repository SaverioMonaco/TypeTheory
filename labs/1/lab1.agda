-- This delaration creates a new type, called "Bool".
-- This type has exactly two values: false and true.
data Bool : Set where
  false : Bool
  true  : Bool

-- Sets can also be broader...
data Color : Set where
  red   : Color
  green : Color
  blue  : Color
  pink  : Color

-- We can also create Empty types, no clue why it is useful...
data Empty : Set where

-- First function, let us create the identity function
-- specifically from Bool to Bool (the type that we defined)
-- (n.b. to do the arrow just pretend you are using LaTeX)
--  → = \to
id : Bool → Bool
id x = x -- take x as input and return x, duh

-- Programming in ADGA you might want to write some template
-- and fill the details later, if you write something like this
-- neg : Bool → Bool
-- neg x = ?
--
-- You just have a sort of hole there, that is not well defined
-- but the program will just run
-- if you then write Ctrl-C and Ctrl-C it will autofill for you
-- (type x)
-- to remove a hole fill it then type Ctrl-C and Ctrl-Space
neg : Bool → Bool
neg false = true
neg true =  false

-- Defyning a constant
ex : Bool
ex = neg false

-- You can check if ex is true by typing
-- Ctrl-C and Ctrl-V (or Ctrl-C and Ctrl-N) and then in the prompt ex

-- input: 1     | 2     | and
--        true  | true  | true
--        true  | false | false
--        false | true  | false
--        false | false | false
and : Bool → Bool → Bool -- takes two Bool and returns a Bool
and false y     = false
and true  false = false
and true  true  = true

ex2 : Bool
ex2 = and false true

data exℕ : Set where -- \bN
  exzero  : exℕ
  exone   : exℕ
  extwo   : exℕ
  exthree : exℕ
  exfour  : exℕ
-- ...
-- We cannot define them all, they are infinite!

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ -- "succ" is short for "successor"
-- The elements (values, inhabitants) of ℕ are:
-- zero
-- succ zero
-- succ (succ zero)
-- succ (succ (succ zero))
-- ...

one : ℕ
one = succ zero

-- add2 of 30 should be 32
add2 : ℕ → ℕ
add2 n = succ (succ n)

-- "pred one" should be zero.
-- "pred (succ (succ zero))" should be one.
-- "pred zero" should be zero. let us not go into negative numbers for now.
pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

-- ADGA supports so-called "dependent types": types which depend on values.
-- The prototypical example for a dependent type is the type of vectors of lenght n.
-- In C we have the type int[] of arrays of integers.
-- ex zero-vector : (n : ℕ) → Vector n

-- Let us define the addition function
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b =  succ (a + b)
-- example computation
-- two + b               = 
-- succ (succ zero) + b  =
-- succ (succ zero + b)  =
-- succ (succ (zero + b) =
-- succ (succ b)

-- "double one" should be succ (succ zero)
-- "double two" should be four.
double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

