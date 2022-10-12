-- AGDA IN PADOVA 2022
-- Exercise sheet 1


--------------------
----[ BOOLEANS ]----
--------------------

data Bool : Set where
  false : Bool
  true  : Bool

_&&_ : Bool → Bool → Bool
false && b     = false
true  && false = false
true  && true  = true

-- EXERCISE: Implement boolean "or".
-- "false || true" should evaluate to "true".
-- "true  || true" should evaluate to "true".
_||_ : Bool → Bool → Bool
false || b = b
true  || b = true

_||'_ : Bool → Bool → Bool
false ||' false = false
false ||' true  = true
true  ||' b     = true

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁ f" should evaluate to "false".
constantly-true : Bool → Bool
constantly-true x = true

constantly-true' : Bool → Bool
constantly-true' false = true
constantly-true' true  = true

is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f false && f true
-- does not work: is-tautology₁ f = f ≡ constantly-true
-- in math: is-tautology₁(f) = f(false) && f(true)

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = {!!}

-- COMMENT:
-- Function extensionality means: "If f x = g x for all x, then f = g."

---------------------------
----[ NATURAL NUMBERS ]----
---------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- EXERCISE: Define the function "half" which divides its input by two.
-- For instance "half (succ (succ (succ (succ zero))))" should be "succ (succ zero)"
-- and "half (succ (succ (succ zero)))" should be "succ zero" (so we round down).
half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero   -- in math: half(1) = 0.5 = 0 (rounded down)
half (succ (succ n)) = succ (half n)
-- (1+n)/2 = 0.5 + n/2
-- (1+1+n)/2 = 1 + n/2

-- EXERCISE: Define (cut-off) subtraction. For instance "succ zero - succ zero"
-- and "succ zero - succ (succ zero)" should both be "zero".
_-_ : ℕ → ℕ → ℕ
a - b = {!!}

-- EXERCISE: Define multiplication and exponentiation.

-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
eq? : ℕ → ℕ → Bool
eq? a b = {!!}

-- EXERCISE: Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second. For instance, "≤?
-- zero zero" should evaluate to "true" while "≤? (succ zero) zero"
-- should evaluate to "false".
≤? : ℕ → ℕ → Bool
≤? a b = {!!}

-- EXERCISE: Define a function "even?" which determines whether its input is even.
-- For instance, "even? zero" and "even? (succ (succ zero))" should both evaluate to "true",
-- while "even? (succ zero)" should evaluate to "false".
even? : ℕ → Bool
even? zero            = true
even? (succ zero)     = false
even? (succ (succ n)) = even? n

¬_ : Bool → Bool
¬ false = true
¬ true  = false

even?' : ℕ → Bool
even?' zero     = true
even?' (succ n) = ¬ (even?' n)

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird
-- There are no values of the type Weird!

data ∅ : Set where  -- \emptyset
-- this is the manifestly empty type.

empty-function : ∅ → ℕ
empty-function ()

question : ℕ → ∅
question n = {!!}  -- this hole is unfillable

prior-question : ∅ → ∅
prior-question x = x

prior-question' : ∅ → ∅
prior-question' ()

bonus-question : Weird → ∅
bonus-question (foo x) = bonus-question x


-- on to dependent types!

-- The type "list of integers" depends on the type of integers, but
-- this is still a type (and not a value), and hence the type "list of integers"
-- would not usually be called a "dependent type".

-- The type "vectors of length n" depends on the number n (which is a value, not a type),
-- and hence the type "vectors of length n" would be called a "dependent type".

data Vector : ℕ → Set where
  []  : Vector zero
  _∷_ : {n : ℕ} → Bool → Vector n → Vector (succ n)

example-vector : Vector (succ (succ (succ zero)))
example-vector = false ∷ (true ∷ (true ∷ []))  -- [false,true,true]

false-vector : {n : ℕ} → Vector n
false-vector {zero}   = []
false-vector {succ n} = false ∷ false-vector

ex : Vector (succ (succ (succ zero)))
ex = false-vector

-- "false-vector (succ (succ (succ zero)))" should evaluate to "false ∷ (false ∷ (false ∷ [])))"

data Vector' (A : Set) : ℕ → Set where
  []  : Vector' A zero
  _∷_ : {n : ℕ} → A → Vector' A n → Vector' A (succ n)
-- for instance, Vector' Bool (succ (succ zero)) is the type of boolean vectors of length 2.
-- for instance, Vector' ℕ    (succ (succ zero)) is the type of vectors of length 2 whose entries are natural numbers.

data Vector'' : Set → ℕ → Set where
  []  : {A : Set} → Vector'' A zero
  _∷_ : {A : Set} {n : ℕ} → A → Vector'' A n → Vector'' A (succ n)
  -- ♥   : Vector'' Bool (succ (succ zero))

-- for instance, "map f (x ∷ (y ∷ (z ∷ [])))" should evaluate to "f x ∷ (f y ∷ (f z ∷ []))".
-- map : {A : Set} → {B : Set} → {n : ℕ} → (A → B) → Vector' A n → Vector' B n
map : {A B : Set} {n : ℕ} → (A → B) → Vector' A n → Vector' B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Set is the type of all small types; it's the "universe".
-- for instance, ℕ : Set
-- for instance, Bool : Set
-- for instance, ∅ : Set

-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : Set₄ : ...

-- Agda has a mode to switch it as follows: zero : ℕ : Set : Set : Set : Set : Set : ...
-- The resulting system will be inconsistent (be able to prove 1 = 0).

-- ℕ is actually a value of type Set. :-)
