-- AGDA IN PADOVA 2022
-- Exercise sheet 3
-- Look at it after LAB5

-- Known Sets and functions:
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
----------------------------

------------------------
----[ EVEN AND ODD ]----
------------------------

-- Even n is the type of witnesses that n is even.
data Even : ℕ → Set where
  base-even : Even zero -- base element
  -- if we know n is Even, succ (succ n) is Even
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero) -- base element
  -- if we know n is Odd, succ (succ n) is Odd
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

---[ EXERCISE 1 ]---
-- Show that the sum of even numbers is even
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
-- 1. type lemma-succ-even = ?, then Ctrl-C Ctrl-L to compile
--    creating the hole { }0
-- 2. type lemma-succ-even p q = {}0, then Ctrl-C Ctrl-,
--    to get hold of the situation:
-- Output:
--         Goal: Even (a + b)
--        ————————————————————————————————————————————————————————————
--         q : Even b
--         p : Even a
--         b : ℕ   (not in scope)
--         a : ℕ   (not in scope)
-- 3. Perform "case-split" in p with Ctrl-C Ctrl-C (>> p) after clicking
--    on the { }0
lemma-sum-even base-even q = q -- trivial, we already have directly the witness
                               -- that base-even + q is even since base-even + q is q
-- (step-even p) + q = step (p + q) and we can prove p + q is even by recursion
-- since every step-even of the recursion is even we get the proof
lemma-sum-even (step-even p) q = step-even (lemma-sum-even p q)

---[ EXERCISE 2 ]---
-- Show that the successor of an even number is odd and vice versa
lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
-- lemma-succ-even = { }0 and Ctrl-C Ctrl-,
-- Goal: Even a → Odd (succ a)
--      ——————————————————————————
--       a : ℕ   (not in scope)
-- Case split on lemma-succ-even p = { }0 (>> p)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even p) = step-odd (lemma-succ-even p)

-- Just as the one above
lemma-succ-odd : {b : ℕ} → Odd b → Even (succ b)
-- the proof of the successor of base-odd (1) being even
-- is the step-even of base-even (0→2)
lemma-succ-odd base-odd = step-even (base-even)
lemma-succ-odd (step-odd b) = step-even (lemma-succ-odd b)

---[ EXERCISE 3 ]---
-- Show that the sum of odd numbers is even
-- Goal: Odd a → Odd b → Even (a + b)
--      ————————————————————————————————
--       b : ℕ   (not in scope)
--       a : ℕ   (not in scope)
lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd base-odd q = lemma-succ-odd q
lemma-sum-odd (step-odd p) q = step-even (lemma-sum-odd p q)

---[ EXERCISE 4 ]---
-- Show that the sum of an odd number with an even number is odd
-- Goal: Odd a → Even b → Odd (a + b)
--      —————————————————————————————————————
--       b : ℕ   (not in scope)
--       a : ℕ   (not in scope)
lemma-sum-mixed : {a b : ℕ} → Odd a → Even b → Odd (a + b)
lemma-sum-mixed base-odd e = lemma-succ-even e
lemma-sum-mixed (step-odd o) e = step-odd (lemma-sum-mixed o e)

---[ EXERCISE 5 ]---
-- Show that every number is even or odd.
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- For instance, if x : A, then left x : A ⊎ B.

-- Goal: Even a ⊎ Odd a
--      ——————————————————
--       a : ℕ
lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
-- if you want to demonstrate that (succ a) is either
-- even (left) or odd (right)
-- assume lemma-even-odd to be demonstrated with these
-- two scenarios:
lemma-even-odd (succ a) with lemma-even-odd a
-- if a (p) belongs in left (even), the witness is
-- in right using the proof that its successor is in even
...| left  p = right (lemma-succ-even p)
-- if a (p) belongs in right (odd), the witness is
-- in left using the proof that its successor is in odd
...| right p = left (lemma-succ-odd  p)

---[ EXERCISE 6 ]---
-- Show that the number one is not even, in the following sense:
data ⊥ : Set where

-- By definition, "not A" means "A implies contradiction"
-- If 1 would be even, then contradiction "⊥"
lemma-one-not-even : Even (succ zero) → ⊥
-- there are no inputs to lemma-one-not-even, Agda knows that it cannot
-- be true
lemma-one-not-even ()

-- QUESTION: How to prove that it is NOT the case that successors of even numbers are even?
lemma : ((n : ℕ) → Even n → Even (succ n)) → ⊥
lemma f = lemma-one-not-even (f zero base-even)

---[ EXERCISE 7 ]---
-- Show that the double of any number is even
-- (Note: With our current Agda knowledge, this is very hard. Later it
-- will be very easy.)
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ b) = {!!!!}


-----------------------
----[ TAUTOLOGIES ]----
-----------------------

---[ EXERCISE 8 ]---
-- Fill in the following hole (lambda notation for anonymous function
-- might be useful ("λ x → ..."), but is not required), thereby verifying
-- a well-known logical tautology.
-- If A implies B, then if B implies R then also A implies R
contraposition : {A B R : Set} → (A → B) → ((B → R) → (A → R))
-- if you have contraposition f = { }0 and type Ctrl-C Ctrl-A
-- (Automatic Proof Search) you get
-- contraposition f = λ z z₁ → z (f z₁)

-- the type theory way of reading this is that
-- contraposition is a function that reads as input is a function of the kind
-- A→B and returns a function of the kind A→R
-- we can use lambda notation λ which takes an input a parameter x
contraposition f = λ k → (λ x → k (f x))
-- Honestly I don't know what happened...

add2 : ℕ → ℕ
add2 = _+_ (succ (succ zero))

ex : ℕ
ex = _+_ zero zero   -- this is what "zero + zero" gets desugared to

{-
  anonymous functions:
  in Agda: λ x → ...
  in Haskell: \x -> ...
  in JavaScript: function (x) {...}
  in Perl: sub {...}


  in Agda, there are no functions of two arguments: "f x y" is strictly speaking, a lie.
  As a substitute, there are functions f reading a single argument x as input and returning,
  as output, a new function which then reads a further argument y as input and computes the result.

  f : X → Y → Z        f : X → (Y → Z)

  f x y = (f x) y
          ^^^^^
          function Y → Z

  Keyword: "currying"
-}

---[ EXERCISE 9 ]---
--Verify that disjunction is commutative, in the following sense:
or-commutative : {A B : Set} → A ⊎ B → B ⊎ A
or-commutative (left  x) = right x
or-commutative (right y) = left  y

{-
in Haskell:
or-commutative : Either a b → Either b a
or-commutative (Left  x) = Right x
or-commutative (Right y) = Left  y
-}

