-- Exercise 3:
-- AGDA IN PADOVA 2022
-- Exercise sheet 3

-- Define Natural Numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Define Addition
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)


------------------------
----[ EVEN AND ODD ]----
------------------------

-- Even is the type of witnesses that n is even.
data Even : ℕ → Set where
  base-even : Even zero -- first witness: zero
  -- function that finds witnesses knowing a witness
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- Odd is the type of witnesses that n is odd.
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

---[ EXERCISE 1 ]---
--- Show that the sum of even numbers is even
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
-- 0 + q = q
lemma-sum-even base-even     q = q
-- p+2 + q = proof[(p+q)] + 2
lemma-sum-even (step-even p) q = step-even (lemma-sum-even p q)

---[ EXERCISE 2 ]---
--- Show that the successor of an even number is odd and vice versa
lemma-succ-even : {n : ℕ} → Even n → Odd (succ n)
lemma-succ-even base-even = base-odd
-- Example:
-- lemma-succ-even (step-even 2) -> lemma-succ-even (4)
-- lemma-succ-even 4 = step-odd (lemma-succ-even 2)
--                     step-odd (lemma-succ-even 2) -> step-odd (step-odd ((lemma-succ-even 0))
--                     step-odd (step-odd (lemma-succ-even 0)) -> step-odd (step-odd base-odd)
--                  = 5 (Odd)
lemma-succ-even (step-even p) = step-odd (lemma-succ-even p)

lemma-succ-odd : {n : ℕ} → Odd n → Even (succ n)
lemma-succ-odd base-odd = step-even base-even
lemma-succ-odd (step-odd p) = step-even (lemma-succ-odd p)

---[ EXERCISE 3 ]---
-- Show that the sum of odd numbers is even
lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd base-odd q = lemma-succ-odd q
lemma-sum-odd (step-odd p) q = step-even (lemma-sum-odd p q)

---[ EXERCISE 4 ]---
-- Show that the sum of an odd number with an even number is odd
lemma-sum-mixed : {a b : ℕ} → Odd a → Even b → Odd (a + b)
lemma-sum-mixed base-odd q = lemma-succ-even q
lemma-sum-mixed (step-odd q) p = step-odd (lemma-sum-mixed q p)


---[ EXERCISE 5 ]---
-- Show that every number is even or odd.
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- For instance, if x : A, then left x : A ⊎ B.
lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
...| left p  = right (lemma-succ-even p)
...| right p = left (lemma-succ-odd p)

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

foo : ℕ → ⊥
foo zero     = {!!}
foo (succ n) = foo n

---[ EXERCISE 7 ]---
-- Show that the double of any number is even
-- (Note: With our current Agda knowledge, this is very hard. Later it
-- will be very easy.)
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ b) = {!!}


-----------------------
----[ TAUTOLOGIES ]----
-----------------------

-- EXERCISE: Fill in the following hole (lambda notation for anonymous function
-- might be useful ("λ x → ..."), but is not required), thereby verifying
-- a well-known logical tautology.
contraposition : {A B R : Set} → (A → B) → ((B → R) → (A → R))
contraposition f = λ k x → k (f x)

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

---[ EXERCISE 7 ]---
-- Verify that disjunction is commutative, in the following sense:
or-commutative : {A B : Set} → A ⊎ B → B ⊎ A
or-commutative (left  x) = right x
or-commutative (right y) = left  y

{-
in Haskell:
or-commutative : Either a b → Either b a
or-commutative (Left  x) = Right x
or-commutative (Right y) = Left  y
-}

