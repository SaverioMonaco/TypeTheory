-------------------------------
-------------------------------
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-------------------------------
-------------------------------

------------------------
----[ EVEN AND ODD ]----
------------------------

-- Even n is the type of witnesses that n is even
-- The definition of Even is just as the
-- definition of ℕ
data Even : ℕ → Set where
  base-even : Even zero -- base element
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero) -- base element
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

------------------------------------------
-- >> EXERCISE 1
-- Show that the sum of even numbers is even
------------------------------------------
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base-even b = b
lemma-sum-even (step-even a) b = step-even (lemma-sum-even a b)

------------------------------------------
-- >> EXERCISE 2
-- Show that the successor of an even number is odd and vice versa
------------------------------------------
lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even a) = step-odd (lemma-succ-even a)

lemma-succ-odd : {b : ℕ} → Odd b → Even (succ b)
lemma-succ-odd base-odd = step-even base-even
lemma-succ-odd (step-odd b) = step-even (lemma-succ-odd b)

------------------------------------------
-- >> EXERCISE 3
-- Show that the sum of odd numbers is even
------------------------------------------
lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd base-odd b = lemma-succ-odd b
lemma-sum-odd (step-odd a) b = step-even (lemma-sum-odd a b)

------------------------------------------
-- >> EXERCISE 4
-- Show that the sum of an odd number with an even number is odd
------------------------------------------
lemma-sum-mixed : {a b : ℕ} → Odd a → Even b → Odd (a + b)
lemma-sum-mixed base-odd b = lemma-succ-even b
lemma-sum-mixed (step-odd a) b = step-odd (lemma-sum-mixed a b)

------------------------------------------
-- >> EXERCISE 5
-- Show that every number is even or odd.
------------------------------------------
data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- for instance if x in A, then left x in A ⊎ B

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
...| left p  = right (lemma-succ-even p)
...| right p = left  (lemma-succ-odd  p)

------------------------------------------
-- >> EXERCISE 6
-- Show that the number one is not even.
------------------------------------------
-- This is a preview of proofs by contradiction
data ⊥ : Set where

lemma-one-not-even : Even (succ zero) → ⊥
lemma-one-not-even ()

------------------------------------------
-- >> EXERCISE 7
-- Verify that disjunction is commutative, in the following sense:
------------------------------------------
or-commutative : {A B : Set} → A ⊎ B → B ⊎ A
or-commutative (left x) = right x
or-commutative (right x) = left x




