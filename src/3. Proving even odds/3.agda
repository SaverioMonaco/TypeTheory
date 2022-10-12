data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ∅ : Set where

one : ℕ
one = succ zero

two : ℕ
two = succ (succ zero)

four : ℕ
four = succ (succ (succ (succ zero)))

-- We will now define, for any natural number n, "Even n".
-- More precisely, "Even n" is a certain type.
-- Namely the type of *witnesses that n is even*.

-- For instance, the type "Even one" (where one = succ zero) should be an empty type.
-- In contrast, the types "Even zero" and "Even four" should each be inhabited.

data Even : ℕ → Set where
  Base : Even zero                                 -- "the number zero is even"
  Step : (n : ℕ) → Even n → Even (succ (succ n))   -- "for every number n, if n is even, so is succ (succ n)"

-- "Odd" is a function which maps natural numbers to (newly created) types.
-- Namely, "Odd n" is the type of witnesses that n is odd.
-- For instance, the type "Odd zero" is empty and the type "Odd one" is inhabited.
data Odd : ℕ → Set where
  Base' : Odd one
  Step' : (n : ℕ) → Odd n → Odd (succ (succ n))

lemma-even-odd : (n : ℕ) → Even n → Odd (succ n)
lemma-even-odd .zero            Base       = Base'
lemma-even-odd .(succ (succ n)) (Step n p) = Step' (succ n) (lemma-even-odd n p)
{-
  in English:

  By induction on n.
  Base case n = 0: In this case we have to verify that 1 is odd. This is trivial (by Base').
  Induction step m → 2 + m: In this case we have to verify that, if m is even, then succ m is odd.
  Because m is even, m is of the form succ (succ n) for some even number n.
  Hence by the inductive hypothesis, the number succ n is odd.
  Hence by Step', the number succ (succ (succ n)) is odd.
-}

data _⊎_ (A B : Set) : Set where  -- in Haskell, this type is called "Either"
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- The type "ℕ ⊎ Bool" contains the following values:
-- left zero, left (succ zero), left (succ (succ zero)), ...
-- right false, right true

-- "Every natural number is even or odd."
theorem : (n : ℕ) → Even n ⊎ Odd n
theorem zero     = left Base
theorem (succ n) with theorem n
... | left  p = right (lemma-even-odd n p)
... | right q = {!!}

fun-fact : Even zero
fun-fact = Base

fun-fact' : Even two
fun-fact' = Step zero Base

fun-fact'' : Even four
-- fun-fact'' = Step (succ (succ zero)) (Step zero Base)
fun-fact'' = Step two fun-fact'

fun-fact''' : Odd (succ (succ (succ zero)))
fun-fact''' = Step' (succ zero) Base'

lemma : (n : ℕ) → Even n → Even n   -- "for every number n, if n is even, then n is even"
lemma n p = p

lemma' : (n : ℕ) → Odd n → Odd n   -- "for every number n, if n is odd, then n is odd
lemma' n p = p

lemma'' : {A : Set} → A → A   -- "A implies A"   "if A, then A"
lemma'' x = x

{-
  ROSETTA STONE BETWEEN COMPUTING AND LOGIC

  programming                  logic/type theory
  ----------------------------------------------
  type A → A of functions      statement that A implies A
  identity function            proof of the statement that A implies A
-}




{-
-- CLAIM: There is no function from ℕ → ∅.
claim : (ℕ → ∅) → ∅
claim f = f zero
-- "There are no function f : ℕ → ∅, just have a look at what f(zero) would be!"

claim' : (ℕ → ∅) → ∅
claim' f = f (succ zero)
-- "There are no function f : ℕ → ∅, just have a look at what f(1) would be!"

data Bool : Set where
  false true : Bool

Set-of-decidable-subsets : Set → Set
Set-of-decidable-subsets X = X → Bool

Powerset : Set → Set₁
Powerset X = X → Set
-- the empty subset of X is given by the function λ x → ∅

truer-Powerset : Set → Set₂
truer-Powerset X = X → Set₁

{-
even-truer-Powerset : Set → Set
even-truer-Powerset X = X → Set₂
-}

-- Prop is the type of all those small types which contain at most one inhabitant.
-- Prop itself is not a small type, but a large type.

is-prop : Set → Set
is-prop X = {!(a : X) → (b : X) → a ≡ b!}    -- "is-prop X" means: "X contains at most one inhabitant"

{-
Prop : Set₁
Prop = ?  -- (the type of pairs (X,p) where X is a small type and p is an element of is-prop X)
-}

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

is-decidable : Set → Set
is-decidable X = X ⊎ (X → ∅)

is-semidecidable-oracle : {X : Set} → (X → Bool ⊎ ∅) → Set
is-semidecidable-oracle f = ?

-- Prop₁ is the type of all those large types which contain at most one inhabitant.
-- Prop₁ itself is not a large type, but a very large type.

-- Prop₂ is the type of all those very large types which contain at most one inhabitant.
-- Prop₂ itself is not a very large type, but a very very large type.

{-


Powerset' : Set → Set₁
Powerset' X = X → Prop
-- the empty subset of X is given by the function λ x → ∅

truer-Powerset' : Set → Set₂
truer-Powerset' X = X → Prop₁

even-truer-Powerset' : Set → Set₃
even-truer-Powerset' X = X → Prop₂

-- Set is the type of small types, but Set itself is not a small type.
-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : ...

-- For most types X, there is no procedure for checking whether any
-- given predicate f : X → Bool has a zero (attains false).
-- But for some types, there is.
-- For instance, for finite types there is.
-- Amazing wonder: Also for some infinite types there is such a checking procedure.
-- Approximately: There is such a checking procedure if and only if X is compact (when thought of as a space).

-- CLAIM: The number one is not even.
-- RECALL: In logic, "¬ φ" is a shorthand for "φ ⇒ ⊥".
{-
lemma-one-not-even : Even one → ∅
lemma-one-not-even = ?
-}

-}
-}

