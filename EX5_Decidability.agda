data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Empty Set, which indicates contradiction
data ⊥ : Set where

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

------------------------------------------
-- >> EXERCISE 1
-- Prove that ≤' is decidable
------------------------------------------
data _≤_ : ℕ → ℕ → Set where
  base : {a : ℕ}   → a ≤ a
  step : {a b : ℕ} → a ≤ b → a ≤ succ b

data Bool : Set where
  false true : Bool
  
------------------------------------------
-- >> EXERCISE 2
-- Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
------------------------------------------
data AllEven : List ℕ → Set where
  empty : AllEven []
  cons : {x : ℕ} {xs : List ℕ} → Even x → AllEven xs → AllEven (x ∷ xs)

data Dec (X : Set) : Set where
  yes : X       → Dec X
  no  : (X → ⊥) → Dec X

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even a) = step-odd (lemma-succ-even a)

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd = step-even base-even
lemma-succ-odd (step-odd a) = step-even (lemma-succ-odd a)

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left (base-even)
lemma-even-odd (succ a) with lemma-even-odd a
... | left p  = right (lemma-succ-even p)
... | right p = left  (lemma-succ-odd p)

lemma-odd-and-even : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even (step-odd p) (step-even q) = lemma-odd-and-even p q

even? : (n : ℕ) → Dec (Even n)
even? n with lemma-even-odd n
... | left  p = yes p
... | right q = no (lemma-odd-and-even q)

lemma-helper : {x : ℕ} {xs : List ℕ} → (Even x) → (AllEven xs → ⊥) → (AllEven (x ∷ xs) → ⊥)
lemma-helper p q (cons x-even xs-even) = q xs-even

all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? []       = yes empty
all-even? (x ∷ xs) with even? x with all-even? xs
... | yes p | yes f = yes (cons p f)
... | yes p | no  g =  no (lemma-helper p g)
... | no  q | _ = no λ { (cons r _) → q r }

------------------------------------------
-- >> EXERCISE 3
-- Show that the sum of the elements of a list satisfying "AllEven" is even.
------------------------------------------
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

lemma-+-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-+-even base-even q = q
lemma-+-even (step-even p) q = step-even (lemma-+-even p q)

sum-is-even : (xs : List ℕ) → AllEven xs → Even (sum xs)
sum-is-even [] p = base-even
sum-is-even (x ∷ xs) (cons p q) = lemma-+-even p (sum-is-even xs q)

-- Boolean-based approach as in Haskell
≤? : ℕ → ℕ → Bool
≤? zero     b        = true
≤? (succ a) zero     = false
≤? (succ a) (succ b) = ≤? a b

-- translation of the preceding Boolean-based definition to a relational definition:
data _≤'_ : ℕ → ℕ → Set where
  base' : {b : ℕ}   → zero ≤' b
  step' : {a b : ℕ} → a ≤' b → succ a ≤' succ b

-- Goal: succ a ≤' succ b → ⊥
--       —————————————————————
--       q : a ≤' b → ⊥
--       a b : ℕ
lemma-helper-≤' : {a b : ℕ} → (a ≤' b → ⊥) → (succ a ≤' succ b → ⊥)
lemma-helper-≤' p (step' a≤b) = p a≤b

≤'-is-decidable : (a b : ℕ) → Dec (a ≤' b)
≤'-is-decidable zero     b        = yes base'
≤'-is-decidable (succ a) zero     = no λ ()
≤'-is-decidable (succ a) (succ b) with ≤'-is-decidable a b
... | yes p = yes (step' p)
... | no  q = no  (lemma-helper-≤' q)
