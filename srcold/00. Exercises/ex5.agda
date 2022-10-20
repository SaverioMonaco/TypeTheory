-- AGDA IN PADOVA 2022
-- Exercise sheet 5

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixl 5 _≡_
infixl 6 _+_
infixl 7 _·_

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)


------------------------------------
----[ GENERALITIES ON EQUALITY ]----
------------------------------------

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- EQUATIONAL REASONING

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p


---------------------------------
----[ EQUALITIES OF NUMBERS ]----
---------------------------------

lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
-- (lemma-+-zero a) is a value of type ((a + zero) ≡ a).
-- What we need is a value of type (succ (a + zero) ≡ succ a).

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero     b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))

lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
-- Goal: a + (b + c) ≡ a + b + c
-- ————————————————————————————————————————————————————————————
--         a, b, c : ℕ
-- N.B: from ((a + b) + c) Agda computed it is equivalent to a + b + c
lemma-+-associative zero b c = refl
-- Goal: succ (a + (b + c)) ≡ succ (a + b + c)
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl
lemma-·-distributive (succ a) b c = begin
  ((succ a + b) · c)      ≡⟨⟩
  (succ (a + b) · c)      ≡⟨⟩
  c + ((a + b) · c)       ≡⟨ cong (_+_ c) (lemma-·-distributive a b c) ⟩
  c + ((a · c) + (b · c)) ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩
  (c + (a · c)) + (b · c) ≡⟨⟩
  (succ a · c) + (b · c)  ∎

-- EXERCISE: Prove this theorem.
lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap zero     b c = refl
lemma-+-swap (succ a) b c = begin
  (succ a + (b + c)) ≡⟨⟩
  succ (a + (b + c)) ≡⟨ cong succ (lemma-+-swap a b c) ⟩
  succ (b + (a + c)) ≡⟨ symm (lemma-+-succ b (a + c)) ⟩
  b + succ (a + c)   ≡⟨⟩
  b + (succ a + c)   ∎
-- Note: There is a second solution without a case distinction.
-- This second solution instead appeals to associativity and commutativity.

lemma-+-swap' : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap' zero     b c = refl
lemma-+-swap' (succ a) b c = trans (cong succ (lemma-+-swap' a b c)) (symm (lemma-+-succ b (a + c)))

-- EXERCISE: Verify associativity of multiplication.
lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative zero     b c = refl
lemma-·-associative (succ a) b c = begin
  (succ a) · (b · c)    ≡⟨⟩
  (b · c) + a · (b · c) ≡⟨ cong (λ z → b · c + z) (lemma-·-associative a b c) ⟩
  (b · c) + (a · b) · c ≡⟨ symm (lemma-·-distributive b (a · b) c) ⟩
  (b + a · b) · c       ≡⟨⟩
  (succ a · b) · c      ∎

-- LET'S RESUME AT 15:36 :-)

-- EXERCISE: Fill in this hole.
lemma-·-zero : (a : ℕ) → ((a · zero) ≡ zero)
lemma-·-zero zero = refl
-- Goal: a · zero ≡ zero
-- ——————————————————————
lemma-·-zero (succ a) = (lemma-·-zero a)

-- EXERCISE: Fill in this hole.
lemma-·-succ : (a b : ℕ) → ((a · succ b) ≡ (a + (a · b)))
lemma-·-succ zero b = refl
-- Goal: succ (b + a · succ b) ≡ succ (a + (b + a · b))
--       ———————————————————————————————————————————————
--       a, b : ℕ
lemma-·-succ (succ a) b = {!!}

-- EXERCISE: Verify commutativity of multiplication.
-- Hint: lemma-·-zero and lemma-·-succ will come in handy.
lemma-·-commutative : (a b : ℕ) → ((a · b) ≡ (b · a))
lemma-·-commutative a b = {!!}


-----------------------------
----[ MORE ON RELATIONS ]----
-----------------------------

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- EXERCISE: Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
data AllEven : List ℕ → Set where
  empty : AllEven []
  cons  : {x : ℕ} {xs : List ℕ} → Even x → AllEven xs → AllEven (x ∷ xs)

data Dec (X : Set) : Set where
  yes : X       → Dec X
  no  : (X → ⊥) → Dec X

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd = {!!}

lemma-odd-and-even : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even (step-odd q) (step-even p) = lemma-odd-and-even q p

even? : (n : ℕ) → Dec (Even n)
even? n with lemma-even-odd n
... | left  p = yes p
... | right q = no (lemma-odd-and-even q)

all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? []       = yes empty
all-even? (x ∷ xs) with even? x with all-even? xs
... | yes p | yes f = yes (cons p f)
... | yes p | no  g = {!!}
... | no  q | _ = no λ { (cons r _) → q r }

-- EXERCISE: Show that the sum of the elements of a list satisfying "AllEven" is even.
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

lemma-+-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-+-even p q = {!!}

sum-is-even : (xs : List ℕ) → AllEven xs → Even (sum xs)
sum-is-even xs p = {!!}

-- EXERCISE: Define the relation _≤_ on natural numbers.
data _≤_ : ℕ → ℕ → Set where
  base : {a : ℕ}   → a ≤ a
  step : {a b : ℕ} → a ≤ b → a ≤ succ b

data Bool : Set where
  false true : Bool

-- Boolean-based approach as in Haskell
≤? : ℕ → ℕ → Bool
≤? zero     b        = true
≤? (succ a) zero     = false
≤? (succ a) (succ b) = ≤? a b

-- translation of the preceding Boolean-based definition to a relational definition:
data _≤'_ : ℕ → ℕ → Set where
  base' : {b : ℕ}   → zero ≤' b
  step' : {a b : ℕ} → a ≤' b → succ a ≤' succ b

{-
data Dec (X : Set) : Set where
  yes : X       → Dec X
  no  : (X → ⊥) → Dec X
  -}

≤'-is-decidable : (a b : ℕ) → Dec (a ≤' b)
≤'-is-decidable zero     b        = yes base'
≤'-is-decidable (succ a) zero     = no {!!}
≤'-is-decidable (succ a) (succ b) with ≤'-is-decidable a b
... | yes p = yes (step' p)
... | no  q = no  {!!}
-- EXERCISES: fill these in :-)

{-
foo : (a b : ℕ) → a ≤ b → ...

foo : (a b : ℕ) → ≤? a b ≡ true → ...
-}

-- EXERCISE: Define a predicate "All P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "All P xs" is inhabited if
-- and only if all entries of the list "xs" satisfy P.
-- The special case "All Even" should coincide with the predicate
-- "AllEven" from the previous exercise.
data All {A : Set} (P : A → Set) : List A → Set where
  empty : All P []
  cons  : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- EXERCISE: Define a predicate "Any P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "Any P xs" is inhabited if
-- and only if at least one entry of the list "xs" satisfies P.
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x      → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- EXERCISE: Define a relation "_∈_" such that "x ∈ ys" is the type
-- of witnesses that x occurs in the list ys.
data _∈_ {A : Set} : A → List A → Set where
  here  : {a : A}   {xs : List A} → a ∈ (a ∷ xs)
  there : {a x : A} {xs : List A} → a ∈ xs → a ∈ (x ∷ xs)

-- EXERCISE: Show that "x ∈ ys" if and only if "Any (_≡_ x) ys".
∈-to-Any : {A : Set} {x : A} {ys : List A} → x ∈ ys → Any (_≡_ x) ys
∈-to-Any = {!!}

Any-to-∈ : {A : Set} {x : A} {ys : List A} → Any (_≡_ x) ys → x ∈ ys
Any-to-∈ = {!!}

