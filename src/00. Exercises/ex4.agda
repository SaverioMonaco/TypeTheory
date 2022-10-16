-- AGDA IN PADOVA 2022
-- Exercise sheet 4

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ⊥ : Set where

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

pred : ℕ → ℕ
pred zero     = zero
pred (succ a) = a

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

-- EQUATIONAL REASONING

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q rewrite p = q


_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p



------------------------------------
----[ GENERALITIES ON EQUALITY ]----
------------------------------------

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

---[ EXERCISE 1 ]---
-- Fill in this hole, thereby proving that equality is transitive.
-- Goal: x ≡ z
-- —————————————————————————
-- q : y ≡ z
-- p : x ≡ y
-- z : A   (not in scope)
-- y : A   (not in scope)
-- x : A   (not in scope)
-- A : Set   (not in scope)
trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' refl q = q


---[ EXERCISE 2 ]---
-- Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
equal→pwequal refl = refl

---[ EXERCISE ? ]---
-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)".


---------------------------------
----[ EQUALITIES OF NUMBERS ]----
---------------------------------

---[ EXERCISE 3 ]---
-- Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = refl

---[ EXERCISE 4 ]---
-- Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
-- being pred zero = 0, succ (pred zero) = succ zero ≠ zero
-- since it does not work for every natural number as stated in the definition
-- (a : ℕ) then it must be a contradiction
-- Goal: ⊥
-- —————————
-- f : (a : ℕ) → succ (pred a) ≡ a
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {!!}

---[ EXERCISE 5 ]---
-- Define a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" should be empty
-- and the types "Positive (succ n)" should be inhabited for every n.
-- Then fill in the hole below.
data Positive : ℕ → Set where
  -- do NOT include this constructor:
  -- zero-is-positive : Positive zero
  -- for us zero is neither positive nor negative
  succs-are-positive : {n : ℕ} → Positive (succ n)
  -- any number of the form succ whatever is positive.

lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ b) p = refl

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

---[ EXERCISE 6 ]---
-- Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl
-- Goal: succ (a + (b + c)) ≡ succ ((a + b) + c)
--       ————————————————————————————————————————————————————————————
--       c : ℕ, b : ℕ, a : ℕ
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl
lemma-·-distributive (succ a) b c = begin
  ((succ a + b) · c)      ≡⟨⟩      -- by definition
  (succ (a + b) · c)      ≡⟨⟩      -- by definition
  c + ((a + b) · c)       ≡⟨ cong (_+_ c) (lemma-·-distributive a b c) ⟩   -- by induction (with "c + ___" as a fixed part)
  c + ((a · c) + (b · c)) ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩   -- by associativity of +
  (c + (a · c)) + (b · c) ≡⟨⟩      -- by definition
  (succ a · c) + (b · c)  ∎

---[ EXERCISE 7 ]---
-- Show that the double of any number is even.
-- This has been an exercise before; now we can solve it.
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))
-- Even is a function which takes numbers as inputs and outputs types.

{-
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ b) = transport Even e' p
  where
  p : Even (succ (succ (b + b)))
  p = step-even (lemma-double-even b)

  e : succ (b + b) ≡ (b + succ b)
  e = symm (lemma-+-succ b b)

  e' : succ (succ (b + b)) ≡ succ (b + succ b)
  e' = cong succ e
-}

{-
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ b) = transport Even (cong succ (symm (lemma-+-succ b b))) (step-even (lemma-double-even b))
-}
magic : {x y : ℕ} → x ≡ y → Even x → Even y
magic refl s = s

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero = base-even
-- Goal: Even (succ (b + succ b))
--       ——————————————————————————
--       b : ℕ
-- the ordering does not quite match up
-- with what we would demonstate:
-- (succ (succ (b+b)))
lemma-double-even (succ b) = magic e' p
  where
  p : Even (succ (succ b + b))
  p = step-even (lemma-double-even b)

  -- mini helping proofs
  e : succ (b + b) ≡ (b + succ b)
  e = symm (lemma-+-succ b b)

  e' : succ (succ (b + b)) ≡ succ (b + succ b)
  e' = cong succ e

-------------------------------
----[ EQUALITIES OF LISTS ]----
-------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

module _ {A : Set} where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  -- for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []".
  reverse : List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ∷ʳ x

  -- EXERCISE 8: Verify the following lemma.
  lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  -- Goal: reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  -- ———————————————————————————————————————
  -- x  : A, ys : List A, A  : Set
  lemma-reverse-∷ʳ [] x = refl
  -- Goal: (reverse (ys ∷ʳ x) ∷ʳ x₁) ≡ (x ∷ (reverse ys ∷ʳ x₁))
  lemma-reverse-∷ʳ (x₁ ∷ ys) x = {!!}

  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse []       = refl
  lemma-reverse-reverse (x ∷ xs) =
    trans (lemma-reverse-∷ʳ (reverse xs) x)
          (cong (λ zs → x ∷ zs) (lemma-reverse-reverse xs))

  -- EXERCISE 9: State and prove that _++_ on lists is associative.
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- The following relation relates exactly those lists which have the same length
  -- and whose corresponding entries are equal.
  data _≈_ : List A → List A → Set where
    both-empty     : [] ≈ []
    both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  -- EXERCISE 10: Show that equal lists are related by _≈_.
  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ {[]} refl = both-empty
  ≡→≈ {x ∷ xs} refl = both-same-cons refl (≡→≈ refl)

  -- EXERCISE 11: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ {[]}     both-empty = refl
  ≈→≡ {x ∷ xs} (both-same-cons refl p) = cong (_∷_ x) (≈→≡ p)


---------------------------------
----[ EQUALITIES OF VECTORS ]----
---------------------------------

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop zero      xs        = xs
drop (succ k') (x ∷ xs') = drop k' xs'

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take zero      xs        = []
take (succ k') (x ∷ xs') = x ∷ take k' xs'

_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[]        ++ᵥ ys = ys 
(x ∷ xs') ++ᵥ ys = x ∷ (xs' ++ᵥ ys) 

-- EXERCISE: Verify the following lemma.
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop = {!!}

-- EXERCISE: Find out where the difficulty is in stating that _++ᵥ_ on
-- vectors is associative.


data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

_≢_ : {A : Set} → A → A → Set
x ≢ y = ((x ≡ y) → ⊥)

theorem : zero ≢ succ zero
theorem ()

module _ {A : Set} (cmp : (x : A) → (y : A) → (x ≡ y) ⊎ (x ≢ y)) where
  delete : A → List A → List A
  delete x [] = []
  delete x (y ∷ ys) with cmp x y
  ... | left  p = delete x ys
  ... | right p = y ∷ delete x ys
  -- if x and y are the same,     the result should be delete x ys
  -- if x and y are not the same, the result should be y ∷ delete x ys

  count-number-of-occurences : A → List A → ℕ
  count-number-of-occurences x ys = {!!}

