-------------------------------
-------------------------------
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Empty Set, which indicates contradiction
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

-- Here we define the equality ≡ (\==)
data _≡_ {X : Set} : X → X → Set where
  -- with the following properties (just one):
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
-- Internally Agda uses the equality for
-- commands (such as the rewrite keyword)

-------------------------------
-------------------------------

------------------------------------
----[ GENERALITIES ON EQUALITY ]----
------------------------------------

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

------------------------------------------
-- >> EXERCISE 1
-- Prove that equality is transitive.
------------------------------------------
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

------------------------------------------
-- >> EXERCISE 2
-- Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
------------------------------------------
equal→pwequal : {A B : Set} {x : A} {f g : A → B} → f ≡ g → f x ≡ g x
equal→pwequal refl = refl

---------------------------------
----[ EQUALITIES OF NUMBERS ]----
---------------------------------

------------------------------------------
-- >> EXERCISE 3
-- Show that the predecessor of the successor
-- of a number is that number again.
------------------------------------------
lemma-pred-succ : (n : ℕ) → n ≡ (pred (succ n))
lemma-pred-succ n = refl

------------------------------------------
-- >> EXERCISE 4
-- Show that it is not the case that "succ (pred a) ≡ a"
-- for all natural numbers a. Being pred zero = 0,
-- succ (pred zero) = succ zero ≠ zero
-- since it does not work for every natural number
-- as stated in the definition
------------------------------------------
lemma-succ-pred : ((n : ℕ) → succ (pred n) ≡ n) → ⊥
lemma-succ-pred f with f zero
... | ()

------------------------------------------
-- >> EXERCISE 5
-- Define a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" should be empty
-- and the types "Positive (succ n)" should be inhabited for every n.
-- Then fill in the hole below.
------------------------------------------
data Positive : ℕ → Set where
  succs-are-positive : {n : ℕ} → Positive (succ n)

lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ a) p = refl

------------------------------------------
-- >> EXERCISE 6
-- Find the commutative property of the addition
------------------------------------------
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero b = symm (lemma-+-zero b)
-- Goal: succ (a + b) ≡ (b + succ a)
lemma-+-commutative (succ a) b = trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))

------------------------------------------
-- >> EXERCISE 7
-- Verify that addition is associative.
------------------------------------------
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

------------------------------------------
-- >> EXERCISE 8
-- Verify the distributive property
------------------------------------------
lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl
-- Goal: (c + ((a + b) · c)) ≡ ((c + (a · c)) + (b · c))
lemma-·-distributive (succ a) b c = trans (cong (λ x → (c + x)) (lemma-·-distributive a b c) ) (lemma-+-associative c (a · c) (b · c) )

------------------------------------------
-- >> EXERCISE 9
-- Show that the double of any number is even.
------------------------------------------
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero = base-even
-- Goal: Even (succ (b + succ b))
--      ——————————————————————————
--       b : ℕ
lemma-double-even (succ b) = helper succ-desucc p
  where
  helper : {x y : ℕ} → x ≡ y → Even x → Even y
  helper refl eveness = eveness
  
  desucc : (succ (b + b)) ≡ (b + succ b)
  desucc = symm (lemma-+-succ b b)

  succ-desucc : succ (succ (b + b)) ≡ succ (b + succ b)
  succ-desucc = cong succ desucc

  p : Even (succ (succ b + b))
  p = step-even (lemma-double-even b)

-------------------------------
----[ EQUALITIES OF LISTS ]----
-------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

example-list = succ (succ zero) ∷ (succ zero ∷ (zero ∷ []))

module _ {A : Set} where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  ------------------------------------------
  -- >> EXERCISE 10
  -- Define reverse function
  -- for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []".
  ------------------------------------------
  reverse : List A → List A  
  reverse [] = []
  reverse (x ∷ xs) = reverse xs ∷ʳ x

  ------------------------------------------
  -- >> EXERCISE 11
  -- lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  ------------------------------------------
  lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  lemma-reverse-∷ʳ [] x = refl
  lemma-reverse-∷ʳ (y ∷ ys) x = cong (λ xs → xs ∷ʳ y) (lemma-reverse-∷ʳ ys x)

  ------------------------------------------
  -- >> EXERCISE 12
  -- lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  ------------------------------------------
  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse [] = refl
  lemma-reverse-reverse (x ∷ xs) = trans (lemma-reverse-∷ʳ (reverse xs) x) (cong (λ xs → x ∷ xs) (lemma-reverse-reverse xs))

  ------------------------------------------
  -- >> EXERCISE 13
  -- State and prove that _++_ on lists is associative.
  ------------------------------------------
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  ------------------------------------------
  -- >> EXERCISE 14
  -- Show that equal lists are related by _≈_.
  ------------------------------------------

  -- The following relation relates exactly those lists which have the same length
  -- and whose corresponding entries are equal.
  data _≈_ : List A → List A → Set where
    both-empty     : [] ≈ []
    both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ {[]} refl = both-empty
  ≡→≈ {x ∷ xs} refl = both-same-cons refl (≡→≈ refl)

  ------------------------------------------
  -- >> EXERCISE 14
  -- Show that related lists are equal
  ------------------------------------------
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ {[]} both-empty = refl
  ≈→≡ {x ∷ xs} (both-same-cons refl p) = cong (λ xs → x ∷ xs) (≈→≡ p)
  
---------------------------------
----[ EQUALITIES OF VECTORS ]----
---------------------------------

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

myvector : Vector ℕ (succ (succ (succ zero)))
myvector = zero ∷ (succ zero ∷ (succ (succ zero) ∷ []))
myvector2 : Vector ℕ (succ (succ zero))
myvector2 = (succ (succ (succ zero))) ∷ ((succ (succ (succ (succ zero)))) ∷ [])

------------------------------------------
-- >> EXERCISE 15
-- remove the first k prepended elements
------------------------------------------
-- drop 3 [1,2,3,4,5,6] → [4,5,6]
drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop zero xs = xs
drop (succ k) (x ∷ xs) = drop k xs

------------------------------------------
-- >> EXERCISE 16
-- the contrary of drop
------------------------------------------ 
-- take 3 [1,2,3,4,5,6] → [1,2,3]
take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take zero xs = []
take (succ k) (x ∷ xs) = x ∷ (take k xs)

------------------------------------------
-- >> EXERCISE 17
-- Concatenate two list
------------------------------------------
_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[] ++ᵥ ys = ys
(x ∷ xs) ++ᵥ ys = x ∷ (xs ++ᵥ ys)

------------------------------------------
-- >> EXERCISE 18
-- (k : ℕ) (xs : Vector A (k + n)) →  (take k xs ++ᵥ drop k xs) ≡ xs
------------------------------------------
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) →  (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop zero xs = refl
lemma-take-drop (succ k) (x ∷ xs) = cong (λ xs → x ∷ xs) (lemma-take-drop k xs)

