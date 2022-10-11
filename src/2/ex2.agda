-- Exercise 1:
---------------------------
----[ NATURAL NUMBERS ]----
---------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)


-----------------
----[ LISTS ]----
-----------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- EXERCISE: Define a function which sums the numbers of a given list
sum : List ℕ → ℕ
sum []       = {!!}
sum (x ∷ xs) = {!!}

-- EXERCISE: Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}


-------------------
----[ VECTORS ]----
-------------------

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

-- EXERCISE: Define a function which computes the length of a given vector.
-- There are two possible implementations, one which runs in constant time
-- and one which runs in linear time.
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV []       = zero
lengthV (x ∷ xs) = succ (lengthV xs)

lengthV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV' {n} {A} xs = n

-- EXERCISE: Define the "map" function for vectors.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f xs = {!!}

-- EXERCISE: Define these vector functions.
-- For instance, "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])" should evaluate to "f x a ∷ f y b ∷ []".
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f []       []       = {!!}
zipWithV f (x ∷ xs) (y ∷ ys) = {!!}

-- For instance, "dropV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "b ∷ c ∷ []".
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
dropV k xs = {!!}

-- For instance, "takeV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "a ∷ []".
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero     xs       = []
takeV (succ k) (x ∷ xs) = x ∷ takeV k xs

-- For instance, "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])" should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
xs ++ ys = {!!}

-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV xs y = {!!}

-- For instance, "reverseV (a ∷ b ∷ c ∷ [])" should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV xs = {!!}

-- For instance, "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])" should evlauate to
-- "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concatV []         = []
concatV (xs ∷ xss) = xs ++ concatV xss

