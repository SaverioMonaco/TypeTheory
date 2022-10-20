-------------------------------
-------------------------------
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_·_ : ℕ → ℕ → ℕ
zero   · b = zero
succ a · b = b + (a · b)

-------------------------------
-------------------------------

-----------------
----[ LISTS ]----
-----------------

-- List is an object of a given type (A)
data List (A : Set) : Set where
  -- base element (empty list)
  []  : List A
  -- prepend function prepend(x, list) = [x,list]
  _∷_ : A → List A → List A

list_example : List ℕ -- with ℕ we declare its element will be naturals
list_example = (succ (succ (succ zero))) ∷ ((succ (succ zero)) ∷ (succ zero ∷ []))
--           = [3,2,1]

------------------------------------------
-- >> EXERCISE 1
-- Define a function which sums the numbers of a given list
------------------------------------------
sum : List ℕ → ℕ
sum [] = zero
sum (x ∷ xs) = x + (sum xs)

-- >> sum list_example                           → (sum [1,2,3])
-- succ (succ (succ (succ (succ (succ zero)))))  → (6)

------------------------------------------
-- >> EXERCISE 2
-- Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
------------------------------------------

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

-- >> map (λ xs → xs + (succ zero)) list_example
-- succ (succ (succ (succ zero))) ∷ (succ (succ (succ zero)) ∷ (succ (succ zero) ∷ []))

-- Note: (λ xs → xs + (succ zero)) is the syntax to define an anonymous function
-- λ that takes xs as input and adds succ zero to it (adds one)

-------------------
----[ VECTORS ]----
-------------------
-- The difference is that Vector has a fixed lenght

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

vector_example : Vector ℕ (succ (succ (succ zero)))
vector_example = zero ∷ ((succ zero) ∷ ((succ (succ (succ zero))) ∷ []))

------------------------------------------
-- >> EXERCISE 3
-- Define a function which computes the length of a given vector.
-- There are two possible implementations, one which runs in constant time
-- and one which runs in linear time.
------------------------------------------

-- Very trivial function:
-- When you pass the vector, it returns its lenght
-- being one of its parameters
lenghtV : {n : ℕ} {A : Set} → Vector A n → ℕ
lenghtV {n} {A} xs = n

lenghtV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lenghtV' [] = zero
lenghtV' (x ∷ xs) = succ (lenghtV' xs)

-- >> lenghtV' vector_example
-- succ (succ (succ zero))

------------------------------------------
-- >> EXERCISE 4
-- Define the "map" function for vectors.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
------------------------------------------

mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f [] = []
mapV f (x ∷ xs) = (f x) ∷ (mapV f xs)

-- >> mapV (λ xs → xs + (succ zero)) vector_example
-- succ zero ∷ (succ (succ zero) ∷ (succ (succ (succ (succ zero))) ∷ []))

------------------------------------------
-- >> EXERCISE 5
-- 5.1 "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])"
--      should evaluate to "f x a ∷ f y b ∷ []".
-- 5.2 "dropV (succ zero) (a ∷ b ∷ c ∷ [])"
--      should evaluate to "b ∷ c ∷ []".
-- 5.3 "takeV (succ zero) (a ∷ b ∷ c ∷ [])"
--      should evaluate to "a ∷ []".
-- 5.4 "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])"
--      should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
-- 5.5 "snocV (a ∷ b ∷ []) c"
--      should evaluate to "a ∷ b ∷ c ∷ []".
-- 5.6 "reverseV (a ∷ b ∷ c ∷ [])"
--      should evaluate to "c ∷ b ∷ a ∷ []".
-- 5.7 "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])"
--      should evlauate to "a ∷ b ∷ c ∷ d ∷ []".
------------------------------------------

-- 5.1 zipWithV
-- "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])"
--  should evaluate to "f x a ∷ f y b ∷ []"
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f []       []       = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

-- 5.2 dropV
-- "dropV (succ zero) (a ∷ b ∷ c ∷ [])"
--  should evaluate to "b ∷ c ∷ []".
dropV : {n : ℕ} {A : Set} → (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero xs = xs
dropV (succ a) (x ∷ xs) = dropV a xs

-- >> dropV (succ zero) vector_example
-- zero ∷ (succ zero ∷ (succ (succ (succ zero)) ∷ []))

-- 5.3 takeV
-- "takeV (succ zero) (a ∷ b ∷ c ∷ [])"
--  should evaluate to "a ∷ []".
takeV : {n : ℕ} {A : Set} → (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero xs = []
takeV (succ k) (x ∷ xs) = x ∷ (takeV k xs)

-- >> takeV (succ (succ zero)) vector_example
-- zero ∷ (succ zero ∷ [])

-- 5.4 _++_
-- "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])"
--  should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {n m : ℕ} {A : Set} → Vector A n → Vector A m → Vector A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- >> vector_example ++ vector_example
-- zero ∷
-- (succ zero ∷
-- (succ (succ (succ zero)) ∷
-- (zero ∷ (succ zero ∷ (succ (succ (succ zero)) ∷ [])))))

-- 5.5 snocV
-- "snocV (a ∷ b ∷ []) c"
--  should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {n : ℕ} {A : Set} → Vector A n → A → Vector A (succ n)
snocV [] k = k ∷ []
snocV (x ∷ xs) k = x ∷ (snocV xs k)

-- snocV vector_example zero
-- zero ∷ (succ zero ∷ (succ (succ (succ zero)) ∷ (zero ∷ [])))

-- 5.6 reverseV
-- "reverseV (a ∷ b ∷ c ∷ [])"
--  should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {n : ℕ} {A : Set} → Vector A n → Vector A n
reverseV [] = []
reverseV (x ∷ xs) = snocV (reverseV xs) x 

-- >> vector_example
-- zero ∷ (succ zero ∷ (succ (succ (succ zero)) ∷ []))
-- >> reverseV vector_example
-- succ (succ (succ zero)) ∷ (succ zero ∷ (zero ∷ []))

-- 5.7 concatV
-- "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])"
--  should evlauate to "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concatV []         = []
concatV (xs ∷ xss) = xs ++ concatV xss



