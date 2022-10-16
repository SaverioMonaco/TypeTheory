-- Exercise 2:
-- Look at it after LAB2
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

mylist : List ℕ
mylist = (succ (succ (succ zero))) ∷ ((succ (succ zero)) ∷ (succ zero ∷ []))

---[ EXERCISE 1 ]---
-- Define a function which sums the numbers of a given list
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

-- (Ctrl-C Ctrl-N (or V) )
-- >> mylist
-- succ (succ (succ zero)) ∷ (succ (succ zero) ∷ (succ zero ∷ []))
-- >> sum mylist
-- succ (succ (succ (succ (succ (succ zero)))))

---[ EXERCISE 2 ]---
-- Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs 

add1 : ℕ → ℕ
add1 n = n + succ zero

-- (Ctrl-C Ctrl-N (or V) )
-- >> map add1 mylist
-- succ (succ (succ (succ zero))) ∷ (succ (succ (succ zero)) ∷
-- (succ (succ zero) ∷ []))

-------------------
----[ VECTORS ]----
-------------------

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

myvector : Vector ℕ (succ (succ (succ zero)))
myvector = zero ∷ (zero ∷ (zero ∷ []))

---[ EXERCISE 3 ]---
-- Define a function which computes the length of a given vector.
-- There are two possible implementations, one which runs in constant time
-- and one which runs in linear time.
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV []       = zero
lengthV (x ∷ xs) = succ (lengthV xs)

lengthV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV' {n} {A} xs = n

-- (Ctrl-C Ctrl-N (or V) )
-- >> lengthV myvector
-- succ (succ (succ zero))
-- >> lengthV' myvector
-- succ (succ (succ zero))

--- [ EXERCISE 4 ]---
-- Define the "map" function for vectors.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

-- (Ctrl-C Ctrl-N (or V) )
-- >> mapV add1 myvector
-- succ zero ∷ (succ zero ∷ (succ zero ∷ []))

---[ EXERCISE 5 ]---
-- Define these vector functions.
-- For instance, "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])"
-- should evaluate to "f x a ∷ f y b ∷ []".
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f []       []       = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

myvector2 : Vector ℕ (succ (succ (succ zero)))
myvector2 = zero ∷ ((succ zero) ∷ ((succ (succ zero)) ∷ []))

-- For instance, "dropV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "b ∷ c ∷ []".
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero xs = xs
dropV (succ k) (x ∷ xs) = dropV k xs

-- For instance, "takeV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "a ∷ []".
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero     xs       = []
takeV (succ k) (x ∷ xs) = x ∷ takeV k xs

-- For instance, "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])" should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[] ++ ys = ys  
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV [] y = y ∷ []
snocV (x ∷ xs) y = x ∷ snocV xs y 

-- For instance, "reverseV (a ∷ b ∷ c ∷ [])" should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV [] = []
reverseV (x ∷ xs) = snocV (reverseV xs) x 

-- For instance, "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])" should evlauate to
-- "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concatV []         = []
concatV (xs ∷ xss) = xs ++ concatV xss

