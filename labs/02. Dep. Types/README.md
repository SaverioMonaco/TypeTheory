## Vectors, basic functions with vectors:
#### on to dependent types!
* ***Negative example***
  The type "list of integers" depends on the type of integers, but this is still a type (and not a value), and hence the type "list of integers" would not usually be called a "dependent type".
* ***Positive example***
  The type "vectors of length n" depends on the number n (which is a value, not a type), and hence the type "vectors of length n" would be called a "dependent type".
  (By "vector of lenght n" it means a list of n elements)

#### Old sets and functions:
```agda
data Bool : Set where
  false : Bool
  true  : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ -- "succ" is short for "successor"
```

#### Vector of Booleans
Let us implement a vector of lenght n, aka a dependent type:
1. First we need to agree which type are the elements in the list (let us say the elements should be Booleans
```agda
data Vector : ℕ → Set where
```
2. Define the empty vector
```agda
data Vector : ℕ → Set where
  []  : Vector zero
```
3. Then we need to specify the way to prepend (_::_) a value to a vector that already exists:
```agda
data Vector : ℕ → Set where
  []  : Vector zero
  _∷_ : {n : ℕ} → Bool → Vector n → Vector (succ n)
```
Note:
```agda
-- Define a vector of lenght 3
example-vector : Vector (succ (succ (succ zero)))
-- Fill it prepending
example-vector = false ∷ (true ∷ (true ∷ []))  -- [false,true,true]
```
in the Agda notation you cannot write
```agda
[false,true,true]
```
but:
```agda
false ∷ (true ∷ (true ∷ []))
```
Namely you first define the empty vector `[]`, then you prepend true `true :: []`, then you prepend true `true :: ...`, then you prepend false `false :: ...`

```agda
data Vector : ℕ → Set where
  []  : Vector zero
  _∷_ : {n : ℕ} → Bool → Vector n → Vector (succ n)
-- :: takes as input:
--    -  a natural number n, 
--       the natural number is inside curly brackets {},
--       and it will be inferred by Agda automatically
--    -  a boolean (the actual input)
--    -  the input list to perform the append onto
--    takes as output:
--    -  a vector of size (succ n)  
```

#### False vector
Let us implement another function built on top of the `Vector` Set.
We would like to have a function such that
```agda
false-vector (succ (succ (succ zero))
```
should evaluate to
```agda
false ∷ (false ∷ (false ∷ [])))
```
Let us define it:
```agda
false-vector : {n : ℕ} → Vector n
false-vector {zero}   = []
false-vector {succ n} = false ∷ false-vector
```
It is defined recursively, we attach `false` on the same structure with `n = n-1`.

```agda
ex : Vector (succ (succ (succ zero)))
ex = false-vector

>> ex
false ∷ (false ∷ (false ∷ [])))
```

In the funciton defined above, we could have used the type infer functionality of Agda:
```agda
false-vector : {n : ℕ} → Vector n
false-vector {zero}   = []
false-vector {succ n} = { }0 ∷ { }1
```
Clicking on `{ }0` and then typing Ctrl-C Ctrl+,:
```agda
>>> Goal: Bool
```
Clicking on `{ }1` and then typing Ctrl-C Ctrl+,:
```agda
>>> Goal: Vector n
```

#### Vector of generic types
```agda
data Vector' (A : Set) : ℕ → Set where
  []  : Vector' A zero
  _∷_ : {n : ℕ} → A → Vector' A n → Vector' A (succ n)
-- * for instance, Vector' Bool (succ (succ zero)) is
--   the type of boolean vectors of length 2.
-- * for instance, Vector' ℕ    (succ (succ zero)) is
--   the type of vectors of length 2 whose entries are natural numbers.
```

#### Map functions:
Here we learn how to apply a function to all elements of a Vector Set
It takes two arguments, a function and a vector, and it will return the vector with elements evaluated with the function.
For instance
```agda
map f (x ∷ (y ∷ (z ∷ []))
```
should evaluate to
```agda
f x ∷ (f y ∷ (f z ∷ []))
```

Firstly we need to introduce the Set type:
Set is the type of all small types; it's the "universe".
- for instance, ℕ : Set
- for instance, Bool : Set
- for instance, ∅ : Set
  
`A : Set` means that A can be an arbitrary type.

```agda
-- map : {A : Set} → {B : Set} → {n : ℕ} → (A → B) → Vector' A n → Vector' B n
map : {A B : Set} {n : ℕ} → (A → B) → Vector' A n → Vector' B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
```
