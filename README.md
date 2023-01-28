(ITALIANO: Note del corso di Teoria dei Tipi: [qui](./notes/notes.md))

# Agda Tutorials:
0. [Commands](#commands)
1. [Types and Functions](#sets&func)
2. [Framework for defining functions](#framework)
3. [Lists and Vectors](#lists)
4. [Module System](#modules)
6. [Proving lemmas with Witnesses](#wit)
6. [Step for proving lemmas (Equality)](#eq1)
7. [Keyword #1: where](#where)
8. [Keyword #2: rewrite](#rewrite)
9. [Keyword #3: with](#with)
  9.1 [if... else](#ifelse)
10. [Decidability](#dec)
---
| **Command**  |       | **Input Combination** |
|--------------|-------|-----------------------|
| Compile      | $\to$ | Ctrl-C Ctrl-L         |
| Run          | $\to$ | Ctrl-C Ctrl-N         |
| Case Assist  | $\to$ | Ctrl-C Ctrl-C         | 
| Remove hole  | $\to$ | Ctrl-C Ctrl-␣         |
| Type hint    | $\to$ | Ctrl-C Ctrl-,         |
| Automatic Proof Search (Auto) | $\to$ | Ctrl-C Ctrl-A | 	
---
## 1. Basic Types and Functions <a name="sets&func"></a>
#### 1.1 Define Types:
Syntax:
```agda
data $NAME : Set where
    $(elements of the Type)
```
Example: Natural Numbers ℕ
```agda
data ℕ : Set where -- ℕ = \bN
  -- base element (0)
  zero : ℕ
  -- function succ is a generic function from
  -- ℕ → ℕ, in our conception
  -- succ zero              → 1
  -- succ (succ zero)       → 2
  -- succ (succ (succ zero) → 3
  succ : ℕ → ℕ
```

#### 1.2 Define Functions:
Syntax:
```agda
$functionname : Type (Input) → Type (Output)
$functionname ... ($what_the_function_does)
```

Example: Add 1 to a Natural Number 
```agda
add1 : ℕ → ℕ
add1 n = succ n
```

Agda can only support only one argument for its functions, however we can implement multiple arguments as follows:
```agda
add : ℕ → ℕ → ℕ
add zero b = b
add (succ a) b = succ (a + b)
```
By pressing Ctrl-C Ctrl-N we can test the funciton:
```
>> add (succ zero) (succ (succ zero))
succ (succ (succ zero))
```
We just added the successor of zero (one) and the successor of the successor of zero (two) and we got the successor of the successor of the successor of zero.

With the help of the underscores we can suggest Agda where to place our function with respect to the arguments:
```agda
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)
```
Now we can place the two arguments _around_ the "+" sign:
```
>> (succ zero) + (succ (succ zero))
succ (succ (succ zero))
```
## 2. Framework for defining functions:<a name="framework"></a>
Defining functions can be eased by the use of Short-cuts.
Example: AND function for Booleans:
First we define the Boolean type:
```agda
data Bool : Set where
  true  : Bool
  false : Bool
```
Here we start defining the function `_&&_` just as in **1.2**:
```agda
_and_ : Bool → Bool → Bool
a and b = ?
```
If we type the generic arguments and the result as `?` and then compile (**Ctrl-C Ctrl-L**), a _hole_ will be generated:
```agda
_and_ : Bool → Bool → Bool
a and b = { }0
```
We can let Agda find by itself find all the possible case-scenarios of the function `and` by typing in the hole **Ctrl-C Ctrl-C**:
```
pattern variables to case (empty for split on result):
>> a
```
If we type `a` (the first argument) Agda will automatically create all the possible scenarios concerning that variable
```agda
_and_ : Bool → Bool → Bool
true and b  = { }0
false and b = { }1
```
If we repeat it for the `b` argument in the `{ }0` and `{ }1` holes we get to:
```agda
_and_ : Bool → Bool → Bool
true and true   = { }0
true and false  = { }1
false and true  = { }2
false and false = { }3
```
From here we can fill all the hole with the answers we know:
```agda
_and_ : Bool → Bool → Bool
true and true   = {true }0
true and false  = {false }1
false and true  = {false }2
false and false = {false }3
```
The holes can be dissolved by typing **Ctrl-C Ctrl-␣** when inside it.

## 3. Lists and Vectors <a name="lists"></a>
**Lists:**
```agda
-- List is an object of a given type (A)
data List (A : Set) : Set where
  -- base element (empty list)
  []  : List A
  -- prepend function prepend(x, list) = [x,list]
  _∷_ : A → List A → List A

list_example : List ℕ -- with ℕ we declare its element will be naturals
list_example = (succ (succ (succ zero))) ∷ ((succ (succ zero)) ∷ (succ zero ∷ []))
--           = [3,2,1]
```
**Vectors:** (they have a fixed lenght stated in the initialization)
```agda

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

vector_example : Vector ℕ (succ (succ (succ zero)))
vector_example = zero ∷ ((succ zero) ∷ ((succ (succ (succ zero))) ∷ []))
```
For examples of applications of functions to Vectors and Lists see [./EX2_Lists_n_Vectors](EX2_Lists_n_Vectors.agda)

## 4. Module System <a name="modules"></a>
When building large programs it is crucial to be able to split the program over multiple files and to not have to type check and compile all the files for every change. The module system offers a structured way to do this.

Assume you are working in a file called `main.agda` and you need to access Types and Functions in other files `imports/naturals.agda` and `imports/booleans.agda`

```
root
│   main.agda  
│
└───imports
    |   naturals.agda
    |   booleans.agda
```
The files in the import folder in which we define the helping functions and types must be formatted as it follows
```agda
module import.$filename where
  ...
```
For example:
```agda
module imports.naturals where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  one = succ zero

  add1 : ℕ → ℕ
  add1 a = succ a
```
In order to use the code in `main.agda` from the imported folder we need to tell to import them.
In `main.agda`
```agda
open import imports.naturals
open import imports.booleans
```
Now we can use the Types and Functions as it they where in the file:
```
>> add1 zero
succ zero
```

## 5. Proving lemmas with Witnesses <a name="wit"></a>
In Agda (and in Type Theory) proving something means that the relative type of what we want to prove is inhabited. Namely if we want to prove that _"four is an even number"_ we can construct the type _Four is even_ and verify wether it is inhabited or not.

**Example**:

What is the Type _"four is an even number"_?

1.Construct the Even data type which takes a natural number as input and outputs a set:

  ```agda
  data Even : ℕ → Set where
    Base-even : Even zero                               -- "the number zero is even"
    Step-even : (n : ℕ) → Even n → Even (succ (succ n)) -- "for every number n, if n
                                                        -- is even so is
                                                        -- succ (succ n)"
  ```

  The data type `Even` contains two elements:
  - `Base-even` which is a **witness** that zero is even.
  - `Step-even` that states that if we have a witness of the type `Even n`, then it next next successor is Even too, therefore another witness for another number.

  Now if we cast `Even four`, this is a type.

2. We can start proving that zero is even, next that two is even and then that four is even:

```agda
zero-is-even : Even zero
-- the witness that zero is even is the base element of the Even type
zero-is-even = Base-even

two-is-even : Even two
-- if zero is even (which we know as the base even number) then is next
-- next successor is an even too.
-- Step-even takes in input two elements:
--          1. a natural number n
--          2. the witness (proof) that that natural number is even
-- and then it outputs the witness that two is a natural number
two-is-even = Step-even zero Base-even

four-is-even : Even four
four-is-even = Step-even two (two-is-even)
```

Similarly we can prove that _"three is an Odd number"_:

```agda
data Odd : ℕ → Set where
  Base-odd : Odd one
  Step-odd : (n : ℕ) → Odd n → Odd (succ (succ n))

one-is-odd : Odd one
one-is-odd = Base-odd

three-is-odd : Odd three
three-is-odd = Step-odd one Base-odd
```

## 6. Proving lemmas (Equality) <a name="eq1"></a>
In Agda:
- The ordinary equality sign '=' is for definitions.
- In contrast, '≡' is the customary notation in the comunity for _observations, results_.

But first we have to define what '≡' is. Agda does not know about that yet.
Here we define it for natural numbers, but it can be easily extended for any set.
```agda
data _≡_ : ℕ → ℕ → Set where
  -- every given thing is equal to itself
  refl : {a : ℕ} → (a ≡ a)   -- "reflexivity"
```
The only property we require from `≡` is _refleivity_, namely that for every number a, a is equal to a.

Just from this only property, the other basic properties can be defined:
1. **congruence**: If x and y are equal, any function applied to them must return equal values:
```agda
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
```
2. **symmetry**: If x is equal to y, y is equal to x:
```agda
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl
```
3. **transitivity**: If x is equal to y and y is equal to z, x is equal to z:
```agda
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p
```
#### Example 1: Proving (a + zero) ≡ a
First we need to define the basic stuff:
```agda
-- Natural Numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Addition
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

-- Equality
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

-- Equality: Congruence Property
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Equality: Symmetry Property
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

-- Equality: Transitivity Property
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

```
Now we go to proving the lemma:
1. Name the lemma and state what you want to prove:
```
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
```
2. Add the general template:
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = ?
```
3. Compile (Ctrl-C Ctrl-L):
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = { }0
```
This created a hole which can be filled anytime

4. Try a case split, since we only have a single parameter (a) we split a
(Inside the hole: Ctrl-C Ctrl-C)
```
pattern variables to case (empty for split on result): a
```
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = { }0
lemma-+-zero (succ a) = { }1
```
5. Get some insights of the holes:
(Inside the hole 0, Ctrl-C Ctrl-,)
```
Goal: zero ≡ zero
```
Here we need to prove something we already define in `≡`, namely `refl`
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = {refl }0
lemma-+-zero (succ a) = { }1
```
(Inside the hole 1, Ctrl-C Ctrl-,)
```
Goal: succ (a + zero) ≡ succ a
```
Which is basically the lemma we want to prove, but with succ in front of both term, this calls for congruence:
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = {refl }0
lemma-+-zero (succ a) = {cong succ (lemma-+-zero a) }1
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = {refl }0
lemma-+-zero (succ a) = {cong succ (lemma-+-zero a) }1
 ```

6. Remove the holes with Ctrl-C Ctrl-␣
```agda
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
 ```

The holes will be eliminated only if the demonstration is consistent, now that this lemma is considered proven we can use it to proves other lemmas and so on...

#### Example 2: A more complicated example: 
Assuming we also demonstrated the following lemma:
```agda
lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)
 ```
Now we want to demonstate the commutative property of the addition:
```agda
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = ?
```
(Case split in a)
```agda
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero b = { }0
lemma-+-commutative (succ a) b = { }1
```
`zero` case asks for the following proof (Ctrl-C Ctrl-,):
```
Goal: (b : ℕ) → b ≡ (b + zero)
```
Which is quite the `lemma-+-zero` but on the other way around:
```agda
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b = { }0
```
The next hole is rather less trivial, it asks for:
```
Goal: succ (a + b) ≡ (b + succ a)
```
We basically need to go from the left-hand side `succ (a + b)` to the right-hand side `(b + succ a)` using only lemmas and properties we already demonstrated/defined.
For this example, the steps are:
1. `succ (a + b) ---> succ (b + a)` thanks to `lemma-+-commutative a b`
2. `succ (b + a) ---> (a + succ b)` thanks to `symm lemma-+-succ b a`
This translates to:
```agda
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b = trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))
```
For other demonstrations of lemmas about equality see [./EX4_Equality.agda](EX4_Equality.agda)

## 7. Special keyword #1 : where <a name="where"></a>
`where` is the first special keyword, is use is to **carry simple lemmas into a bigger demonstration**. Let us see it with an example:

Suppose we already introduced Natural Numbers `Nat`, the operation of addition `_+_` and the equality relation `_≡_`:

```agda
-- We want to demonstrate the trivial folowing relation
theorem : {a : ℕ} → (succ a + a) ≡ succ (a + a)
theorem {a} = ?
```

To demonstare it, `cong` property of the equivalence may come in handy:

```agda
cong : {A : Set} → {x y : A} → (f : A → A) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

theorem : {a : ℕ} → (succ a + a) ≡ succ (a + a)
theorem {zero}   = refl
theorem {succ a} = cong succ refl
```

We could have written the above demonstration using `where`:

```agda
theorem' : {a : ℕ} → (succ a + a) ≡ succ (a + a)
theorem' {zero} = refl
theorem' {succ a} = cong' succ refl -- at this line cong' is not defined, 
                                    -- we carry its definition below using
                                    -- with:
  where
  cong' : {A : Set} → {x y : A} → (f : A → A) → (x ≡ y) → (f x ≡ f y) 
  cong' f refl = refl
```

## 8. Special keyword #2 : rewrite <a name="rewrite"></a>

???

## 9. Special keyword #3 : with <a name="with"></a>


`with` is used to consider many possibilities a data type may have. Also it is almost essential to some recursive demonstrations:

As an example, let us demonstrate that a given number is either even or odd.

Let us define the required types:

```agda
data Even : ℕ → Set where
  base-even : Even zero -- base element
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero) -- base element
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
````

And let us assume that we already demonstrated that if we have an odd number, its successor is even and viceversa:

```agda
lemma-succ-even : (a : ℕ) → (Even a) → Odd (succ a)
lemma-succ-even zero base-even    = base-odd
lemma-succ-even (succ (succ a)) (step-even p) = step-odd (lemma-succ-even a p)

lemma-succ-odd : (b : ℕ) → (Odd b) → Even (succ b)
lemma-succ-odd (succ zero) base-odd = step-even base-even
lemma-succ-odd (succ (succ b)) (step-odd p) = step-even (lemma-succ-odd b p)
```

```agda
lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) = { }0
```

The goal here is to demonstrate that `succ a` is in `Even a ⊎ Odd a`, but the witness of it (left or right) depends on a, its precedessor. Let us use `with`

```agda
lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
...| left  p = { }0 -- p : Odd a
...| right p = { }1 -- p : Even a
```
Basically we want to demonstrate that succ a` is in `Even a ⊎ Odd a` **given that** (with) lemma-even-odd a holds in the two possible scenarios (Odd a and Even a).

```agda
lemma-even-odd : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
...| left  p = right (lemma-succ-even a p)
...| right p = left (lemma-succ-odd a p)
```

### 9.1. Special keyword #3 : with as if... else <a name="ifelse"></a>
Agda does not really have `if... else` statements, the closest structure to that is `with` in Agda
Example: **Filter list**
```agda
data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Define a function that returns false if
-- the argument integer is zero, truìe otherwise
not-zero : ℕ → Bool
not-zero zero = false
not-zero (succ n) = true

-- Arguments:
-- > A → Bool filer function
-- > List A list to filter
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
...    | true  = x ∷ filter p xs
...    | false = filter p xs

-- natural-vector = [3,0,2,0,1,0]
natural-vector = (succ (succ (succ zero))) ∷ 
                 (zero ∷ (succ (succ zero) ∷
                 (zero ∷ (succ zero ∷ (zero ∷ [])))))
```
```
>> filter not-zero natural-vector
succ (succ (succ zero)) ∷ (succ (succ zero) ∷ (succ zero ∷ []))
```
```agda
-- [3,2,1]
```
Example: **Compare numbers**
You can abstract over multiple terms in a single with-abstraction. To do this you separate the terms with vertical bars `|`.
```agda
data Bool : Set where
  true  : Bool
  false : Bool

data Comparison : Set where
  greater : Comparison
  less    : Comparison
  equal   : Comparison

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_<_ : (a : ℕ) → (b : ℕ) → Bool
zero < zero     = false
zero < (succ b) = true
(succ a) < zero = false
(succ a) < (succ b) = a < b

one = succ zero
two = succ one
three = succ two
four = succ three
five = succ four

compare : ℕ → ℕ → Comparison
compare x y with x < y | y < x
...            | true  | _     = less
...            | _     | true  = greater
...            | false | false = equal
```
```
>> compare two one
greater
>> compare one three
less
>> compare four four
equal
```

## 10. Decidability <a name="dec"></a>
_"Decidability in CS is the property (some properties) that there are machines which are able to find out wether that property holds or not"_
**Decidable properties** : Examples:
- property that a natural number being a prime number
- property that a number to be positive or zero
  
**Non-decidable properties** : Examples:
- property that a given function from ℕ to ℕ to have a zero (for this you would need to simulate the input for all possible natural number, which requires an infinite amount of time, just because to prove that a given function does NOT have a zero, you need to try every possible natural number)

How can this be formalized in Agda?

```agda
-- "Dec A" is the type of witnesses that A is decidable:
data Dec (A : Set) : Set where 
  yes :   A → Dec A 
  no  : ¬ A → Dec A 
```
There are two kinds of inhabitands of that type. If you want to verify `A`, you can (at your own choosing) either verify `A` or `¬ A`.

Example: **Positivity is decidable**
```agda
data Positive : ℕ → Set where
  succs-are-positive : (a : ℕ) → Positive (succ a)

positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = ?
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```
What do we put for `zero` in `?`?
For a moment let us try to fill that hole with a `yes` 
```agda
positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = yes ?
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```
Now in `?` we need a witness that `zero` is positive, which we are not able to.

```agda
data Positive : ℕ → Set where
  succs-are-positive : (a : ℕ) → Positive (succ a)

positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = no  (λ ()) 
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```

```agda
-- "Every inhabited set of natural numbers contains a mininmum"
-- this is true
-- We can picture a function P : ℕ → Set as a set of natural numbers
-- namely, the number n belongs to this set if and only if P n is
-- inhabited, hence P n is the type of witnesses that n belongs to the set.
data _≤_ (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ 
  -- fill this in

-- function that computes the minimum
minimum : (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ
minimum = ?

-- function that verify that the minimum is
-- computed correctly
lemma-minimum-is-computed-correctly
  : (P : ℕ → Set) → (a₀ : ℕ) → (p : P a₀)
  → (n : ℕ) → P n → a₀ ≤ n 
lemma-minimum-is-computed-correctly = ?
```
The two holes cannot be filled, intuitively: if the given minimum given `a₀` is `zero` we are done.
If it is greater than `zero` we would need to check wether there is a smaller number in the Set, which cannot be mechanically done.
