# Agda Tutorials:
0. [Commands](#commands)
1. [Types and Functions](#sets&func)
2. [Framework for defining functions](#framework)
3. [Lists and Vectors](#lists)
4. [Module System](#modules)
5. [if... else](#ifelse)
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

## 5. if... else <a name="ifelse"></a>
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
You can abstract over multiple terms in a single with-abstraction. To do this you separate the terms with vertical bars `|`.
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