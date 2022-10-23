# Agda Tutorials:
0. [Commands](#commands)
1. [Types and Functions](#sets&func)
2. [Framework for defining functions](#framework)
3. [Lists](#lists)
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