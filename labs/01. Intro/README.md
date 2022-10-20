
## LBooleans, natural numbers, basic functions:
### Introduction
_Three mottos:_
1. proving = programming
2. conjecturing = specifying
3. induction = recursion

***Agda*** is:
1. a programming language;
2. a proof language.

With Agda you can...
1. ensure correctness of proofs;
2. practically explore Type Theory;
3. appreciate mathematics from a new point of view;
4. verify correctness of programs.

#### Sets
In the beginning Agda does not know about anything, not about numbers, list or even Booleans, we have to teach them.
Let us start creating the Booleans:

```agda
-- This delaration creates a new type, called "Bool".
-- This type has exactly two values: false and true.
data Bool : Set where
  false : Bool
  true  : Bool
```

Sets can also be broader...

```agda
data Color : Set where
  red   : Color
  green : Color
  blue  : Color
  pink  : Color
```

Or even empty (no idea why they can be useful)
```agda
data Empty : Set where
```
Next we will implement a couple of functions with Booleans:
#### Identity Function
```agda
-- First function, let us create the identity function
-- specifically from Bool to Bool (the type that we defined)
-- (n.b. to do the arrow just pretend you are using LaTeX)
--  → = \to
id : Bool → Bool
id x = x -- take x as input and return x, duh
```
In Agda we do not have a special keyword for declaring a function (like `funciton` in C), we just write the name of the function, after the ":" we put the types of the function.

Now that we have our first function we can actually test it by running the code by pressing Ctrl-C Ctrl-N (on Emacs) / Ctrl-C Ctrl-N (on Agdapad).

```agda
>> id false
false
>> id true
true
```

Notice: An important note is about how we write parenthesis on Agda:
* in mathematics we would write _sin(5)_
* in Agda we write `sin 5`
  
In situation where the argument is longer in Agda we write both parenthesis and space:
`id (x + y)`

#### Negation Function
Programming in ADGA you might want to write some template and fill the details later, if you write something like this:

```Agda
neg : Bool → Bool
neg x = ?
```
(Press Ctrl-C Ctrl-L)
```Agda
neg : Bool → Bool
neg x = { }0
```
`{ }0` is a hole where additional agda code will be filled by some argument, in the meantime Agda will ignore in during compiling
(Press Ctrl-C Ctrl-C)
```bash
>> pattern variables to case (empty for split on result): [[]]
```
(Insert x)
```Agda
neg : Bool → Bool
neg true  = { }0
neg false = { }1
```
Agda already came up with a template for us and we can just fill the holes:
```Agda
neg : Bool → Bool
neg true  = {true }0
neg false = {false}1
```
(Now that we filled the holes we need to remove them using Ctrl-C Ctrl-␣)
```Agda
neg : Bool → Bool
neg true  = true
neg false = false
```

#### Defining a constant
```Agda
ex : Bool
ex = neg false
```
which is the value `true`

```Agda
ex : Bool
ex = neg (neg false)
```
which is the value `false`

#### AND function

|   Input 1     | Input 2     | 1 and 2   |
|---------------|-------------|--------|
|   true        | true        | true   |
|   true        | false       | false  | 
|   false       | true        | false  |
|   false       | false       | false  |

```Agda
and : Bool → Bool → Bool -- takes two Bool and returns a Bool
and false y     = false
and true  false = false
and true  true  = true
```
(Ctrl-C Ctrl-V)
```agda
>> and false true
false
>> and true true
true
```

The AND function can be defined differently such that we can write it as `input1 and input2` instead of `and input1 input2`
```agda
_&&_ : Bool → Bool → Bool -- takes two Bool and returns a Bool
&& false y     = false
&& true  false = false
&& true  true  = true

>> true && false
false
```
#### Set with successors: Natural Numbers
How can we define Natural Numbers? They are infinite!
We can use the constructor `succ` which define the successor of a number, with this recursion, any number from zero to infinity are defined: 
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ -- "succ" is short for "successor"

-- The elements (values, inhabitants) of ℕ are:
-- 0: zero
-- 1: succ zero
-- 2: succ (succ zero)
-- 3: succ (succ (succ zero))
-- ...
```
In this way we can define constants of the Natural Set
```agda
one : ℕ
one = succ zero
```
Or we can let Agda infer the type
```agda
one : _
one = succ zero
```

#### Addition
##### Add2
First we define the `add2` function, we take a natural number and just add 2:
```agda
-- add2 of 30 should be 32
add2 : ℕ → ℕ
add2 n = succ (succ n)

>> add2 one
succ (succ (succ zero))
```

We can use the succ constructor to define the predecessor:
```agda
-- "pred one" should be zero.
-- "pred (succ (succ zero))" should be one.
-- "pred zero" should be zero. let us not go into negative numbers for now.
pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

>> pred one
zero
>> pred zero
zero
```
ADGA supports so-called "dependent types": types which depend on values. The prototypical example for a dependent type is the type of vectors of lenght n. In C we have the type int[] of arrays of integers.
Example:
```agda
zero-vector : (n : ℕ) → Vector n
```
Where the lenght is specified by the first argument.

##### General addition
```agda
-- Let us define the addition function
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b =  succ (a + b)
-- example computation
-- two + b               = 
-- succ (succ zero) + b  =
-- succ (succ zero + b)  =
-- succ (succ (zero + b) =
-- succ (succ b)

>> zero + one
one
>> succ (succ zero) + succ (succ (succ zero))
succ (succ (succ (succ (succ zero))))
```

#### Double
One of the core feature of Agda is the possibility of define function recursively:
```agda
-- "double one" should be succ (succ zero)
-- "double two" should be four.
double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

>> double zero
zero
>> double (succ zero)
succ (succ zero)
```
