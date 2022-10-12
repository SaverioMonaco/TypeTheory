## First steps in proving: even and odd numbers:
*"To code is to prove and to prove is to code"*

As always, we need some old Sets and functions already defined:
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data ∅ : Set where

one : ℕ
one = succ zero

two : ℕ
two = succ (succ zero)

four : ℕ
four = succ (succ (succ (succ zero)))
```

#### Lemma: "Even n" \& "Odd n"
We will now define, for any natural number n, "Even n", which we would like to be some statement that can be either true or false. However in Agda we just have types . Even "Even n" is a certain type, namely the type of *witnesses that n is even*.
- The type "Even one" (where one = succ zero) should be an empty type.
- The types "Even zero" and "Even four" should each be inhabited.

```agda
data Even : ℕ → Set where
  -- "the number zero is even"
  Base : Even zero
  -- "for every number n, if n is even, so is succ (succ n)"
  Step : (n : ℕ) → Even n → Even (succ (succ n))
```
These two only statements describe entirely the definition of *even*.

As we defined Even, we can define *Odd*:
```agda
-- "Odd" is a function which maps natural numbers to (newly created) types.
-- Namely, "Odd n" is the type of witnesses that n is odd.
-- For instance, the type "Odd zero" is empty
-- and the type "Odd one" is inhabited.
data Odd : ℕ → Set where
  -- Most basic odd number
  Base' : Odd one
  -- Deducing if numbers are odd if we already know that a
  -- given number is odd.
  Step' : (n : ℕ) → Odd n → Odd (succ (succ n))
```
With that we can state our first lemmas:
1. _For every number n, if a number n is even, then n is even_ (Duh)
"If-then" statements in mathematics correspond to function in Agda
```agda
-- Not a deep lemma, but a good first example
--              if...    then...
lemma : (n : ℕ) Even n → Even n
lemma n p = p
```
`n` is the number, while p is the proof, the witness for which we know this property to be true.

Note: In this lemma there is no notion of even-ness per se, we could have written Odd or any other property, in logic :
```agda
-- for every number n, if n is odd, then n is odd
lemma' : {A : Set} → Odd n → Odd n
lemma' n p = p

-- A → A, A implies A, if A then A
lemma'' : {A : Set} → A → A
lemma'' x = x
```
##### Rosetta Stone between Computing and Logic
| Programming | | Logic / Type theory|
|-------------|-|------------------|
| type A → A of functions | | Statement that A implies A|
|identity function| | Proof of the statement that A implies A

2. _If a number is even, then its successor is odd_
   
```agda
lemma-even-odd : (n : ℕ) → Even n → Odd (succ n)
-- Since we are proving from even to odd, the first number must be zero,
-- while the others must be successor of successors of the previous one
--              number          witness      
lemma-even-odd .zero            Base       = Base'
lemma-even-odd .(succ (succ n)) (Step n p) = Step' (succ n) (lemma-even-odd n p)
```

In English:
  >By induction on n.
  >Base case n = 0: In this case we have to verify that 1 is odd. This is trivial (by Base')
  >Induction step m → 2 + m: In this case we have to verify that, if m is even, then succ m is odd.
  >Because m is even, m is of the form succ (succ n) for some even number n.
  >Hence by the inductive hypothesis, the number succ n is odd.
  >Hence by Step', the number succ (succ (succ n)) is odd.

Let us verify now the following Theorem
> _Every natural number is either even or odd_
We need a function that takes a natural numbe as input and outputs a witness that is even or odd:

First we need to create the conjunction of the two sets:
```agda
-- in Haskell, this type is called "Either"
data _⊎_ (A B : Set) : Set where  
  left  : A → A ⊎ B
  right : B → A ⊎ B
```
To explain the above set:
The type "ℕ ⊎ Bool" contains the following values:
* `left zero`, `left (succ zero)`, `left (succ (succ zero))`, ...
* `right false`, `right true`

```agda
-- "Every natural number is even or odd."
theorem : (n : ℕ) → Even n ⊎ Odd n
theorem zero     = left Base
theorem (succ n) with theorem n
-- We need to came out with a witness that n is even or odd
... | left  p = right (lemma-even-odd n p)
-- Here we would need the lemma lemma-odd-even
... | right q = {!!}
```
