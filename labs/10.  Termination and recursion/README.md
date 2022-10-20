## On termination and well-founded recursion

Known Sets and functions:
```agda
data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

Let us implement a new function which you might know:
```agda
half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)
```
And you can prove that it is true by using `≡` `refl` property:
```agda
-- PROOF
_ : half (succ (succ (succ (succ zero)))) ≡ succ (succ zero)
_ = refl
```
Instead of defining `≡` we could have imported the equality operator from the standard library:
```agda
open import Relation.Binary.PropositionalEquality -- ≡
```
(Which is defined almost the same way we defined it)

Now we define a funciton that outputs the number of bits needed to represent a given input natural number:
```agda
-- "digits 4" should be "3", because "4" in binary is "100"
-- "digits 5" should also be "3" because "5" in binary is "101"
digits : ℕ → ℕ
digits zero     = zero   -- the binary expansion of 0 is ""
-- one more than the digits of half its number
digits (succ n) = succ (digits (half (succ n)))
```
If you write in Agda a function like this, it would not be compiled, it has termination problems, it is not fully recursive.
An easier example to understand would be:
```agda
loop ℕ → ℕ
loop n = loop n
```
_Agda rejects functions with infinite loops and it reject function which Agda thinks it has infinite loops_
For example, Agda complains about the `digits` function because it does not know that `half (succ n)` is much smaller than `succ n`.
##### Solution #1: Add a sort of flag:
```agda
{-# TERMINATING #-}
digits : ℕ → ℕ
digits zero     = zero
digits (succ n) = succ (digits (half (succ n)))
```
Here we _promise_ Agda that the function does terminate, quick and easy.

This is easy but it can break mathematics, you can prove things that are false, why not prove that `0=1`? 
```agda
weird : zero ≡ succ zero
 weird = weird
```
This function leads to `Termination checking failed` and will not compile, but if we add our magic flag:
```agda
{-# TERMINATING #-}
weird : zero ≡ succ zero
weird = weird
```
It now runs smoothly, and `zero ≡ one`.
Another example is:
```agda
data ⊥ : Set where

{-# TERMINATING #-}
weird' : ⊥
weird' = weird'
```
This can be easily misused, hence there exists a flag to put Agda in a so called _safe mode_, just put this at the beginning of the file:
```agda
{-# OPTIONS --safe #-}
```
Which prevents Agda to use tools that are likely to break mathematics.

##### Solution #2: NON_TERMINATING flag
Here we explicitly remark the function as non-terminating, this will compile everything as long as the function is not actually used, for fear that Agda will get stuck in a infinite loop.
```agda
{-# NON_TERMINATING #-}
digits : ℕ → ℕ
digits zero     = zero
digits (succ n) = succ (digits (half (succ n)))
```

##### Solution #3: Change algorithm
Not an option which can be always available

```agda
module Option-3 where
  data Bin : Set where
  [] : Bin
  _O : Bin → Bin
  _I : Bin → Bin
  -- For instance: The number 6 (binary 110) is encoded as [] I I O.
  -- This is a shorthand for _O (_I (_I [])).

  decode : Bin → ℕ
  decode xs = {!!}

  succ' : Bin → Bin
  succ' []     = [] I
  succ' (xs O) = xs I
  succ' (xs I) = (succ' xs) O

  encode : ℕ → Bin
  encode zero     = []
  encode (succ n) = succ' (encode n)

  length : Bin → ℕ
  length []     = zero
  length (xs O) = succ (length xs)
  length (xs I) = succ (length xs)

  digits : ℕ → ℕ
  digits n = length (encode n)
```

##### Solution #4: Use a poor version of GAS
In the first algorithm we introduce a parameter `gas` which gives the upperbound on how long we are willing to do the recursion.
```agda
module Option-4 where
  digits : ℕ → ℕ
  digits n = go n n
    where
    go : ℕ → ℕ → ℕ
    go zero     gas        = zero
    go (succ n) zero       = zero   -- bailout case (*)
    go (succ n) (succ gas) = succ (go (half (succ n)) gas)

  _ : digits (succ (succ (succ zero))) ≡ succ (succ zero)
  _ = refl

  _ : digits (succ (succ (succ (succ zero)))) ≡ succ (succ (succ zero))
  _ = refl

  -- NOTE: This solution works, but is brittle. It depends on supplying a sufficient
  -- amount of initial gas, to ensure that the bailout clause (*) is never reached.
  -- This should be proven. Later, proofs about properties of digits will always be
  -- encumbered by having to deal with gas.

  -- This is surprisingly hard to prove:
  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = {!!}
```
Or
```agda
-- Like option (4), but clearly distinguish bailout case from correct results
module Option-4' where
  data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X → Maybe X

  succ' : Maybe ℕ → Maybe ℕ
  succ' nothing = nothing
  succ' (just n) = just (succ n)

  go : ℕ → ℕ → Maybe ℕ
  -- no problem here
  go zero gas = just zero
  -- ran out of gas, this is a problem, wrong result
  go (succ n) zero = nothing
  go (succ n) (succ gas) = succ' (go (half (succ n)) gas)

  digits : ℕ → Maybe ℕ
  digits n = go n n

  digits' : ℕ → ℕ
  digits' = {!!}
```
##### Solution #5: Change algorithm
__Genera idea__: Have Solution #4 as a starting point but instead of pick some initial amount of gas with a natural number, we use a custom data type.

```agda
module Option-5 where
  data Acc : ℕ → Set where
    acc : {x : ℕ} → ((y : ℕ) → y < x → Acc y) → Acc x
  -- The type "Acc x" is the type of witnesses
  -- that the number x is "accessible".

  -- The number zero is accessible, because all
  -- its predecessors (there are none) are.
  lemma-zero-is-accessible : Acc zero
  lemma-zero-is-accessible = acc (λ y ())

  lemma-one-is-accessible : Acc (succ zero)
  lemma-one-is-accessible = acc (λ { zero base → lemma-zero-is-accessible })

  lemma-two-is-accessible : Acc (succ (succ zero))
  lemma-two-is-accessible = acc (λ { .(succ zero) base → lemma-one-is-accessible ; .zero (step base) → lemma-zero-is-accessible })

  theorem-ℕ-well-founded : (n : ℕ) → Acc n
  theorem-ℕ-well-founded n = {!!}

  go : (n : ℕ) → Acc n → ℕ
  go zero     gas     = zero
  go (succ n) (acc f) = succ (go (half (succ n)) (f (half (succ n)) (lemma-half< n)))

  digits : ℕ → ℕ
  digits n = go n (theorem-ℕ-well-founded n)

  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = {!!}

  data G : ℕ → ℕ → Set where
    -- naive definition: "digits zero = zero"
    base : G zero zero

    -- naive definition: "digits (succ n) = succ (digits (half (succ n)))"
    step : {n y : ℕ} → G (half (succ n)) y → G (succ n) (succ y)

  lemma-G-is-functional : {a b b' : ℕ} → G a b → G a b' → b ≡ b'
  lemma-G-is-functional = {!!}

  data Σ (X : Set) (Y : X → Set) : Set where
    _,_ : (x : X) → Y x → Σ X Y

  lemma-G-is-total : (a : ℕ) → Σ ℕ (G a)
  lemma-G-is-total a = {!!} , {!!}

  lemma-G-is-computed-by-function : (a : ℕ) → G a (digits a)
  lemma-G-is-computed-by-function a = {!!}
```