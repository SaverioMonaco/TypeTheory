## First steps in proving: equality of natural numbers

Define Sets and Function already studied:
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
```

For some reason we want to prove that zero is equal to zero.
The Agda way of proving that is not to use the equality sign'=', but to use the symbol '≡' (\\==).
```agda
-- (zero ≡ zero) is the type of witnesses that 
-- zero equals zero (this type is inhabited).
-- (zero ≡ succ zero) is the type of witnesses that
--  zero equals succ zero (this type is empty).
lemma : zero ≡ zero    -- \==
lemma = refl
```
In Agda:
- The ordinary equality sign '=' is for definitions.
- In contrast, '≡' is the customary notation in the comunity for _observations, results_.

But first we have to define what '≡' is. Agda does not know about that yet.
```agda
data _≡_ : ℕ → ℕ → Set where
  -- every given thing is equal to itself
  refl : {a : ℕ} → (a ≡ a)   -- "reflexivity"
```
Going back to the lemma:
```agda
lemma : zero ≡ zero    -- \==
lemma = refl
```
```agda
-- lemma' is a function which takes as input a natural number b
-- and outputs a witness that b=b
lemma' : (b : ℕ) → ((zero + b) ≡ b)
lemma' b = refl
```
As we defined the addition function, Agda knows about `zero + b = b` but it does not know about `b + zero = b`. Just `refl` will not work.
```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
-- In this case both side are manifestly equal and we can use refl
lemma'' zero     = refl
lemma'' (succ a) = ?
```
What do we put in `?` ?
```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
-- In this case both side are manifestly equal and we can use refl
lemma'' zero     = refl
lemma'' (succ a) = a + zero ≡ a
```
DOES NOT WORK!
What we have written there `a + zero ≡ a` is a type, namely the type of witnesses that `a + zero = a`, this is a non-empty type but it is not useful for filling the hole, in the hole we must not put a type but a witness.

What about recursion?
```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
-- In this case both side are manifestly equal and we can use refl
lemma'' zero     = refl
lemma'' (succ a) = lemma'' a
```
Agda will complain about that. The output of the function needs a type `(a + zero) ≡ a)`, but if we inspect the needed type (Ctrl+C Ctrl+,):
- `(lemma'' a)` is a value of type `((a + zero) ≡ a)`.
- What we need is a value of type `(succ (a + zero) ≡ succ a)`.

Maybe we need another constructor for the equality:
```agda
data _≡_ : ℕ → ℕ → Set where
  -- every given thing is equal to itself
  refl : {a : ℕ} → (a ≡ a)   -- "reflexivity"
  bailout : {a b : ℕ} → (a ≡ b)
```
`bailout` will simply supply equalities for everything we put as inputs, without checking.
We can trick Agda to think that `zero ≡ one`, `two ≡ five`...

We should better **not** hold that kind of power.
We do not need another constructor, what we need is a lemma.

_If we have some equation, and we apply something on both sides, the equation still holds true:_
```agda
-- For any two natural numbers x, y, and for any function f
-- such that goes from N to N, if x and y happend to be equal y
-- then f(x) also equals f(y)
cong : {x y : ℕ} → (f : ℕ → ℕ) → (x ≡ y) → (f x ≡ f y)
cong = {!!}
-- It will be proved at the beginning of the next lecture
```

Once we have the proof, we can prove the main lemma this way:
```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
-- In this case both side are manifestly equal and we can use refl
lemma'' zero     = refl

lemma'' (succ a) = cong succ (lemma'' a)
-- (lemma'' a) is a value of type ((a + zero) ≡ a).
-- What we need is a value of type (succ (a + zero) ≡ succ a).
```



