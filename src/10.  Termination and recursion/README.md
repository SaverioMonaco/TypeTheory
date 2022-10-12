## On termination and well-founded recursion
-- AGDA IN PADOVA

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b      → a < succ b

lemma-half< : (a : ℕ) → half (succ a) < succ a
lemma-half< a = {!!}

_ : half (succ (succ (succ (succ zero)))) ≡ succ (succ zero)
_ = refl

-- We'd like to define the "digits" function, computing the
-- number of binary digits of a given natural number.
-- For instance, "digits 4" should be "3", because "4"
-- is "100" in binary. Also "digits 5" should be "3",
-- because 5 in binary is "101".

-- However, the following code is rejected by Agda because
-- of termination issues:
{-
digits : ℕ → ℕ
digits zero     = zero   -- the binary expansion of 0 is ""
digits (succ n) = succ (digits (half (succ n)))
-}

-- There are five options how to deal with this issue:
-- (1) {-# TERMINATING #-} (this won't work with {-# OPTIONS --safe #-})
-- (2) {-# NON_TERMINATING #-} (this won't work with {-# OPTIONS --safe #-})
-- (3) rewrite function, employ a different algorithm
-- (4) use a poor version of gas
-- (5) use a sophisticated version of gas ("well-founded induction")

module Option-1 where
  {-# TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero   -- the binary expansion of 0 is ""
  digits (succ n) = succ (digits (half (succ n)))

  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = refl

  _ : digits (succ (succ (succ (succ zero)))) ≡ succ (succ (succ zero))
  _ = refl

  _ : digits (succ (succ (succ zero))) ≡ succ (succ zero)
  _ = refl

  {-# TERMINATING #-}
  weird : zero ≡ succ zero
  weird = weird

  data ⊥ : Set where

  {-# TERMINATING #-}
  weird' : ⊥
  weird' = weird'

module Option-2 where
  {-# NON_TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  -- This does not work:
  -- _ : digits (succ (succ (succ (succ zero)))) ≡ succ (succ (succ zero))
  -- _ = refl

  f : (n : ℕ) → digits n ≡ digits n
  f n = refl

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

  _ : digits (succ (succ (succ zero))) ≡ succ (succ zero)
  _ = refl

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

-- Like option (4), but clearly distinguish bailout case from correct results
module Option-4' where
  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just    : X → Maybe X

  succ' : Maybe ℕ → Maybe ℕ
  succ' nothing  = nothing
  succ' (just n) = just (succ n)

  go : ℕ → ℕ → Maybe ℕ
  go zero     gas        = just zero
  go (succ n) zero       = nothing
  go (succ n) (succ gas) = succ' (go (half (succ n)) gas)

  digits : ℕ → Maybe ℕ
  digits n = go n n

  digits' : ℕ → ℕ
  digits' = {!!}

module Option-5 where
  data Acc : ℕ → Set where
    acc : {x : ℕ} → ((y : ℕ) → y < x → Acc y) → Acc x
  -- The type "Acc x" is the type of witnesses that the number x is "accessible".

  -- The number zero is accessible, because all its predecessors (there are none) are.
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

