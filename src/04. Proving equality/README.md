## First steps in proving: equality of natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data _≡_ : ℕ → ℕ → Set where
  refl : {a : ℕ} → (a ≡ a)   -- "reflexivity"
  -- bailout : {a b : ℕ} → (a ≡ b)

{-
theorem : zero ≡ succ zero
theorem = bailout
-}

-- (zero ≡ zero) is the type of witnesses that zero equals zero (this type
-- is inhabited).
-- (zero ≡ succ zero) is the type of witnesses that zero equals succ zero (this type
-- is empty).
lemma : zero ≡ zero    -- \==
lemma = refl

lemma' : (b : ℕ) → ((zero + b) ≡ b)
lemma' b = refl

{-
factorial : ℕ → ℕ
factorial zero = {!!}
factorial (succ n) = {!!}
-}

cong : {x y : ℕ} → (f : ℕ → ℕ) → (x ≡ y) → (f x ≡ f y)
cong = {!!}

lemma'' : (a : ℕ) → ((a + zero) ≡ a)
lemma'' zero     = refl
lemma'' (succ a) = cong succ (lemma'' a)
-- (lemma'' a) is a value of type ((a + zero) ≡ a).
-- What we need is a value of type (succ (a + zero) ≡ succ a).

