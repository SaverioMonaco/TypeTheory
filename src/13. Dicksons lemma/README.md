## Extracting constructive content from classical proofs (illustrated with Dickson's lemma)
module transcript13 where
-- EXTRACTING
--   CONSTRUCTIVE CONTENT
-- FROM
--   CLASSICAL PROOFS
-- \o/

{-
  THEOREM (Dickson's Lemma "D12"):
    For every function α : ℕ → ℕ,
    there are numbers i < j such that α(i) ≤ α(j).
    More precisely, there is a number i such that α(i) ≤ α(1+i).

  PROOF (classical).
    Let i be the minimum of α.
    Then, obviously, α(i) ≤ α(1+i).

  NOTE:
    There is no algorithm "minimum : (ℕ → ℕ) → ℕ".

  EXAMPLE FOR D12:
    α(0) = 5, α(1) = 3, α(2) = 2, α(3) = 20, ...
    then for instance i = 2 works

  THEOREM (Dickson's Lemma "D22"):
    For every functions α, β : ℕ → ℕ,
    there are numbers i < j such that α(i) ≤ α(j) and β(i) ≤ β(j).

  THEOREM (Dickson's Lemma "D32"):
    For every functions α, β, γ : ℕ → ℕ,
    there are numbers i < j such that α(i) ≤ α(j), β(i) ≤ β(j), γ(i) ≤ γ(j).

  THEOREM (Dickson's Lemma "D23"):
    For every functions α, β : ℕ → ℕ,
    there are numbers i < j < k such that α(i)≤α(j)≤α(k) and β(i)≤β(j)≤β(k).
-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

module Classical where
  data ⊥ : Set where

  ⊥-elim : {X : Set} → ⊥ → X
  ⊥-elim ()

  postulate
    oracle : (X : Set) → X ⊎ (X → ⊥)

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → Σ[ a ∈ ℕ ] ((b : ℕ) → α a ≤ α b)
    go a with oracle (Σ[ n ∈ ℕ ] α n < α a)
    ... | inj₁ (n , p) = go n
    ... | inj₂ f       = a , h
        where
        h : (b : ℕ) → α a ≤ α b
        h b with ≤-<-connex (α a) (α b)
        ... | inj₁ αa≤αb = αa≤αb
        ... | inj₂ αb<αa = ⊥-elim (f (b , αb<αa))

    minimum : Σ[ a ∈ ℕ ] ((b : ℕ) → α a ≤ α b)
    minimum = go 0

    theorem : Σ[ i ∈ ℕ ] α i ≤ α (suc i)
    theorem with minimum
    ... | a , f = a , f (suc a)

module ConstructiveButUninformative (⊥ : Set) where
  ¬_ : Set → Set
  ¬ X = X → ⊥

  ⊥-elim : {X : Set} → ⊥ → ¬ ¬ X
  ⊥-elim r = λ k → r

  oracle : (X : Set) → ¬ ¬ (X ⊎ (X → ⊥))
  oracle X = λ k → k (inj₂ (λ x → k (inj₁ x)))

  return : {X : Set} → X → ¬ ¬ X
  return x = λ k → k x

  _⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
  _⟫=_ m f = λ k → m (λ x → f x k)

  escape : ¬ ¬ ⊥ → ⊥
  escape f = f (λ x → x)

  module _ (α : ℕ → ℕ) where
    {-# TERMINATING #-}
    go : ℕ → ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → ¬ ¬ (α a ≤ α b)))
    go a = oracle (Σ[ n ∈ ℕ ] α n < α a) ⟫= g
      where
      g : (Σ[ n ∈ ℕ ] α n < α a ⊎ (Σ[ n ∈ ℕ ] α n < α a → ⊥)) → ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → ¬ ¬ (α a ≤ α b)))
      g (inj₁ (n , p)) = go n
      g (inj₂ f)       = return (a , h)
        where
        h : (b : ℕ) → ¬ ¬ (α a ≤ α b)
        h b with ≤-<-connex (α a) (α b)
        ... | inj₁ αa≤αb = return αa≤αb
        ... | inj₂ αb<αa = ⊥-elim (f (b , αb<αa))

    minimum : ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → ¬ ¬ (α a ≤ α b)))
    minimum = go 0

    theorem : ¬ ¬ (Σ[ i ∈ ℕ ] α i ≤ α (suc i))
    theorem = minimum ⟫= λ (a , f) → f (suc a) ⟫= λ p → return (a , p)

module Constructive where
  module _ (α : ℕ → ℕ) where
    Dickson : Set
    Dickson = Σ[ i ∈ ℕ ] α i ≤ α (suc i)

    open ConstructiveButUninformative Dickson

    thm : Dickson
    thm = escape (theorem α)

module Example where
  α : ℕ → ℕ
  α 0 = 5
  α 1 = 3
  α 2 = 10
  α n = 9

  does-work = Constructive.thm α


{-
  NORMAL APPROACH:
  -- f : X → Y
  function f (x) {
    ...;
    ...;
    return 5;
  }

  -- fetch("https://...").then(function (contents) {...});

  var foo = f(3);
  var bar = f(foo + 5);
  ...;
  ...;

  CONTINUATION-PASSING STYLE:
  -- f : X → ¬ ¬ Y
  function f (x, k) {
    ...;
    ...;
    k(5);
  }

  f(3, function (foo) {
    f(foo + 5, function (bar) {
      ...;
      ...;
    });
  });
-}

