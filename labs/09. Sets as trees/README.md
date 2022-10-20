## Sets as trees: introduction to one of the most important models of CZF and to the connection between set theory and type theory

Usual definitions:
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```
#### Sets as trees

In predicative mathematics, we don't have the powerset operation.
```python
P({a,b}) = { ∅, {a}, {b}, {a,b} }
```
The powerset of the set `{a,b}` is the set consisting of `∅, {a}, {b}, {a,b}`

**Goal**: define an Agda type `V` of sets accompanied by functions as:
|            |               |                                                    |
|------------|---------------|----------------------------------------------------|
|`emptySet`  |`: V         ` |    `∅`                                              |
|`pair`      |`: V → V → V ` |    `pair x y = {x,y}`                               |
|`singleton` |`: V → V     ` |    `singleton x = {x}`                              |
|`_∪_`       |`: V → V → V ` |                                                    |
|`powerset`  |`: V → V     ` |    we will fail to implement this function!        |

For this lecture we need to introduce the concept of _binary trees_:
```agda
data BinaryTree (A : Set) : Set where
  -- empty tree
  nil  : BinaryTree A
  -- fork 
  --         left child     right child
  fork : A → BinaryTree A → BinaryTree A → BinaryTree A
```
Example of binary tree:
```agda
{-
  TREES:
  ________________________________

  ∅:      *     empty tree
  ________________________________

  {x,y}:     *                    
            / \
           x   y
  ________________________________

  {{x}, y, {a,b}}:       *
                       / | \
                      *  y  *
                      |    / \
                      x   a   b
-}

exampleTree : {A : Set} → A → A → A → BinaryTree A
exampleTree x y a = fork x nil (fork y (fork a nil nil) nil)

{- Graphical representaiton of the exampleTree
    x
   / \
 nil  y
     / \
    a  nil
   / \
 nil nil 
-}
```
We could either create functions on binary trees:
- function that counts the number of leaves in a binary tree
- function that takes a binary tree of binary trees and flattens the structure in a single binary tree

We can also have the notion of a _mixed tree_.
```agda
data MixedTree (A : Set) : Set where
  nil  : MixedTree A
  -- binary forking
  fork₂ : A → MixedTree A → MixedTree A → MixedTree A
  -- forking with 3 children
  fork₃ : A → MixedTree A → MixedTree A → MixedTree A → MixedTree A
  -- one child forking
  fork₁ : A → MixedTree A → MixedTree A 
  unlabelled-fork₂ : MixedTree A → MixedTree A → MixedTree A
  unlabelled-fork₃ : MixedTree A → MixedTree A → MixedTree A → MixedTree A
  unlabelled-fork₁ : MixedTree A → MixedTree A 
```
But how do we define a general tree?

```agda
-- In Agda there is a hierarchy of sets_
-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : ... : Setω : ...
-- here we need Set₁, the compiler would tell you
-- it is because of the function sup
data V : Set₁ where
  --     index
  sup : {I : Set} → (I → V) → V   -- "sup" is short for "supremum"

emptySet : V
emptySet = sup {⊥} empty-function
  where
  data ⊥ : Set where
  empty-function : ⊥ → V
  empty-function ()
```
The definition of V also seems fishy in that regard: The constructor "sup" returns a fresh element of V for every family of elements of V. But in the beginning, there are no such families to start with! Or are they?

```agda
-- pair x y = {x,y}
pair : V → V → V
pair x y = sup {𝟚} f
  where

  data 𝟚 : Set where
    left  : 𝟚
    right : 𝟚

  f : 𝟚 → V
  f left  = x
  f right = y
```

**Goal**: define a value `N : V` which deserves the name "set of all natural numbers"
natural numbers in set theory:
- `0 := ∅ = {}`
- `1 := { 0 } = { {} }`
- `2 := { 0, 1 } = { {}, {{}} }`
- `3 := { 0, 1, 2 } = { 0, 1, {0,1} } = { {}, {{}}, {{},{{}}} } = succ(2)`
- `succ(n) := n ∪ {n}`

Let us define our `succ` function: `next`
```agda
-- next(x) = x ∪ {x}
{-
  x:     *                next x:  *
       / | \                     / | \     \
     ..........               ..........    x
-}
next : V → V
-- x@(sup {I} f) means that we are using (sup {I} f) 
-- and calling it x
next x@(sup {I} f) = sup {J} g
  where

  data J : Set where
    old : I → J
    new : J

  g : J → V
  g (old i) = f i
  g new     = x
```
fromℕ : ℕ → V
fromℕ zero     = emptySet
fromℕ (succ n) = next (fromℕ n)

-- N as a tree:    *
--              / /  \  \
--             0  1   2  3  4 ...
N : V
N = sup {ℕ} fromℕ

