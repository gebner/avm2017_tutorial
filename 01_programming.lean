/-
  Definitions
-/

def square (m : nat) : nat :=
m * m

-- We can write the same function as a lambda
def square' : ℕ → ℕ :=
λ (m : ℕ), m * m

-- ... or using pattern matching
def square'' : ℕ → ℕ
| 0     := 0
| (m+1) := (m+1) * (m+1)

/-
  Interactive commands
-/

#print square'

#eval square' 12

#check square
#check λ x, square (string.length x)

example (x : string) := square (string.length x)

/-
  Polymorphic definitions
-/

-- types are first-class values
#check ℕ
#check Type
#check Type 1
#check Type 2

universes u
#check Type u

-- polymorphic functions take the type as an extra argument
def squared_length (α : Type u) (xs : list α) : ℕ :=
square (list.length xs)

#eval squared_length ℕ [1, 2, 3]
#eval squared_length ℕ (1 :: 2 :: 3 :: [])
#eval squared_length Type [ℕ, ℤ, string → bool]

-- using curly braces, Lean will fill in the type automatically ("implicit argument")
def squared_length' {α : Type u} (xs : list α) : ℕ :=
square (list.length xs)

#eval squared_length' [1, 2, 3]
#eval @squared_length' ℕ [1, 2, 3]

/-
  Higher-order functions
-/

def twice {α : Type u} (f : α → α) (a : α) : α :=
f (f a)

def twice' {α : Type u} (f : α → α) : α → α :=
f ∘ f

/-
  Recursion
-/

def reverse {α : Type u} : list α → list α
-- pattern matching only applies to the arguments after the colon
| []      := []
| (x::xs) := reverse xs ++ [x]

def nested_list (α : Type u) : ℕ → Type u
| 0     := α
-- recursive calls only have arguments from after the colon
| (n+1) := list (nested_list n)

#reduce nested_list ℕ 5

-- Why does this work?
example (n : ℕ) (xs : nested_list string (n+1)) :=
reverse xs -- xs needs to be a (list _) here, but it's a nested_list!

-- (nested_list _ (n+1)) reduces to a (list _):
#reduce λ n, nested_list string (n+1)
-- This is called "definitional equality".

-- We can of course write functions that return nested_list
def n_singleton {α : Type u} : ∀ n, α → nested_list α n
-- in the base case, the return type is (nested_list α 0) =def= α
| 0     a := a
-- in the step case, the return type is (list (nested_list α n))
| (n+1) a := [n_singleton n a]

/-
  Inductive types
-/

inductive tree (α : Type u)
| leaf (value : α) : tree
| node (left : tree) (right : tree) : tree

#check tree.node (tree.leaf 1) (tree.leaf 3)

/-
  Inductive families
-/

inductive vector (α : Type u) : ℕ → Type u
| nil : vector 0
| cons {n : ℕ} (head : α) (tail : vector n) : vector (n+1)

def vector.head {α} : ∀ {n}, vector α (n+1) → α
| _ (vector.cons hd tl) := hd

#check vector.cons 3 (vector.cons 4 (vector.nil ℕ))
#eval vector.head $ vector.cons 3 (vector.cons 4 (vector.nil ℕ))

/-
  Structures
-/

structure point (α : Type u) :=
(x : α)
(y : α)

def pt : point ℕ := { y := 1, x := 2 }

#eval pt.y
#eval point.y pt

example : point ℕ := point.mk 1 2
example : point ℕ := ⟨1, 2⟩
example := { point . x := 1, y := 2 }
example : point ℕ := { x := 1, y := 2 }

example := { pt with x := 5 }

structure point3 (α : Type u) extends point α :=
(z : α)

example : point3 ℕ := { pt with z := 3 }

/-
  Type classes
-/

-- using square brackets, Lean will fill in the argument using type-class inference
def tree.sum {α : Type u} [has_add α] : tree α → α
| (tree.leaf v)    := v
| (tree.node t s)  := tree.sum t + tree.sum s

instance (α : Type u) : has_append (tree α) :=
{ append := tree.node } -- type classes are just structures

example (t : tree ℕ) (s : tree ℕ) := t ++ s