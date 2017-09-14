universes u

#check true ∧ false ∨ (3 > 1 → 1 < 3)
#check 4 = 2+2
#check ∀ n : ℕ, n ≠ 0 → ∃ m, n = m+1

/-
  Curry-Howard: Propositions as types

  (A proposition is true if there is a value of the type.)
-/

-- Functions are proofs of implication
lemma p1 {a b : Prop} : a → b → a :=
λ ha hb, ha

-- Functions are proofs of forall
lemma p2 : ∀ n : ℕ, n = n :=
λ n, rfl

-- Conjunction is a product (defined as a structure!)
lemma p3 {a b : Prop} (ha : a) (hb : b) : a ∧ b :=
{ left := ha, right := hb }

-- A proof of exists is a pair of witness and proof
lemma p4 (n : ℕ) : ∃ m, n+1 ≤ m :=
⟨n+1, le_refl _⟩

-- Disjunction is a sum type
lemma p5 {a b : Prop} (ha : a) : a ∨ b :=
or.inl ha

/-
  Proofs are "just" expressions; pattern-matching, recursive definitions,
  etc. just work.
-/

lemma p6 {a b : Prop} : a ∨ b → b ∨ a
| (or.inl ha) := or.inr ha
| (or.inr hb) := or.inl hb

lemma p7 {α : Type u} (p q : α → Prop) : (∃ x, p x) → (∃ x, q x) → (∃ x y, p x ∧ q y)
| ⟨x, hpx⟩ ⟨y, hpy⟩ := ⟨x, y, hpx, hpy⟩

lemma p8 : ∀ n : ℕ, 0 ≤ n
| 0 := le_refl _
| (n+1) :=
  let  h1 : n ≥ 0 := p8 n in
  have h2 : n+1 ≥ n, from nat.le_succ n,
  show 0 ≤ n+1, from le_trans h1 h2

/-
  There are two different kinds of "truth values":
   - Prop: types, erased at runtime
   - bool: inductive type with values tt/ff, computable
-/

#check true ∧ false ∨ true
#check tt && ff || tt

-- Lean automatically converts ("coerces") bools into Props
-- x  is coerced into  x = tt
example : (tt : Prop) := rfl

-- We can convert a Prop p into a bool if it is "decidable",
-- i.e. there is a function that computes whether p is true or not
#eval (∀ x ∈ [1,2,3,4], x^2 < x + 10 : bool)

-- decidable is implemented as a typeclass, and you can add your own instances
#print instances decidable

-- Many definitions in Lean use decidable propositions instead of bool:
#eval if ∀ x ∈ [1,2,3,4], x^2 < x + 10 then "ok" else "ko"
#check guard $ ∀ x ∈ [1,2,3,4], x^2 < x + 10
#check list.filter (λ x, x^2 < x + 10)

/-
  Since Prop is erased at runtime, we can use classical logic in Prop without any problems.
-/
example {p : Prop} : p ∨ ¬ p :=
classical.em p

-- Classical logic implies that all propositions are decidable.
local attribute [instance] classical.prop_decidable

-- However we cannot execute definitions that use classical.prop_decidable to
-- construct data, such definitions are then marked as "noncomputable".
noncomputable def find_root (f : ℕ → ℕ) : ℕ :=
if h : ∃ i, f i = 0 then classical.some h else 0