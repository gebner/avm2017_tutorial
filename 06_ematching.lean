universes u v

/-
  Lean contains several automated reasoning techniques from in SMT solvers

  These are available when using SMT tactics with `begin[smt] end`
-/

-- Congruence closure is applied automatically
example {α : Type} (f : α → α) (a b c)
    (h1 : b = a) (h2 : f c = f b) : f a = f c :=
begin[smt] end

-- CC works modulo associativity and commutativity
example {α : Type u} [comm_group α] (a b c : α)
    (h1 : a * b = c) (h2 : c * c = 1) : b * c * a = 1 :=
begin[smt] end


-- Unit propagation works modulo congruence closure
example {α : Type u} [comm_group α] (a b c : α)
    (h1 : a * b = b) (h3 : a*b*a = b → b = 1) : b = 1 :=
begin[smt] end

-- There is no clausification, but specialized rules for various connectives
example {α : Type u} [comm_group α] (a b c : α)
    (h1 : a * b = b) (h3 : a*b*a ≠ b ∨ b = 1) : b = 1 :=
begin[smt] end


-- Heuristic instantiation (E-matching) uses lemmas annotated with @[ematch]
@[ematch]
lemma le_max {α : Type u} [decidable_linear_order α] (a b : α) :
    a ≤ max a b ∧ b ≤ max a b :=
by simp [le_max_left, le_max_right]

-- We can programmatically access ematch-lemmas, get their patterns, etc.
#eval hinst_lemma.mk_from_decl ``le_max >>= hinst_lemma.pp >>= tactic.trace

@[ematch]
def list.max {α : Type u} [decidable_linear_order α] [inhabited α] : list α → α
| []      := default α
| (x::xs) := max x (list.max xs)

local attribute [ematch] le_trans

example (a b c d e : ℕ) : c ≤ [a,b,c,d,e].max :=
begin[smt]
    eblast  -- repeat E-matching until solved
end


/-
  All of the tools above have an API, you can inspect their state from within Lean.
-/
open tactic
example {α : Type u} [comm_group α] (a b c : α)
    (h1 : a * b = b) (h3 : a*b*a ≠ b ∨ b = 1) := by do
ccs ← cc_state.mk_using_hs,
trace "terms known to be equivalent to b:",
b ← get_local `b, trace $ ccs.eqc_of b,
triv