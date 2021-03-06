/-
  Tactics produce either a single new tactic state, or fail.

  A tactic state is essentially a list of goals.
-/

lemma p1_1 {a b : Prop} : a → b → b ∧ a :=
begin
  intros ha hb,
  apply and.intro,
  assumption,
  assumption,
end

-- we can freely mix tactics and expressions
lemma p1_2 {a b : Prop} : a → b → b ∧ a :=
λ ha hb, ⟨by assumption, begin assumption end⟩

lemma p1_3 {a b : Prop} : a → b → b ∧ a :=
λ ha hb, ⟨by assumption, by trivial⟩ -- failing tactics are underlined in red

lemma p1_4 {a b : Prop} : a → b → b ∧ a :=
begin
  intros ha hb,
  apply and.intro,
  -- repeats a tactic until it fails
  repeat { assumption },
end

lemma p1_6 {a b : Prop} : a → b → b ∧ a :=
-- ; executes the right tactic on all new goals
by intros ha hb; apply and.intro; assumption

lemma p2 (x : ℕ) : true ∧ x = x :=
-- the orelse (<|>) operator allows backtracking
by constructor; trivial <|> refl

/-
  Rewriting
-/

lemma p3 (f : ℕ → ℕ) (a b : ℕ) (h : f (1 * (0 + a)) = f b) : f a = f (0 + b) :=
begin
-- The `rw` tactic takes a (quantified) equation and rewrites the goal using it
  rw zero_add,
-- You can also pass it multiple equations, and rewrite hypotheses
  rw [zero_add, one_mul] at h,
  assumption,
end

/-
  Induction
-/

lemma p4 {α : Type} (xs ys : list α) : (xs.append ys).length = xs.length + ys.length :=
begin
  induction xs; unfold list.append list.length,
  {rw zero_add},
  {cc}, -- congruence closure modulo associativity-commutativity
end

/-
  Tactics are Lean terms as well ("meta-programs")
-/

open tactic

-- Meta-definitions can use general recursion and
-- call to functions implemented in C++

-- Tactics are written using the `tactic` monad:
meta def tactic.interactive.intro_and_cases : tactic unit := do
h ← intro `h,  -- `h is a name literal
trace "intro_and_cases: ", trace_state, -- printf-style debugging is usually the easiest option
cases h

example (a b : Prop) : a ∧ b → a :=
begin
  intro_and_cases,
  assumption,
end