namespace imp

def name := string

/- Define a small expression language -/
inductive exp
| val   : ℕ → exp
| var   : name → exp
| plus  : exp → exp → exp
| times : exp → exp → exp

open exp

#eval plus (val 0) (val 0)

def exp.repr : exp → string
| (val n) := "(val " ++ repr n ++ ")"
| (var n) := "(var " ++ n ++ ")"
| (plus a b) := "(plus " ++ exp.repr a ++ " " ++ exp.repr b ++ ")"
| (times a b) := "(times " ++ exp.repr a ++ " " ++ exp.repr b ++ ")"

instance: has_repr exp := ⟨exp.repr⟩
#eval plus (val 0) (val 0)

/- We mark value as [reducible] to make sure type class resolution
   finds instances for (has_add value), (has_mul value), etc. -/
@[reducible]
def value := ℕ

/- A state is just a mapping from names to values. -/
def state := name → value

/- Arithmetic expression evaluator. -/
@[simp]
def eval : exp → state → value
| (val n)       s := n
| (var x)       s := s x
| (plus a₁ a₂)  s := eval a₁ s + eval a₂ s
| (times a₁ a₂) s := eval a₁ s * eval a₂ s

#eval eval (plus (val 3) (var "x")) (λ x, 0)

/- Constant folding -/
@[simp]
def const_fold : exp → exp
| (val n)      := val n
| (var x)      := var x
| (plus a₁ a₂) :=
  match const_fold a₁, const_fold a₂ with
  | val n₁, val n₂ := val (n₁ + n₂)
  | b₁,     b₂     := plus b₁ b₂
  end
| (times a₁ a₂) :=
  match const_fold a₁, const_fold a₂ with
  | val n₁, val n₂ := val (n₁ * n₂)
  | b₁,     b₂     := times b₁ b₂
  end

#eval const_fold (plus (plus (val 2) (val 3)) (var "x"))

/- Prove basic properties about const_fold. -/
lemma const_fold_correct (a : exp) (s : state) : eval (const_fold a) s = eval a s :=
by induction a; simp; cases const_fold a; cases const_fold a_1; simp * at *

lemma const_fold_idemp (a : exp) : const_fold (const_fold a) = const_fold a :=
by induction a; simp; cases const_fold a; cases const_fold a_1; simp * at *

end imp