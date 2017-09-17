universes u v w

-- We can typically set up the simplifier so that most theorems
-- can be proven by induction + simp

@[simp]
lemma reverse_nil {α : Type u} : [].reverse = ([] : list α) :=
rfl

lemma reverse_core {α : Type u} (xs ys : list α) :
    list.reverse_core xs ys = xs.reverse ++ ys :=
by induction xs generalizing ys;
   simp [list.reverse_core, list.reverse]; simp *

@[simp]
lemma reverse_cons {α : Type u} (x : α) (xs : list α) :
    (x :: xs).reverse = xs.reverse ++ [x] :=
by simp [list.reverse, list.reverse_core]; simp [reverse_core]

@[simp]
lemma reverse_concat {α : Type u} (xs ys : list α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse :=
by induction xs generalizing ys; simp *

@[simp]
lemma reverse_reverse {α : Type u} (xs : list α) : xs.reverse.reverse = xs :=
by induction xs; simp *

example {α : Type u} (xs ys : list α) :
    (xs.reverse ++ ys).reverse = ys.reverse ++ xs :=
by simp

@[simp]
lemma map_reverse {α : Type u} {β : Type v} (f : α → β) (xs : list α) :
    list.map f (list.reverse xs) = list.reverse (list.map f xs) :=
by induction xs; simp [*, list.map]

@[simp]
lemma map_id {α : Type u} (xs : list α) : list.map (λ x, x) xs = xs :=
by apply list.map_id

@[simp]
lemma map_map {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (xs : list α) :
    list.map g (list.map f xs) = list.map (g ∘ f) xs :=
by apply list.map_map

example (xs : list ℕ) :
    (list.reverse $
     list.map (λ x, x - 2) $
     list.reverse $
     list.map (λ x, x + 2) xs)
    = xs :=
by simp [(∘)]

-- What lemmas do we need to add to prove the following?
example (xs : list ℕ) :
    let xs := xs.filter (λ x, x > 0) in
    let xs := xs.map (λ x, 3 * x / x) in
    ∀ x ∈ xs, x = 3 :=
by simp {contextual := tt}