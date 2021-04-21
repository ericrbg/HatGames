import algebra.big_operators.basic

open_locale big_operators

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}
variables [comm_monoid β]

open finset

-- I use this file for changes I PR'd into `mathlib`, but haven't arrived yet

/-
∑ (m : γ) in univ \ {a}, (arr (v, m)).fst =
  ∑ (x : γ) in filter (λ (x : γ), (v, x) = b) (univ \ {a}), k.fst +
    ∑ (x : γ) in filter (λ (x : γ), ¬(v, x) = b) (univ \ {a}), (arr (v, x)).fst
-/

@[to_additive] lemma prod_ite_of_false {p : α → Prop} {hp : decidable_pred p} (f g : α → β)
  (h : ∀ x ∈ s, ¬p x) : (∏ x in s, if p x then f x else g x) = (∏ x in s, g x) :=
by { rw prod_ite, simp [filter_false_of_mem h, filter_true_of_mem h] }

@[to_additive] lemma prod_ite_of_true {p : α → Prop} {hp : decidable_pred p} (f g : α → β)
  (h : ∀ x ∈ s, p x) : (∏ x in s, if p x then f x else g x) = (∏ x in s, f x) :=
by { simp_rw ←(ite_not (p _)), apply prod_ite_of_false, simpa }

@[to_additive] lemma prod_apply_ite_of_false {p : α → Prop} {hp : decidable_pred p} (f g : α → γ)
  (k : γ → β) (h : ∀ x ∈ s, ¬p x) : (∏ x in s, k (if p x then f x else g x)) = (∏ x in s, k (g x)) :=
by { simp_rw apply_ite k, exact prod_ite_of_false _ _ h }

@[to_additive] lemma prod_apply_ite_of_true {p : α → Prop} {hp : decidable_pred p} (f g : α → γ)
  (k : γ → β) (h : ∀ x ∈ s, p x) : (∏ x in s, k (if p x then f x else g x)) = (∏ x in s, k (f x)) :=
by { simp_rw apply_ite k, exact prod_ite_of_true _ _ h }

/-finset.filter_true_of_mem : ∀ {α : Type u} {p : α → Prop} [_inst_1 : decidable_pred p]
 {s : finset α}, (∀ (x : α), x ∈ s → p x) → filter p s = s
-/
