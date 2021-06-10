import combinatorics.simple_graph.basic
import algebra.big_operators.order
import data.fintype.card
import .constructions
import tactic.ring_exp

open_locale big_operators

/-!
# Hat Games

This module defines the notion of a simple hat game played on an `α` `simple_graph`
with `β` colours, and proves bounds from the literature on this area.

## Main definitions

* `hat_guessing_function` is a structure that represents a guessing function on `α`. The key part
  is `f`, the function itself, but we also have that the function is invariant under
  non-local changes (that is, it can only "see" vertices it's connected to) and that it
  actually guesses hats at all times, as required for a strategy to be winning.

## Implementation notes

* `hat_guessing_function G β` requires `[decidable_eq α]` to do an `ite`; there's likely a way to
  remove it by making it a function `∀ a : α, G.neighbour_set α → β`, which also makes
  `f_local` trivial, but this involves a lot of coercions, which are not fun.

-/

open simple_graph

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

/--
A hat-guessing function is a function that takes in a vertex, and an arrangement of hats, and
tries to guess its own vertex. It must fit two conditions: first, it can only depend on the values
of vertices that are adjacent to it, and it must also guess correctly on at least one vertex.
-/
@[nolint has_inhabited_instance] -- this whole file is dedicated to whether G, β instances exist!
structure hat_guessing_function {α : Type*} (G : simple_graph α) [decidable_eq α] (β : Type*) :=
(f : α → (α → β) → β)
(f_local': ∀ a b : α, ¬G.adj a b → ∀ arr : (α → β), ∀ k : β,
  f a arr = f a (λ x, if x = b then k else arr x))
(f_guesses': ∀ arr : (α → β), ∃ a : α, f a arr = arr a)

namespace hat_guessing_function

variables {α β γ : Type*} {G : simple_graph α} [decidable_eq α] (hg : hat_guessing_function G β)

instance : has_coe_to_fun (hat_guessing_function G β):= ⟨_, f⟩

theorem f_local : ∀ {a b : α}, ¬G.adj a b → ∀ arr : (α → β), ∀ k : β,
hg a arr = hg a (λ x, if x = b then k else arr x) := hg.f_local'

theorem f_guesses : ∀ arr : (α → β), ∃ a : α, hg a arr = arr a := hg.f_guesses'

@[simp] lemma f_eq_coe : hg.f = hg := rfl

@[simp] lemma coe_mk (h₁ h₂) : ⇑(⟨hg, h₁, h₂⟩ : hat_guessing_function G β) = hg := rfl

section basic

/--
If you have a guesser `α → β`, and a function with a right-inverse `f : β → γ`, then
you can create a guesser `α → γ`.
-/
def guesser_of_rinverse {f : β → γ} {g : γ → β} (hf : function.right_inverse g f) :
hat_guessing_function G γ :=
{ f := λ a arr, f $ hg a $ g ∘ arr,
  f_local' := λ _ _ nadj _ _, begin
    rw hg.f_local nadj,
    congr,
    ext,
    split_ifs with h; simp [h]
  end,
  f_guesses' := λ arr, let ⟨a, ha⟩ := hg.f_guesses (g ∘ arr) in ⟨a, by rw [ha, hf]⟩ }

/--
We replace the right-inverse requirement with a surjection. With axiom of choice, being surjective
is equivalent to having a right-inverse; however, this means that this definition is non-computable.
-/
noncomputable def guesser_of_surjection {f : β → γ} (hf : function.surjective f) :
hat_guessing_function G γ := hg.guesser_of_rinverse $ function.right_inverse_surj_inv hf

/--
As expected, if there's a set iso between two types, then guessing on either of them is equivalent.
-/
def guesser_of_equiv (h : β ≃ γ) := hg.guesser_of_rinverse h.right_inv

/-- On an nonempty graph, you can trivially guess 1 colour. -/
def inhabited_guesser [nonempty α] : hat_guessing_function G unit :=
{ f := λ _ _, unit.star,
  f_local' := λ _ _ _ _ _, rfl,
  f_guesses' := by simp }

/--
On a graph with an edge, you can guess 2 colours. The strategy is to take the two vertices, and
one vertex guesses that they are the same colour, whilst the other vertex guesses they aren't.
-/
def edge_guesser {v w : α} (h : G.adj v w) : hat_guessing_function G bool :=
{ f := λ x arr, if v = x then arr w else (if w = x then !(arr v) else ff),
  f_local' := by intros; split_ifs; subst_vars; tauto,
  f_guesses' := λ arr, begin
    by_cases eq : arr w = arr v, --split-ifs doesn't work with binders
      { use v, simp [eq] },
      { use w,
        suffices : !arr v = arr w, by simpa [G.ne_of_adj h],
        cases (arr v); cases (arr w); trivial }
  end }

/--
Subgraphs aren't properly implemented in mathlib yet, but this emulates the mechanism. If you have
that `(a, b)` is an edge in `G` implies that it is an edge in `H`, then we can clearly use the
strategy of `G` on `H` to guess the same amount of colours.
-/
def simple_subgraph {H : simple_graph α} (h : ∀ a b : α, G.adj a b → H.adj a b) :
hat_guessing_function H β :=
{ f := hg,
  f_local' := λ a b nadj, hg.f_local $ mt (h a b) nadj,
  f_guesses' := hg.f_guesses }

end basic

section finite

open finset

variables [fintype β] [fintype γ]

/--
If two β, γ have equal cardinality, and we have an `hat_guessing_function G β`, then there exists
a `hat_guessing_function G γ`; however, we cannot computably extract it. (This is choice-related;
how do we pick which guessing function?)
-/
-- TODO: Make a `trunc` version; however, I don't know the API.
lemma exists_equal_cards_guess (h : ‖β‖ = ‖γ‖) : nonempty (hat_guessing_function G γ) :=
⟨guesser_of_equiv hg (fintype.equiv_of_card_eq h)⟩

/--
The non-computable equivalent to the above statement.
-/
noncomputable def equal_cards_guess (h : ‖β‖ = ‖γ‖) : hat_guessing_function G γ :=
(hg.exists_equal_cards_guess h).some

/-- Auxillary lemmata for `max_guess_lt_card_verts`. -/
lemma size_univ_larger (k : ℕ) : k * (k + 1) ^ (k - 1) < (k + 1) ^ k :=
begin
  cases k,
  { norm_num },
  ring_exp,
  simp [mul_two, pos_iff_ne_zero, pow_ne_zero]
end

lemma cancel_pow {k n : ℕ} : k * (n + 1) ≤ (n + 1) ^ n → k ≤ (n + 1) ^ (n - 1) :=
begin
  cases n,
  { norm_num },
  simp [pow_succ']
end

/--
For `k` vertices on a graph, you can never guess `k+1` colours. We prove this using
simple properties of cardinality, and is essentially a reduction of the case on a
complete graph to all other possible graphs.
-/
theorem best_guess_le_card_verts [fintype α] : hat_guessing_function G (option α) → false := begin
  intro hg,
  let guessed_at := λ a, univ.filter (λ arr, hg a arr = arr a),

  have univ_large : |(univ : finset (α → option α))| = (‖α‖ + 1) ^ ‖α‖, by simp [card_univ],
  -- the approach we take here is to show that individual vertices can guess "relatively few"
  -- configurations, but `univ` (the total number of configurations) is larger than that
  suffices small_guesses : ∀ a : α, |guessed_at a| ≤ (‖α‖ + 1) ^ (‖α‖ - 1),
  { let all_guessed := univ.filter (λ arr, ∃ a : α, hg a arr = arr a),

    have all_are_guessed : univ = all_guessed,
      ext arr,
      simpa using hg.f_guesses arr,

    -- `univ.bUnion guessed_at` is our key object. this is the union over all vertices of what is
    -- guessed at that specific vertex, and for a winning hg-function, this needs to be all of them.
    have bUnion_guessed_at_eq_guessed : all_guessed = univ.bUnion guessed_at,
      apply subset.antisymm,
      { intros arr arr_guessed,
        simpa using hg.f_guesses arr },
      { rintros _ -, rw ←all_are_guessed, apply mem_univ },

    -- we get a contradiction based on this; if there was a HG function, every config would work,
    -- but each individual vertex can only guess so many, and indeed not enough;
    -- then there's no hope of us ever guessing all of the vertices

    have bUnion_small : |univ.bUnion guessed_at| ≤ ‖α‖ * (‖α‖ + 1) ^ (‖α‖ - 1) :=
    calc |univ.bUnion guessed_at| ≤ ∑ a, |guessed_at a| : card_bUnion_le
         ... ≤ ∑ a, (λ _, (‖α‖ + 1) ^ (‖α‖ - 1)) a : sum_le_sum (λ x _, small_guesses x)
         ... ≤ ‖α‖ * (‖α‖ + 1) ^ (‖α‖ - 1) : by simp [card_univ],

    rw [all_are_guessed, bUnion_guessed_at_eq_guessed] at univ_large,
    rw univ_large at bUnion_small,
    have := size_univ_larger (‖α‖), -- unsure why parser wants brackets
    linarith },

  -- now we need to show that all vertices guess a smaller proportion than you'd expect. the main
  -- idea is that a vertex can't see itself (at least), so any pair of configurations that
  -- are different only on themselves can't be distinguished by the hat guessing function.
  -- we model this phenomenon with `similar_arrs`, which is the equivalence class of
  -- vertices under this relation.
  intro a,
  let modify_arr := λ arr : α → option α, λ k, (λ x : α, if x = a then k else arr x),
  let similar_arrs := λ arr, finset.map (⟨modify_arr arr, _⟩) (univ), swap,
    -- `finset.map` requires an embedding, which gives _very_ nice cardinality results
    -- (clearly useful for us!) but we must prove that `modify_arr arr` is injective
    { intros x y fx_eq_fy,
      rw function.funext_iff at fx_eq_fy,
      specialize fx_eq_fy a,
      simp_rw modify_arr at fx_eq_fy,  -- you _can't_ combine both these lines for some reason
      simp only [if_true, eq_self_iff_true] at fx_eq_fy,
      assumption },

  have at_most_similar : |guessed_at a| * (‖α‖ + 1) ≤ |(guessed_at a).bUnion similar_arrs|,
    { rw card_bUnion, simp [card_univ],
    -- `card_bUnion` requires disjointness for equality, which is proved below
    intros arr1 arr1guessed arr2 arr2guessed arr1_ne_arr2,
    rw disjoint_iff_ne,
    intros arr3 arr3_sim_arr1 arr4 arr4_sim_arr2,
    -- our approach is to show that if arr1 ≠ arr2, then they have to be different in a
    -- non-`a` variable, therefore meaning that disjointness holds
    simp only [similar_arrs, if_true, eq_self_iff_true, function.embedding.coe_fn_mk,
               mem_map, mem_fin_range, exists_true_left] at arr3_sim_arr1 arr4_sim_arr2,
    obtain ⟨k, -, arr3_sim_arr1⟩ := arr3_sim_arr1,
    obtain ⟨m, -, arr4_sim_arr2⟩ := arr4_sim_arr2,
    simp_rw [modify_arr] at arr3_sim_arr1 arr4_sim_arr2,

    -- If two colourings are the same except at non-connected vertices, and they guess,
    -- then they must be equal. (TODO: May be worth extracting this, it's a useful proof!)
    contrapose! arr1_ne_arr2 with arr3_eq_arr4, funext x,
    have hg_local := hg.f_local (G.loopless a),
    substs arr3_eq_arr4 arr4_sim_arr2,
    rename arr3_sim_arr1 → arr1_sim_arr2,
    rw [function.funext_iff] at arr1_sim_arr2,
    funext x,

    obtain rfl | h := em (x = a), -- `split-ifs` would be nice, but throws away too much information
    { simp only [true_and, mem_filter, mem_univ] at arr1guessed arr2guessed,
      rw [←arr1guessed, ←arr2guessed, hg_local arr1 k, hg_local arr2 m],
      simp_rw λ t, arr1_sim_arr2 t },
    specialize arr1_sim_arr2 x,
    simp only [h, if_false] at arr1_sim_arr2,
    exact arr1_sim_arr2 },

  have less_than_card_univ : |(guessed_at a).bUnion similar_arrs| ≤ (‖α‖ + 1) ^ ‖α‖,
    by simpa only [←univ_large, card_univ] using card_le_univ _,

  exact cancel_pow (at_most_similar.trans less_than_card_univ)
end

end finite

section complete

/--
Finite complete graphs on `α` have guessing strategies that guess `α` colours. This is a
natural extension of the 2-player result to any finite commutative group.
-/
def complete_guess [fintype α] [add_comm_group α] : hat_guessing_function (complete_graph α) α :=
{ f := λ k arr, k - ∑ x in finset.univ \ {k}, arr x,
  f_local' := λ a b a_eq_b arr _, begin
    change ¬a ≠ b at a_eq_b, push_neg at a_eq_b, subst a_eq_b,
    simp [sub_right_inj, finset.sum_ite_of_false]
  end,
  f_guesses' := λ arr, begin
    let s := ∑ x in finset.univ, arr x,
    use s,
    suffices : s = ∑ x in finset.univ \ {s}, arr x + arr s,
    { nth_rewrite 0 this, abel },
    rw [←(show _ = arr s, from finset.sum_singleton), finset.sum_sdiff],
    exact finset.subset_univ _
  end }

end complete

section lexicographic

/-!
This section follows the proof in Gadoleau & Georgiou 2015 (https://arxiv.org/pdf/1311.2022.pdf)
that the lexicographic product of a graph and a complete graph can create graphs with better
hat-guessing strategies.
-/

/-
The next few lines essentially verify what is assumed in the paper. Locality proofs are often
ignored in the papers as these functions are "clearly" defined to be local; the approach I took
doesn't have this flexibility, sadly.
-/

open finset

variables [fintype γ] [decidable_eq γ]

/-- The β part of the lex guessing function. -/
def guess_β [add_comm_group β] (va : α × γ) (arr : α × γ → β × γ)
  := (hg va.1 (λ x, ∑ m : γ, (arr ⟨x, m⟩).1)) - ∑ m in univ \ {va.2}, (arr ⟨va.1, m⟩).1

/-- The γ part of the lex guessing function. -/
def guess_γ {α} [add_comm_group γ] (va : α × γ) (arr : α × γ → β × γ) :=
  - (∑ m in univ \ {va.2}, (arr ⟨va.1, m⟩).2) - va.2

lemma guess_β_local [add_comm_group β] {a b : α × γ}
  (nadj : ¬(G · γ).adj a b) {arr : α × γ → β × γ} {k : β × γ} :
  hg.guess_β a arr = hg.guess_β a (λ x, if x = b then k else arr x) :=
begin
  rw guess_β,
  rw lex_adj at nadj,
  obtain ⟨v, a⟩ := a,
  congr' 1,
  -- we focus on converting the first part of the expression into the right form
  convert hg.f_local (by tauto) (λ (x : α), ∑ (m : γ), (arr (x, m)).fst) _,
  funext,
  split_ifs with h,
  { subst h }, -- degenerate case of the first part
  -- the rest comes from the lexicographic relations; we use `all_goals` as the sums are the same
  all_goals { rw sum_apply_ite_of_false, tidy }
end

lemma guess_γ_local [add_comm_group γ] {a b : α × γ}
  (h : ¬(G · γ).adj a b) {arr : α × γ → β × γ} {k : β × γ} :
  guess_γ a arr = guess_γ a (λ x, ite (x = b) k (arr x)) :=
by { rw guess_γ, congr' 2, rw sum_apply_ite_of_false, tidy }

/-- Lemma 1 in the Gadouleau paper, generalised to guessing types.  -/
def blow_up [add_comm_group β] [add_comm_group γ] : hat_guessing_function (G · γ) (β × γ) :=
{ f := λ va arr, (hg.guess_β va arr, guess_γ va arr),
  f_local' := λ a b nadj _ k, by rw [hg.guess_β_local nadj, guess_γ_local nadj],
  f_guesses' := λ arr, begin
    obtain ⟨x, hx⟩ := hg.f_guesses (λ x, ∑ m : γ, (arr ⟨x, m⟩).1),
    use ⟨x, -∑ m, (arr ⟨x, m⟩).2⟩,
    ext,
      { have : ∑ m in _, (arr (x, m)).fst = _ := sum_singleton,
        rw [guess_β, hx, sub_eq_iff_eq_add', ←this, sum_sdiff],
        simp },
      have : ∑ m in _, (arr (x, m)).snd = _ := sum_singleton,
      rw [guess_γ, neg_sub_neg, ←this, sub_eq_iff_eq_add', sum_sdiff],
      simp
  end }

end lexicographic

end hat_guessing_function
