import data.set.finite
import data.nat.basic
import data.zmod.basic -- only needed because it makes `ring` work better?!
import combinatorics.simple_graph.basic
import algebra.big_operators.basic
import data.finset
import tactic
import tactic.rewrite_search.frontend
import .constructions
import .shim

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

variables {α : Type*} (G : simple_graph α) [decidable_eq α]

/--
A hat-guessing function is a function that takes in a vertex, and an arrangement of hats, and
tries to guess its own vertex. It must fit two conditions: first, it can only depend on the values
of vertices that are adjacent to it, and it must also guess correctly on at least one vertex.
(This isn't inhabited for many, many G, β!!)
-/
@[nolint has_inhabited_instance]
structure hat_guessing_function (β : Type*) :=
(f : α → (α → β) → β)
(f_local: ∀ a b : α, ¬G.adj a b → ∀ arr : (α → β), ∀ k : β,
  f a arr = f a (λ x, if x = b then k else arr x))
(f_guesses: ∀ arr : (α → β), ∃ a : α, f a arr = arr a)

section basic

/--
If you have a guesser `α → β`, and a function with a right-inverse `f : β → γ`, then
you can create a guesser `α → γ`.
-/
def guesser_of_rinverse {β γ} {G : simple_graph α} (hg : hat_guessing_function G β) (f : β → γ)
  (g : γ → β) (hf : function.right_inverse g f) : hat_guessing_function G γ :=
{ f := λ a arr, f $ hg.f a $ g ∘ arr,
  f_local := begin
    intros a b nadj_a_b arr k, congr' 1,
    rw hg.f_local a b nadj_a_b (g ∘ arr) (g k),
    congr' 1, ext, split_ifs with h; simp [h]
  end,
  f_guesses := λ arr, by {obtain ⟨a, ha⟩ := hg.f_guesses (g ∘ arr), use a, rw [ha, hf]} }

/--
We replace the right-inverse requirement with a surjection. With axiom of choice, being surjective
is equivalent to having a right-inverse; however, this means that this definition is non-computable.
-/
noncomputable def guesser_of_surjection {β γ} {G : simple_graph α} (hg : hat_guessing_function G β)
  (f : β → γ) (hf : function.surjective f) : hat_guessing_function G γ
  := guesser_of_rinverse hg f (function.surj_inv hf) (function.right_inverse_surj_inv hf)

/--
As expected, if there's a set iso between two types, then guessing on either of them is equivalent.
-/
def guesser_of_equiv {β γ} {G : simple_graph α} (hg : hat_guessing_function G β) (h : β ≃ γ)
:= guesser_of_rinverse hg _ _ h.right_inv

/-- On an nonempty graph, you can trivially guess 1 colour. -/
def inhabited_guesser [nonempty α] : hat_guessing_function G unit :=
{ f := λ _ _, unit.star,
  f_local := λ _ _ _ _ _, rfl,
  f_guesses := by simp }

/--
On a graph with an edge, you can guess 2 colours. The strategy is to take the two vertices, and
one vertex guesses that they are the same colour, whilst the other vertex guesses they aren't.
-/
def edge_guesser (v w : α) (t : G.adj v w) : hat_guessing_function G bool :=
{ f := λ x arr, if v = x then arr w else (if w = x then !(arr v) else ff),
  f_local := by {intros, split_ifs; subst_vars; tauto},
  f_guesses := λ arr, by begin
    by_cases (arr w = arr v), --split-ifs doesn't work with binders
      { use v, simpa },
      { use w, suffices : !arr v = arr w, by simpa [G.ne_of_adj ‹G.adj v w›],
        cases (arr v); cases (arr w); trivial }
  end }

/--
Subgraphs aren't properly implemented in mathlib yet, but this emulates the mechanism. If you have
that `(a, b)` is an edge in `G` implies that it is an edge in `H`, then we can clearly use the
strategy of `G` on `H` to guess the same amount of colours.
-/
def simple_subgraph {β} (hg : hat_guessing_function G β) (H : simple_graph α)
  (h : ∀ a b : α, G.adj a b → H.adj a b) : hat_guessing_function H β :=
{ f := hg.f,
  f_local := λ a b nadj, hg.f_local a b $ mt (h a b) nadj,
  f_guesses := hg.f_guesses }

end basic

variable {G}

section finite

open finset

variable [fintype α]

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

-- if this stops building, check PR #7136
-- replacement should be fintype.equiv_of_card_eq
/--
If two `fintype`s have the same card, and we can guess on one, we can guess on the other. However,
this is non-computable as the isomorphism isn't unique, and so we need to choose one.
-/
noncomputable def equal_cards_guess (hg : hat_guessing_function G α) (β) [fintype β] (h : ‖α‖ = ‖β‖)
  : hat_guessing_function G β :=
  guesser_of_equiv hg (fintype.nonempty_equiv_of_card_eq h).some

/-- Auxillary lemmata for `max_guess_lt_card_verts`. -/
lemma size_univ_larger (k : ℕ) : k * (k + 1) ^ (k - 1) < (k + 1) ^ k :=
begin
  cases k with k, {norm_num},
  ring_exp, simp [mul_two, pos_iff_ne_zero, pow_ne_zero]
end

lemma cancel_pow (k n : ℕ) : k * (n + 1) ≤ (n + 1) ^ n → k ≤ (n + 1) ^ (n - 1) :=
begin
  cases n, {norm_num}, intro ineq, rw pow_succ' at ineq, simp * at *
end

/--
For `k` vertices on a graph, you can never guess `k+1` colours. We prove this using
simple properties of cardinality, and is essentially a reduction of the case on a
complete graph to all other possible graphs.
-/
theorem best_guess_le_card_verts : hat_guessing_function G (option α) → false := begin
  intro hg, let n := ‖α‖,
  let guessed_at := λ a, univ.filter (λ arr, hg.f a arr = arr a),

  have univ_large : |(univ : finset (α → option α))| = (n + 1) ^ n, by simp [card_univ],

  suffices small_guesses : ∀ a : α, |guessed_at a| ≤ (n + 1) ^ (n - 1),
  { let all_guessed := univ.filter (λ arr, ∃ a : α, hg.f a arr = arr a),

    have all_are_guessed : univ = all_guessed,
      ext arr, simpa using hg.f_guesses arr,
    have bUnion_guessed_at_eq_guessed : all_guessed = univ.bUnion guessed_at,
      apply subset.antisymm,
      { intros arr arr_guessed,
        simpa using hg.f_guesses arr },
      { rintros _ -, rw ←all_are_guessed, apply mem_univ },

    have bUnion_small : |univ.bUnion guessed_at| ≤ n * (n + 1) ^ (n - 1),
    { suffices : ∑ a : α, |guessed_at a| ≤ n * (n + 1) ^ (n - 1),
        apply le_trans, apply card_bUnion_le, exact this,
      apply le_trans, apply sum_le_sum,
        { rintros x -, exact small_guesses x },
      -- `card_univ` feels like a simp lemma
      simp [card_univ] },

    rw [all_are_guessed, bUnion_guessed_at_eq_guessed] at univ_large,
    rw univ_large at bUnion_small,
    have := size_univ_larger n, linarith },

  intro a,

  let modify_arr := λ arr : α → option α, λ k, (λ x : α, if x = a then k else arr x),

  let similar_arrs := λ arr, finset.map (⟨modify_arr arr, _⟩) (univ), swap,
    -- `finset.map` requires an embedding, which gives _very_ nice cardinality results
    -- (clearly useful for us!) but we must prove that `modify_arr arr` is injective
    { intros x y fx_eq_fy, rw function.funext_iff at fx_eq_fy, specialize fx_eq_fy a,
      simp_rw [modify_arr] at fx_eq_fy, simp only [if_true, eq_self_iff_true] at fx_eq_fy,
      assumption }, -- you _can't_ combine `simp` and `simp_rw` here for some reason

  have at_most_similar : |guessed_at a| * (n + 1) ≤ |(guessed_at a).bUnion similar_arrs|,
    { rw card_bUnion, simp [card_univ],
    -- `card_bUnion` requires disjointness for equality, which is proved below
    intros arr1 arr1guessed arr2 arr2guessed arr1_ne_arr2,
    rw disjoint_iff_ne, intros arr3 arr3_sim_arr1 arr4 arr4_sim_arr2,
    -- our approach is to show that if arr1 ≠ arr2, then they have to be different in a
    -- non-`a` variable, therefore meaning that disjointness holds
    simp only [similar_arrs, if_true, eq_self_iff_true, function.embedding.coe_fn_mk,
      mem_map, mem_fin_range, exists_true_left] at arr3_sim_arr1 arr4_sim_arr2,
    obtain ⟨k, -, arr3_sim_arr1⟩ := arr3_sim_arr1,
    obtain ⟨m, -, arr4_sim_arr2⟩ := arr4_sim_arr2,
    simp only [modify_arr] at arr3_sim_arr1 arr4_sim_arr2,

    -- If two colourings are the same except at non-connected vertices, and they guess,
    -- then they must be equal. (TODO: May be worth extracting this, it's a useful proof)
    contrapose! arr1_ne_arr2 with arr3_eq_arr4, funext x,
    have hg_local := hg.f_local a a (G.loopless a),
    substs arr3_eq_arr4 arr4_sim_arr2, rename arr3_sim_arr1 → arr1_sim_arr2,
    rw [function.funext_iff] at arr1_sim_arr2, funext x,

    by_cases h : x = a, -- `split-ifs` would be nice, but throws away too much information
    { subst h,
      simp only [true_and, mem_filter, mem_univ] at arr1guessed arr2guessed,
      rw [←arr1guessed, ←arr2guessed, hg_local arr1 k, hg_local arr2 m],
      simp_rw λ x, arr1_sim_arr2 x },
    specialize arr1_sim_arr2 x, simp only [h, if_false] at arr1_sim_arr2, exact arr1_sim_arr2 },

have less_than_card_univ : |(guessed_at a).bUnion similar_arrs| ≤ (n + 1) ^ n,
  rw [←univ_large, card_univ], exact card_le_univ _,

apply cancel_pow, exact le_trans at_most_similar less_than_card_univ
end

end finite

section complete

open finset

/--
Finite complete graphs on `α` have guessing strategies that guess `α` colours. This is a
natural extension of the 2-player result to any finite commutative group.
-/
def complete_guess [fintype α] [add_comm_group α] : hat_guessing_function (complete_graph α) α :=
{ f := λ k arr, k - ∑ x in univ \ {k}, arr x,
  f_local := λ a b a_eq_b arr _, by begin
    change ¬a ≠ b at a_eq_b, push_neg at a_eq_b, subst a_eq_b,
    simp [sub_right_inj, sum_ite_of_false]
  end,
  f_guesses := λ arr, by begin
    let s := ∑ x in univ, arr x, use s,
    suffices : s = ∑ x in univ \ {s}, arr x + arr s,
      nth_rewrite 0 this, simp,
    rw [←(show _ = arr s, from sum_singleton), sum_sdiff], simp
  end }

end complete

section lexicographic

/-!
This section follows the proof in Gadoleau & Georgiou 2015 (https://arxiv.org/pdf/1311.2022.pdf)
that the lexicographic product of a graph and a complete graph can create graphs with better
hat-guessing strategies.
-/

variables {β γ : Type*}

open finset

/-
The next few lines essentially verify what is assumed in the paper. Locality proofs are often
ignored in the papers as these functions are "clearly" defined to be local; the approach I took
doesn't have this flexibility, sadly.
-/

variables [fintype γ] [decidable_eq γ] (hg : hat_guessing_function G β)

/-- The β part of the lex guessing function. -/
def guess_β [add_comm_group β] (hg : hat_guessing_function G β) (va : α × γ) (arr : α × γ → β × γ)
  := (hg.f va.1 (λ x, ∑ m : γ, (arr ⟨x, m⟩).1)) - ∑ m in univ \ {va.2}, (arr ⟨va.1, m⟩).1

/-- The γ part of the lex guessing function. -/
def guess_γ {α} [add_comm_group γ] (va : α × γ) (arr : α × γ → β × γ) :=
  - (∑ m in univ \ {va.2}, (arr ⟨va.1, m⟩).2) - va.2

lemma guess_β_local [add_comm_group β] (a b : α × γ)
  (nadj : ¬(G · γ).adj a b) (arr : α × γ → β × γ) (k : β × γ) :
  guess_β hg a arr = guess_β hg a (λ x, if x = b then k else arr x) :=
begin
  unfold guess_β, obtain ⟨v, a⟩ := a, congr' 1; dsimp only, -- remove after! (I think)

    -- compile-driven maths; this happens to fit the locality requirement!
    -- I assume this is what the colour in our fake arrangement "really is"
    -- but this code may as well be auto-generated
    let n := ∑ (m : γ), (ite ((b.fst, m) = b) k (arr (b.fst, m))).fst, rw lex_adj at nadj,
    convert hg.f_local v b.1 (by tauto) (λ (x : α), ∑ (m : γ), (arr (x, m)).fst) n,
    funext, split_ifs with h, {subst h},
    -- the rest comes from the lexicographic relations
    all_goals { rw sum_apply_ite_of_false, finish }
end

lemma guess_γ_local [add_comm_group γ] (a b : α × γ)
  (h : ¬(G · γ).adj a b) (arr : α × γ → β × γ) (k : β × γ) :
  guess_γ a arr = guess_γ a (λ x, ite (x = b) k (arr x)) :=
by { unfold guess_γ, congr' 2, rw sum_apply_ite_of_false, finish }

/-- Lemma 1 in the Gadouleau paper, generalised to guessing types.  -/
def blow_up [add_comm_group β] [add_comm_group γ]
  : hat_guessing_function (G · γ) (β × γ) :=
{ f := λ va arr, (guess_β hg va arr, guess_γ va arr),
  f_local := λ a b nadj _ k, by {rw [guess_β_local, guess_γ_local]; exact nadj},
  f_guesses := begin
    intro arr, obtain ⟨x, hx⟩ := hg.f_guesses (λ x, ∑ m : γ, (arr ⟨x, m⟩).1),
    use ⟨x, - ∑ m, (arr ⟨x, m⟩).2⟩, ext,
      { unfold guess_β, simp only [hx],
        have : ∑ m in _, (arr (x, m)).fst = (arr (x, -∑ m, (arr (x, m)).snd)).fst := sum_singleton,
        rw [sub_eq_iff_eq_add', ←this, sum_sdiff], simp },
      unfold guess_γ, simp only [neg_sub_neg],
      have : ∑ m in _, (arr (x, m)).snd = (arr (x, -∑ m, (arr (x, m)).snd)).snd := sum_singleton,
      rw [←this, sub_eq_iff_eq_add', sum_sdiff], simp,
  end }

end lexicographic
