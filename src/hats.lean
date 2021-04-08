import data.set.finite
import data.nat.basic
import data.zmod.basic -- only needed because it makes `ring` work better?!
import combinatorics.simple_graph.basic
import algebra.big_operators.basic
import data.finset
import tactic

open_locale big_operators

set_option pp.beta true

/-!
# Hat Games

This module defines the notion of a hat game on a graph of type `α`, usually `fin n`,
and associated bounds from the literature.

## Main definitions

* `hat_arr` is an arrangement of hats, or more simply, a colouring of the vertices
  (with no other conditions, unlike more common colourings like edge colourings)

* `hat_guessing_function` is a structure that represents a guessing function on `α`. The key part
  is `f`, the function itself, but we also have that the function is invariant under
  non-local changes (that is, it can only "see" vertices it's connected to) and that it
  actually guesses hats at all times, as required for a strategy to be winning.

## Implementation notes

* The API is built to be as general as possible, but most examples focus on hat games on
  `fin n`, as they are very easy to manipulate (for example, with modular arithmetic).
  TODO: maybe there's a simple way to convert a proof on `fin n` to a proof on a `fintype` with
  `card n`. ADDED NOTE: Way easier when graph isos are created.

* `hat_guessing_function G k` is a proof that `k+1` colours can be guessed on `G`. Guessing 0
  colours is absurd and makes everything more annoying to deal with, which is why we use this
  convention. Also, it requires `[decidable_eq α]` to do an `ite`; there's likely a way to remove
  it by making it a function `∀ a : α, G.neighbour_set α → fin (n+1)`, which also makes
  `f_local` trivial, but this involves a lot of coercions, which are not fun.

* `hat_guessing_number G` is the largest number of colours that can be guessed on `G`. This is
  just a natural number, so much easier to use.

-/

open simple_graph

variables {α : Type*} (G : simple_graph α) [decidable_eq α]
/--
An arrangement of hats is just the any function from `α` to all possible hats.
-/
def hat_arr (α : Type*) (n : ℕ) := α → fin n

/--
`simp` doesn't like unfolding `hat_arr` automatically :(
-/
@[simp] lemma hat_arr_def (α : Type*) (n : ℕ) : hat_arr α n = (α → fin n) := rfl

/--
A hat-guessing function is a function that takes in a vertex, and an arrangement of hats, and
tries to guess its own vertex. It must fit two conditions: first, it can only depend on the values
of vertices that are adjacent to it, and it must also guess correctly on at least one vertex.
-/
structure hat_guessing_function (n : ℕ) :=
(f : α → hat_arr α n → fin n)
(f_local: ∀ a b : α, ¬G.adj a b → ∀ arr : hat_arr α n, ∀ k : fin n,
  f a arr = f a (λ x, if x = b then k else arr x))
(f_guesses: ∀ arr : hat_arr α n, ∃ a : α, f a arr = arr a)

/--
The hat-guessing number is the largest possible `n` such that we can guess `n` colours on `G`.
-/
noncomputable def hat_guessing_number :=
  ⨆ (n : ℕ) (hn : nonempty (hat_guessing_function G n)), (n : enat)

/--
Any specific hat-guessing function is a lower-bound on the `hat_guessing_number`.
-/
lemma function_is_lb {G : simple_graph α} {n : ℕ} (hg : hat_guessing_function G n)
  : ↑n <= hat_guessing_number G := le_supr_of_le n $ le_supr_of_le ⟨hg⟩ $ le_refl _

section basic

/--
On an nonempty graph, you can trivially guess 1 colour.
-/
def inhabited_guesser [nonempty α] : hat_guessing_function G 1 :=
{
  f := λ _ _, 1,
  f_local := λ _ _ _ _ _, rfl,
  f_guesses := λ _, by simp
}

lemma inhabited_guesses_one [nonempty α] : ↑1 ≤ hat_guessing_number G
  := function_is_lb $ inhabited_guesser G

/--
On a graph with an edge, you can guess 2 colours. The strategy is to take the two vertices, and
one vertex guesses that they are the same colour, whilst the other vertex guesses they aren't.
-/
def edge_guesser (v w : α) (h : G.adj v w) : hat_guessing_function G 2 :=
{
  f := λ x arr, if x = v then arr w else (if x = w then 1 - arr v else 1),
  f_local := by {intros, split_ifs; subst_vars; solve_by_elim},
  f_guesses := λ arr, by begin
    by_cases are_eq : (arr v = arr w), --split-ifs doesn't work with binders
      { use v, simp [are_eq] },
      { use w, simp [←G.ne_of_adj h, (dec_trivial : ∀ {a b : fin 2}, a ≠ b → 1 - a = b) are_eq] }
  end
}

lemma edge_guesses_two (v w : α) (h : G.adj v w)
  : ↑2 ≤ hat_guessing_number G := function_is_lb $ edge_guesser G v w h


/--
If you have a `hat_guessing_function G (n + 1)`, then you can actually make simpler strategies
for any `k ≤ n`, by `nat.clamp`ing the original strategy.
-/
def hat_guessing_function_is_lb [nonempty α] {n : ℕ} (hg : hat_guessing_function G (n + 1))
: ∀ t : ℕ, t ≤ n → hat_guessing_function G t
| 0 := λ _,
  { f := λ x arr, arr x,
  f_local := λ _ _ _ _ t, t.elim0,
  f_guesses := λ _, by simp }
| (k + 1) := λ h,
  { f := λ x arr, hg.f x (λ x, fin.clamp (arr x) n),
    f_local := λ a b nadj_a_b arr t, by begin
      congr' 1, convert hg.f_local _ _ nadj_a_b _ t,
      funext, split_ifs with x_eq_b, simp [le_of_lt (lt_of_lt_of_le t.is_lt h), fin.clamp],
    end,
    f_guesses := λ arr, by begin
      obtain ⟨a, ha⟩ := hg.f_guesses (λ x, fin.clamp (arr x) _), use a,
      simp_rw ha, simp only [fin.clamp, fin.coe_of_nat_eq_mod, fin.of_nat_eq_coe, coe_coe],
      have : ↑(arr a) ≤ n := le_of_lt (lt_of_lt_of_le (arr a).is_lt h),
      simp [min_eq_left this, nat.mod_eq_of_lt (nat.lt_succ_of_le this)]
    end }

/--
Subgraphs aren't properly implemented in mathlib yet, but this emulates the mechanism. If you have
that `(a, b)` is an edge in `G` implies that it is an edge in `H`, then we can clearly use the
strategy of `G` on `H` to guess the same amount of colours.
-/
def simple_subgraph {n : ℕ} (hg : hat_guessing_function G n) (H : simple_graph α)
  (h : ∀ a b : α, G.adj a b → H.adj a b) : hat_guessing_function H n :=
{
  f := hg.f,
  f_local := λ a b nadj, hg.f_local a b $ mt (h a b) nadj,
  f_guesses := hg.f_guesses
}

end basic

section finite

open finset

variable [fintype α]

instance (n : ℕ) : fintype (hat_arr α n) := pi.fintype

local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

--prefix `𝓗`:10000 := hat_guessing_number

/--
Size of a `hat_arr α n` is the same as the standard size of a function from one set to another.
-/
lemma size_arr {n : ℕ} : ‖hat_arr α n‖ = n ^ ‖α‖ := by simp

/--
Auxillary lemmata for `max_guess_lt_card_verts`.
-/
lemma size_univ_larger (k : ℕ) : k * (k + 1) ^ (k - 1) < (k + 1) ^ k :=
begin
  cases k with k, simp only [nat.succ_pos', one_pow, zero_mul],
  ring_exp, simp [mul_two, pos_iff_ne_zero, pow_ne_zero]
end

lemma cancel_pow (k n : ℕ) : k * (n + 1) ≤ (n + 1) ^ n → k ≤ (n + 1) ^ (n - 1) :=
begin
  cases n, norm_num, intro ineq, rw pow_succ' at ineq, simp [*] at *
end

/--
For `k` vertices on a graph, you can never guess `k+1` colours. We prove this using
simple properties of cardinality, and is essentially a reduction of the case on a
complete graph to all other possible graphs.
-/
theorem best_guess_le_card_verts : hat_guessing_function G (‖α‖+1) → false := begin
  intro hg, let n := ‖α‖,
  let guessed_at := λ a, univ.filter (λ arr, hg.f a arr = arr a),

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

    have univ_large : |univ| = (n + 1) ^ n := size_arr,
    rw [all_are_guessed, bUnion_guessed_at_eq_guessed] at univ_large,
    rw univ_large at bUnion_small,
    have := size_univ_larger n, linarith },

  intro a,

  let modify_arr := λ arr : hat_arr α (n+1), λ k, (λ (x : α), if x = a then k else arr x),

  let similar_arrs : hat_arr α (n+1) → finset (hat_arr α (n+1)) :=
    λ arr, finset.map (⟨modify_arr arr, _⟩) (fin_range (n + 1)),
    -- `finset.map` requires an embedding, which gives _very_ nice cardinality results
    -- (clearly useful for us!) but we must prove that `modify_arr arr` is injective
    swap, { intros x y fx_eq_fy,
    rw function.funext_iff at fx_eq_fy, specialize fx_eq_fy a,
    simp only [modify_arr] at fx_eq_fy, simp only [if_true, eq_self_iff_true] at fx_eq_fy,
    exact fx_eq_fy },

  have at_most_similar : |guessed_at a| * (n + 1) ≤ |(guessed_at a).bUnion similar_arrs|,
    { rw card_bUnion, simp,
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

    -- If two `hat_arr`s are the same except at non-connected vertices, and they guess,
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
  rw ←size_arr, rw ←(@card_univ (hat_arr α (n + 1))), apply card_le_of_subset, apply subset_univ,

apply cancel_pow, exact le_trans at_most_similar less_than_card_univ
end

end finite

section complete

open finset

variable (n : ℕ)

/--
Complete graphs on `n+1` vertices have guessing strategies that guess `n+1` colours. This is a
natural extension of the 2-player result; a vertex `k` guesses that the sum of all hat colours in
the arrangement, mod `n+1`, is `k`, and it must be that one of them is right.
-/
def complete_guess : hat_guessing_function (complete_graph (fin (n+1))) (n+1) :=
{
  f := λ k arr, k - ∑ x in fin_range(n + 1) \ {k}, arr x,
  f_local := λ a b a_eq_b arr _, by begin
    change ¬a ≠ b at a_eq_b, push_neg at a_eq_b, subst a_eq_b,
    rw [sub_right_inj, sum_ite],
    have h : filter (λ x, x = a) (fin_range (n + 1) \ {a}) = ∅, by {ext, simp},
    have h' : filter (λ x, ¬x = a) (fin_range (n + 1) \ {a}) = fin_range (n + 1) \ {a},
      by {ext, simp},
    simp [h, h']
  end,
  f_guesses := λ arr, by begin
    let s := ∑ x in fin_range (n + 1), arr x, use s,
    suffices : s = ∑ x in fin_range (n + 1) \ {s}, arr x + arr s,
      nth_rewrite 0 this, ring,
    rw [←(sum_singleton : _ = arr s), sum_sdiff], simp
  end
}

end complete
