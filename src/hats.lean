import data.set.finite -- fin n
import data.zmod.basic -- makes `ring` work better?!
import combinatorics.simple_graph.basic -- simple-graph
import algebra.big_operators.basic -- sum
import data.finset -- sums are over finsets
import tactic -- duh

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
  `card n`.

* `hat_guessing_function G k` is a proof that `k+1` colours can be guessed on `G`. Guessing 0
  colours is absurd and makes everything more annoying to deal with, which is why we use this
  convention. Also, it requires `[decidable_eq α]` to do an `ite`; there's likely a way to remove
  it by making it a function `∀ a : α, G.neighbour_set α → fin (n+1)`, which also makes
  `f_local` trivial, but this involves a lot of coercions, which are not fun.

* `hat_guessing_number G` is the largest number of colours that can be guessed on `G`. This is
  just a natural number, so much easier to use.

-/

open simple_graph
open fin

/--
An arrangement of hats is just the any function from `α` to all possible hats.
-/
def hat_arr (α : Type*) (n : ℕ) := α → fin n

/--
A hat-guessing function is a function that takes in a vertex, and an arrangement of hats, and
tries to guess its own vertex. It must fit two conditions: first, it can only depend on the values
of vertices that are adjacent to it, and it must also guess correctly on at least one vertex.
-/
structure hat_guessing_function {α : Type*} (G : simple_graph α) (n : ℕ) [decidable_eq α] :=
(f : α → hat_arr α (n+1) → fin (n+1))
(f_local: ∀ a b : α, ¬G.adj a b → ∀ arr : hat_arr α (n+1), ∀ k : fin (n+1),
  f a arr = f a (λ x, ite (x = b) k (arr x)))
(f_guesses: ∀ arr : hat_arr α (n+1), ∃ a : α, f a arr = arr a)

section basic

variables {α : Type*} (G : simple_graph α) [decidable_eq α]

/--
On an inhabited graph, you can guess 1 colour.
-/
def all_guess_one [nonempty α] : hat_guessing_function G 0 :=
{
  f := λ _ _, 1,
  f_local := λ _ _ _ _ _, rfl,
  f_guesses := λ _, by simp
}

lemma only_two_mod_two : ∀ {a b : fin 2}, a ≠ b → 1 - a = b := dec_trivial

/--
On a graph with an edge, you can guess 2 colours. The strategy is to take the two vertices, and
one vertex guesses that they are the same colour, whilst the other vertex guesses they aren't.
-/
def edge_guesses_two (v w : α) (h : G.adj v w) : hat_guessing_function G 1 :=
{
  f := λ x arr, ite (x = v) (arr w) (ite (x = w) (1 - arr v) 1),
  f_local := by {intros, split_ifs; subst_vars; solve_by_elim},
  f_guesses := λ arr, by begin
    by_cases are_eq : (arr v = arr w), --split-ifs doesn't work with binders
      { use v, simp [are_eq] },
      { use w, simp [←G.ne_of_adj h, only_two_mod_two are_eq] }
  end
}

/--
If you have `hat_guessing_function G n`, then you can actually make simpler strategies for
any `k ≤ n`, by `nat.clamp`ing the original strategy.
-/
def hat_guessing_function_is_lb {n : ℕ} (hg : hat_guessing_function G n) (k : ℕ) (h : k ≤ n) :
  hat_guessing_function G k :=
{
  f := λ x arr, hg.f x (λ x, clamp (arr x) _),
  f_local := λ a b nadj_a_b arr t, by begin
    congr' 1, convert hg.f_local _ _ nadj_a_b _ t,
    simp_rw [clamp],
    funext, split_ifs with x_eq_b,
      { suffices : ↑t ≤ n, by simp [this],
        have : ↑t < k + 1 := t.2, linarith },
      refl
  end,
  f_guesses := λ arr, by begin
    cases hg.f_guesses (λ x, clamp (arr x) _) with a ha,
    use a, simp_rw ha, simp only [clamp, coe_of_nat_eq_mod, of_nat_eq_coe, coe_coe],
    have : ↑(arr a) ≤ n,
      have : ↑(arr a) < k + 1 := (arr a).2, linarith,
    simp_rw [min_eq_left this, nat.mod_eq_of_lt (nat.lt_succ_of_le this)],
    rw coe_coe_eq_self
  end
}

/--
Subgraphs aren't properly implemented in mathlib yet, but this emulates the mechanism. If you have
that `(a, b)` is an edge in `G` implies that it is an edge in `H`, then we can clearly use the
strategy of `G` on `H`.
-/
def simple_subgraph {n : ℕ} (hg : hat_guessing_function G n) (H : simple_graph α)
  (h : ∀ a b : α, G.adj a b → H.adj a b) : hat_guessing_function H n :=
{
  f := hg.f,
  f_local := λ a b nadj, hg.f_local a b $ mt (h a b) nadj,
  f_guesses := hg.f_guesses
}

end basic

section complete

open finset

variable (n : ℕ)

/--
Complete graphs on `n+1` vertices have guessing strategies that guess `n+1` colours. This is a
natural extension of the 2-player result; a vertex `k` guesses that the sum of all hat colours in
the arrangement, mod `n+1`, is `k`, and it must be that one of them is right.
-/
def complete_guess : hat_guessing_function (complete_graph (fin (n+1))) n :=
{
  f := λ k arr, k - ∑ x in fin_range(n + 1) \ {k}, arr x,
  f_local := λ a b a_ne_b arr _, by begin
    change ¬a ≠ b at a_ne_b, push_neg at a_ne_b, subst a_ne_b, rw sub_right_inj,
    rw sum_ite,
    have h : filter (λ (x : fin (n + 1)), x = a) (fin_range (n + 1) \ {a}) = ∅ := by {ext, simp},
    have h' : filter (λ (x : fin (n + 1)), ¬x = a) (fin_range (n + 1) \ {a}) =
      fin_range (n + 1) \ {a} := by {ext, simp},
    simp [h, h']
  end,
  f_guesses := λ arr, by begin
    let s := ∑ (x : fin (n + 1)) in fin_range (n + 1), arr x, use s,
    suffices : s = ∑ (x : fin (n + 1)) in fin_range (n + 1) \ {s}, arr x + arr s,
      nth_rewrite 0 this, ring,
    have : _ = arr s := sum_singleton,
    rw [←this, sum_sdiff], simp
  end
}

end complete
