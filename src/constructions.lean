import data.nat.basic
import combinatorics.simple_graph.basic

variables {α β : Type*} (G : simple_graph α)

def lex_product (β) : simple_graph (α × β) :=
{ adj := λ a b, G.adj a.1 b.1 ∨ (a.1 = b.1 ∧ a.2 ≠ b.2),
  sym := by { rintros _ _ (_|⟨_,_⟩); tauto },
  loopless := λ x , by { have := G.loopless x.fst, rintros (_ | _); tauto } }

infix `·`:50 := lex_product

@[simp] theorem lex_adj {G} (a b : α × β) : (G·β).adj a b ↔ G.adj a.1 b.1 ∨ (a.1 = b.1 ∧ a.2 ≠ b.2)
  := iff.rfl
