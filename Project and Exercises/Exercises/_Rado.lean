/-
The 'Rado Graph'. All countably infinite random graphs with edge density between 0 and 1 are
isomorphic. (We won't do the random part of the argument.)

Enter at your own risk.
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Countable.defs

variable {V W : Type*}

/-- A graph `G` has the extension property if, for all disjoint finite sets `A,B` of vertices,
  there is a vertex outside `A ∪ B` that is adjacent to everything in `A` and nothing in `B`.
  (A countable graph with this property must be isomorphic to the Rado graph.)-/
def ExtensionProperty (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, Disjoint A B →
    ∃ x, x ∉ A ∧ x ∉ B ∧ ((∀ v ∈ A, G.Adj v x) ∧ (∀ v ∈ B, ¬ G.Adj v x))

/-- Any two countable graphs with the extension property are isomorphic. -/
theorem ExtensionProperty.iso_of_countable [Countable V] [Countable W] {G : SimpleGraph V}
  {H : SimpleGraph W} (hG : ExtensionProperty G) (hH : ExtensionProperty H) : Nonempty (G ≃g H) :=
  sorry


/-- There is a graph on `ℕ` with the extension property. -/
def radoGraphNat : SimpleGraph ℕ := sorry

theorem radoGraphNat_extensionProperty : ExtensionProperty (radoGraphNat) :=
  sorry
