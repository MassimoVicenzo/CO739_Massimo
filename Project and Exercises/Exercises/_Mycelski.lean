/-
Mycelski's theorem : there are triangle-free graphs with arbitrarily large chromatic number.

Enter at your own risk.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring

def sum (G1 : SimpleGraph α) (G2 : SimpleGraph β) (adj' : α → β → Prop) : SimpleGraph (Sum α β) where

Adj := by
  rintro u v
  match (u,v) with
  | (inl x, inl y) => apply G1.Adj x y
  | (inl x , inr y) => apply adj' x y
  | (inr x , inl y) => apply adj' y x
  | (inr x , inr y) => apply G2.Adj x y

symm := sorry
loopless := sorry



theorem exists_triangle_free_chromaticNumber_eq {n m : ℕ} (hn : n + 1 = 2^m) :
    ∃ (G : SimpleGraph (Fin n)), (SimpleGraph.CliqueFree G 3) ∧ G.chromaticNumber = m := by
  sorry
