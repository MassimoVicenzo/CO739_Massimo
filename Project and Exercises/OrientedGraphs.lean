import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Init.Set
import Mathlib.Data.Set.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-
 ============================================================================================================
 In this section we provide the framework for `Oriented` graphs, we also define `inNeighborSet`s and
 `outNeighborSet`s, and some `lemma`s which can be used to identify the `head`s and `tail`s of an edge.
 ============================================================================================================
-/

section Oriented

variable {G : SimpleGraph V} [Fintype V]

/-
`Oriented G` represents assigning a direction to each edge in a simple graph.
An orientation of a simple graph `G` on a vertex set `V` is a `SimpleGraph` with `head` and `tail` functions
`G.edgeSet → V`. For any `G.Adj u v`, `head` and `tail` return different ends of the edge `uv`.
-/
structure Oriented (G: SimpleGraph V) where

  -- `head` and `tail` functions, edges are directed from the tail to the head of an edge.
  head : G.edgeSet → V
  tail : G.edgeSet → V

  /-
  `h` tells us that the functions `head` and `tail` map every edge with ends `u` and `v`
  to either `u` and `v` or `v` and `u` respectively.
  -/
  h : ∀ e : G.edgeSet, s(head e, tail e) = e

  /-
  `headSymm` and `tailSymm` ensure that `head` and `tail` are both well-defined, i.e.
  order of the vertices (`s(u,v)` vs `s(v,u)`) change the output of `head` and `tail`2
  -/
  headSymm : ∀ u v : V, (hyp : G.Adj u v) → head ⟨s(u,v), hyp⟩ = head ⟨s(v,u), hyp.symm⟩
  tailSymm : ∀ u v : V, (hyp : G.Adj u v) → tail ⟨s(u,v), hyp⟩ = tail ⟨s(v,u), hyp.symm⟩

-- There is something in the linear algebra library already called `Oriented`
-- Might switch it to `Oriented G`

/-
If `Adj u v`, then exactly one of the two vertices is the `head` and the other is the `tail`.
-/
lemma Oriented.head_and_tail_or_tail_and_head (OrG : Oriented G) (h : G.Adj u v):
(OrG.head ⟨s(u,v),h⟩ = u ∧ OrG.tail ⟨s(u,v),h⟩ = v)
∨ (OrG.head ⟨s(u,v), h⟩  = v ∧ OrG.tail ⟨s(u,v),h⟩ = u) := by

  have hyp := OrG.h ⟨s(u,v),h⟩
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hyp
  exact hyp

/-
If `Adj u v`, then `u` is either the `head` or the `tail`.
-/
lemma Oriented.head_or_tail (OrG : Oriented G) (h : G.Adj u v) :
 OrG.head ⟨s(u,v),h⟩ = u ∨ OrG.tail ⟨s(u,v),h⟩ = u  := by

  obtain (h'|h') := OrG.head_and_tail_or_tail_and_head h
  · exact Or.inl h'.1
  · exact Or.inr h'.2

/-
If `Adj u v`, then `v` is either the `head` or the `tail`.
-/
lemma Oriented.head_or_tail' (OrG : Oriented G) (h : G.Adj u v) :
 OrG.head ⟨s(u,v),h⟩ = v ∨ OrG.tail ⟨s(u,v),h⟩ = v  := by

  obtain (h'|h') := OrG.head_and_tail_or_tail_and_head h
  · exact Or.inr h'.2
  · exact Or.inl h'.1

/-
If `Adj u v` and `u` is a `head`, then `v` is a `tail`.
-/
lemma Oriented.tail_of_head (OrG : Oriented G) {h : G.Adj u v} (hhead : OrG.head ⟨s(u,v),h⟩  = u) :
OrG.tail ⟨s(u,v),h⟩ = v := by

  obtain (⟨_,h'⟩|⟨h',_⟩) := OrG.head_and_tail_or_tail_and_head h
  · exact h'
  · exfalso
    rw[hhead] at h'
    exact (G.ne_of_adj h) h'

/-
If `Adj u v` and `u` is a `tail`, then `v` is a `head`.
-/
lemma Oriented.head_of_tail (OrG : Oriented G) {h : G.Adj u v} (htail : OrG.tail ⟨s(u,v),h⟩  = u) :
OrG.head ⟨s(u,v),h⟩ = v := by

  obtain (⟨_,h'⟩|⟨h',_⟩) := OrG.head_and_tail_or_tail_and_head h
  · exfalso
    rw[htail] at h'
    exact (G.ne_of_adj h) h'
  · exact h'

/-
The `outNeighborSet v` is the set of vertices in `V` which are adjacent to `v` and are the head of the edge.
-/
def Oriented.outNeighborSet (OrG : Oriented G) (v : V): Set V :=

  {u : V | ∃ (h: G.Adj v u), OrG.head ⟨s(v,u), h⟩  = u}

/-
The `outDegree v` is the size of `outNeighborSet v`, requires `outNeighborSet v` to be finite.
-/
def Oriented.outDegree (OrG : Oriented G) (v : V) [Fintype ↑(OrG.outNeighborSet v)] : ℕ :=

  (OrG.outNeighborSet v).toFinset.card

/-
The `inNeighborSet v` is the set of vertices in `V` which are adjacent to `v` and are the tail of the edge.
-/
def Oriented.inNeighborSet (OrG : Oriented G) (v : V): Set V :=

  {u : V | ∃ (h: G.Adj v u), OrG.tail ⟨s(v,u), h⟩  = u}

/-
The `outDegree v` is the size of `outNeighborSet v`, requires `outNeighborSet v` to be finite.
-/
def Oriented.inDegree (OrG : Oriented G) (v : V) [Fintype ↑(OrG.inNeighborSet v)] : ℕ :=

  (OrG.inNeighborSet v).toFinset.card

end Oriented

/-
 ======================================================================================================
 In the next section we define `OrientedWalk`s and lay out the foundation to prove that in a finit
 graph, there are only finitely many `OrientedWalk`s which are also `Path`s. Then we prove that for
 fixed and non-fixed endpoints, there exists some `OrientedWalk` which is also a `Path`, such that
 it has the largest length.
 ======================================================================================================
-/

section OrientedWalk

/-
`IsOrientedPath p` respresents a path `p` in a simple graph `G` which was given the orienation `OrG`.
The oriented path has the property that for each vertex `v` in the path, the `next` vertex in the path
is within the `outNeighborSet v`.
-/

variable {G : SimpleGraph V} [fin : Fintype V]

structure SimpleGraph.Walk.IsOrientedWalk (W : G.Walk u v) (OrG : Oriented G): Prop where

  next: if W.length = 0 then True
        else ∀ i ≤ W.length, (W.getVert (i+1)) ∈ OrG.outNeighborSet (W.getVert i)


--theorem PathSupportInjective {u v : V} (P : { p : G.Walk u v | p.IsPath }) : Set.InjOn (SimpleGraph.Walk.support) P := by

--theorem SimpleGraph.SetOfPathsFinite (G : SimpleGraph V) (u: V) (v : V) : (G.Path u v).Finite :=

def FixedOrientedPaths (G : SimpleGraph V) (OrG : Oriented G) (u v : V) : Set (G.Walk u v) :=
  { w : G.Walk u v | w.IsPath ∧ w.IsOrientedWalk OrG}


def SimpleGraph.Walk.IsLongestOrientedPath {u v : V} (W : G.Walk u v) (OrG : Oriented G) : Prop :=
  ∀ (x y : V), ∀ W' ∈ FixedOrientedPaths G OrG x y, W.length ≤ W'.length → W.length = W'.length

def SimpleGraph.Walk.IsLongestOneFixedEndOrientedPath {u v : V} (W : G.Walk u v) (OrG : Oriented G) : Prop :=
  ∀ (y : V), ∀ W' ∈ FixedOrientedPaths G OrG u y, W.length ≤ W'.length → W.length = W'.length


theorem MaximumFixedEndOrientedPath (G : SimpleGraph V) (OrG : Oriented G) (u v : V) :
  ∃ w ∈ FixedOrientedPaths G OrG u v, w.IsLongestOrientedPath OrG := by
  sorry

theorem MaximumOneFixedEndOrientedPath (G : SimpleGraph V) (OrG : Oriented G) (u: V):
  ∃ (v : V), ∃ w ∈ FixedOrientedPaths G OrG u v, w.IsLongestOneFixedEndOrientedPath OrG := by
  sorry

theorem MaximumOrientedPath (G : SimpleGraph V) (OrG : Oriented G):
  ∃ (u v : V), ∃ w ∈ FixedOrientedPaths G OrG u v,
  ∀ (x y : V), ∀ w' ∈ FixedOrientedPaths G OrG x y,
  w.length ≤ w'.length → w.length = w'.length := by

  sorry
  --apply Set.Finite.exists_maximal_wrt

end OrientedWalk

/-
 ===================================================================================================================
 In this section we provide the definition for `Tournament`s based off of the definition for `Oriented` graphs,
 and we prove a result that any `Tournament` has a oriented Hamiltonian path.

 `This section is what is replacing the original theorem I wanted to prove. This proof was much simpler,`
 `and yet, I still was not able to prove it in time for the deadline.`
 ===================================================================================================================
-/

section Tournament

variable (Vfin : Fintype V) [DecidableEq V] (Vnonempty: (@Finset.univ V).Nonempty)

def Tournament (V : Type u) := Oriented (completeGraph V)

/-
We want to show that for oriented completegraph, we can find a Hamiltonian oriented
path. The proof we provide uses induction on the number of vertices, therefore to
avoid issues with types, we show that if `S` is a subset of `V.univ`, then there is
a path `W` which has `W.length = S.card-1`, which we can then conclude meets all
`v∈ S` as `W.IsPath` has `support_nodup`.
-/
theorem ExistsDirectedSpanningPath (n : ℕ) (S : Finset V) (nonempty: S.Nonempty) :
   (h : S.card ≤ n+1) → (OrT : Oriented (completeGraph V)) →
   ∃ (u v : V) (W : (completeGraph V).Walk u v),
   W.length = S.card -1 ∧ W.IsPath ∧ W.IsOrientedWalk (OrT) := by

  -- We proceed by induction with base case `S.card = 1`
  induction n with
  | zero =>
    rintro k OrT
    simp only [zero_add] at *

    -- Since `V` is `nonempty`, we can obtain some vertex `v`
    obtain ⟨v, vmem⟩ := Finset.Nonempty.exists_mem nonempty

    -- We then get the single vertex walk `W := (completeGraph V).Walk v v`
    let W := @SimpleGraph.Walk.nil' V (completeGraph V) v
    have hW : W = SimpleGraph.Walk.nil := sorry
    -- I feel like this should be something simple to prove since I just defined it
    -- literally the line before, but I don't know how to do it.

    -- We use `W` as the walk which satisfies the hypothesis.
    refine ⟨v,v, W , ?_⟩

    constructor
    -- First, we show that the path has length `S.card - 1 = 0`.
    · rw[hW, SimpleGraph.Walk.length_nil]
      have onele := Finset.one_le_card.mpr nonempty
      have singleton := eq_of_le_of_le k onele
      rw [singleton]

    constructor
    -- Next, we show that the walk is indeed a path.
    · apply (SimpleGraph.Walk.isPath_iff_eq_nil W).mpr hW

    -- Finally, we show that the walk is oriented correctly
    · sorry

  | succ k kh =>
    rintro Scard OrT
    rw[add_assoc, one_add_one_eq_two] at Scard

    -- We first split into two cases based on `S.card`.
    by_cases easy : S.card ≤ k+1

    -- First, if `S.card ≤ k+1`, then we can immediately apply the IH.
    · apply kh easy OrT

    -- Otherwise, we have that `S.card = k+2`.
    · push_neg at easy
      have easy : k+2 ≤ S.card := by exact easy
      have Scard : S.card = k+2 := eq_of_le_of_le Scard easy

      -- First, we obtain some vertex `v` by `nonempty`.
      obtain ⟨v, vmem⟩ := Finset.Nonempty.exists_mem nonempty

      -- We can then split the sets of vertices in `S - {v}` into
      -- `inNeighborSet` and `outNeighborSet`.
      let S_in := (OrT.inNeighborSet v) ∩ S
      let S_out := (OrT.outNeighborSet v) ∩ S
        --finset problems
      sorry

      -- Applying induction on each of these sets gives two paths `W_in` and `W_out`.


      -- Now concatinating the paths as `W_in → v → W_out` gives us a spanning path of `S`.


/-
The main theorem is a special case of the previous theorem.
-/
theorem ExistsDirectedHamiltonianPath (OrT : Tournament V):
  ∃ (u v : V) (W : (completeGraph V).Walk u v),
  W.IsHamiltonian ∧ W.IsOrientedWalk OrT := by

  have easy (a : ℕ): a ≤ a + 1 := by simp only [le_add_iff_nonneg_right, zero_le]

  -- Applying the previous theorem gives us a walk `W` with:
  -- `W.length = V.univ.card`
  -- `W.IsPath`
  -- `W.IsOrientedWalk`
  have h := ExistsDirectedSpanningPath ((@Finset.univ V Vfin).card) (@Finset.univ V Vfin) Vnonempty (easy (@Finset.univ V).card) OrT

  -- We use this walk `W` as our Hamiltonian Path.
  -- We can also immediately finish the `W.IsOrientedWalk OrT` goal.
  obtain ⟨u,v,W,⟨hlength,hpath,horiented⟩⟩ := h
  refine ⟨u,v,W,⟨?_,horiented⟩⟩

  -- This leaves the proof that `W.IsHamiltonian`.
  -- Since we know that `hpath : W.IsPath`,
  -- we need only show that `∀ (w : V) : w ∈ W.support`
  apply (hpath.isHamiltonian_iff).mpr
  rintro w

  -- Since `W.IsPath` we have that `support_nodup`, combined with the fact that
  -- `W.length = V.univ.card - 1`, allows us to conclude that
  -- `W.support.toFinset = V.univ`.
  have h: W.support.toFinset = (@Finset.univ V Vfin) := by sorry -- wish I knew how

  apply List.mem_toFinset.mp
  rw [h]

  -- Trivially, `w ∈ V.univ`.
  exact Finset.mem_univ w


end Tournament

/-
 ==================================================================================================================
 In this section, we define a maximal acyclic oriented subgraph of a graph `G` with orientation `OrG`.
 ==================================================================================================================
-/

section MaxAcyclicSubgraph

--def MaximalAcyclicSubgraph (G : SimpleGraph V) (OrG : Oriented G) : SimpleGraph V where

end MaxAcyclicSubgraph

/-
 ================================================================================================================
 In this section we prove a theorem of (Gallai - Roy - Hasse - Vitaver) about colouring graphs, given an
 orientation:
 Given an orientation `OrG` of a simple graph `G`, let `k : ℕ` be the length of the longest
 oriented path in `OrG`, then `χ(G) ≤ k+1`.
 ================================================================================================================
-/

section ColouringTheorem

/-
In the previous section we proved that for each vertex `v` there is a path with finite maximum
length, we use this to define a coloring on the vertex `v`. For each `v : V` we define
`(MaxLengthOrPathColoring G OrG) v` as the length of the longest oriented path starting at `v`.
If the coloring is valid, we can then conclude that `G` is colorable with at most the length of
the longest directed path in `G` + 1 (for length 0 paths).
-/

/-
`MaxLengthOrientedPath G OrG` returns the length of a longest oriented path of `G`.
-/
noncomputable def MaxLengthOrientedPath (G : SimpleGraph V) (OrG : Oriented G) : ℕ :=
  (MaximumOrientedPath G OrG).choose_spec.choose_spec.choose.length


/-
`MaxLengthOrPathColoring G OrG` returns a coloring function of `G`, where each vertex `u` is
colored with a natural number `k` if `k` is the length of the longest path starting at `u`.
-/
noncomputable def MaxLengthOrPathColoring (G : SimpleGraph V) (OrG : Oriented G) : V → ℕ := by
  intro u
  have h := MaximumOneFixedEndOrientedPath G OrG u
  choose _ W _ using h
  exact W.length


/-
A proof that `MaxLengthOrPathColoring G OrG` is indeed a valid coloring.

`So in the middle of this proof I had forgotten a crucial step. You have to take a maximal acyclic subgraph of OrG`
`Which means I need to define that and prove it exist, etc. etc.`
`So I have left this proof out to dry, I will hopefully come back to it at a later date.`
-/
theorem ColoringValid (G : SimpleGraph V) (OrG : Oriented G):
  ∀ (u v : V), G.Adj u v → MaxLengthOrPathColoring G OrG u ≠ MaxLengthOrPathColoring G OrG v := by

  rintro u v adj

  by_contra! abs
  unfold MaxLengthOrPathColoring at abs
  simp only at abs

  let k := MaxLengthOrPathColoring G OrG u
  have hW_u := MaximumOneFixedEndOrientedPath G OrG u
  have hW_v := MaximumOneFixedEndOrientedPath G OrG v

  choose u_end W_u memW_u hW_u using hW_u
  choose v_end W_v memW_v hW_v using hW_v

  have edgeDir := OrG.head_and_tail_or_tail_and_head adj

  rcases edgeDir with (vu|uv)
  · by_cases hv : v ∉ W_u.support <;>  by_cases hu : u ∉ W_v.support
    · sorry
    · sorry
    · sorry
    · sorry

  sorry


end ColouringTheorem
