/-
# The Well-Ordering Principle

This file proves the well-ordering principle from Zorn's lemma - the argument is outlined in
exercise 8.5.19 of Tao's 'Analysis 1'. This is intended to be done *after* `Zorn.lean`.

Just like the 'Zorn' exercise, we set up the proof in a way that makes limited use of mathlib.
We avoid the mathlib API for well-ordered sets, working with the definitions ourselves.
-/

import CO739.Exercises.Zorn

open Set

section WellOrder

/-
The proof shows that each set `X` is well-ordered as follows:

(0) Consider the family `Ω` of pairs `(Y, ≤)` where `Y ⊆ X` and `≤` is well-order of `Y`.
(1) Prove that the 'initial segment or equal' ordering `≼` on `Ω` is a partial order.
(2) Prove that every chain in `Ω` has an upper bound with respect to `≼`.
(3) By Zorn's lemma, conclude that there is a maximal element of `Ω`.
(4) Every maximal element `(Y, ≤)` of `Ω` must have `Y = X`, and therefore give a well-order of `X`.

We formalize this, we take the following approach:

(0) In informal mathematics, this is the easy part! In formalization, this is a design question,
    so needs some real thought.

    In the proof `Ω` is going to be a family on which we will define a global ordering and apply
    Zorn. So ideally, we want to define `Ω` as an object in a framework compatible with our
    statement of Zorn. Typing `#check zorn` gives the following:

    `zorn.{u_1} {α : Type u_1} [Nonempty α] [PartialOrder α]`
      `(h : ∀ (C : Set α), IsChain C → ∃ b, IsUB C b) : ∃ m, IsMaximal m`

    So Zorn applies to some `α : Type*` in which `≤` is defined via a `PartialOrder α`.
    The idiomatic thing, therefore, is to define a type `α` encoding the elements of `X`, and
    then another type `WOSet α` corresponding to `Ω`.

    The elements of `WOSet α` are themselves orderings. These have a different flavour
    from the global ordering; we will be doing things like looking at a pair of elements `x,y`,
    and asking if they are comparable in one well-ordered set versus another.
    It is possible to do this with instances on subtypes, but I want to hold off on this
    kind of dependent-type-theory-heavy approach for now.

    So we actually define `WOSet α` as a custom structure consisting of a set `S`,
    an order relation `le`, and a collection of rules together stating that `le` is only defined on
    pairs in `S`, and forms a well-order of `S`. Because this is a bespoke structure, this
    means we can't hook into all the mathlib API for the `≤` notation, but the advantage is
    that we can make it do exactly what we want, and avoid the headache of a family of relations
    with different domains. We also get some practice in building API for simple structures.

    Before we talk about the rest of the proof, let's define a `WOSet α`.
-/

/-- A structure consisting of a set `S` in `α`, together with a well-ordering `le : α → α → Prop`.
*To keep you on your toes, I've included exactly two mistakes in the definition of this structure.*
Read the whole thing, find them and fix them. -/
@[ext] structure WOSet (α : Type*) where
  -- the underlying set `S`. A more idiomatic/advanced approach would call this set
  -- `carrier` and use coercions to identify a `W : WOSet α` with its underlying set,
  -- but we keep things more elementary for now. If `W` is a `WOSet α`,
  -- then `W.S` is the way to refer to the underlying set of `W` being ordered.
  (S : Set α)

  -- The well-ordering of the underlying set. So if `W : WOSet α`, then `W.le a b` should
  -- be thought of as meaning that '`a ≤ b` in the ordering `≤` given by `W`.'
  (le : α → α → Prop)

  -- this is the axiom that `le a b` only applies to pairs `a,b ∈ S`.
  (supportedOn : ∀ a b, le a b → a ∈ S ∧ b ∈ S)

  -- the ordering `le` is reflexive, transitive and antisymmetric.
  (refl : ∀ a ∈ S, le a a)
  (antisymm : ∀ a b, le a b → le b a → a = b)
  (trans : ∀ a b c, le a b → le b c → le a c)

  --`Mass comment`: changed trans `le c b` to `le b c`

  -- Every nonempty subset of `S` contains a minimum element with respect to `le`.
  (exists_min : ∀ T ⊆ S, T.Nonempty → ∃ b ∈ T, ∀ t ∈ T, le b t)

--`Mass comment`: `T` should be nonempty, not `S`

-- `α` is a type in which `x,y,z` are elements, `S` is a set, and `W,W'` are `WOSet`s.
variable {α : Type*} {x y z : α} {S : Set α} {W W' : WOSet α}

section WOSet

/- Let's define an example of this structure in the easiest case possible;
we should trivially be able to define a well-ordering of the empty set.

To define a term `W : WOSet α`, we need to fill in all the structure fields.
There are quite a few of these fields, but you don't have to copy them all out; if you type
`def WOSet.empty (α : Type*) : WOSet α := _`,
then click on the blue lightbulb that comes up, the lean extension can automatically
build you a skeleton where all the structure fields are written for you. -/
def WOSet.empty (α : Type*) : WOSet α where
  -- the underlying set is the empty set `∅`.
  S := ∅
  -- the ordering is the relation which ignores its two arguments and says 'no'.
  le := fun _ _ ↦ False

  -- it isn't rocket science to show that this choice of `S` and `le` satisfies all the rules.
  -- `simp` can do most of the work; it knows, for example, that the empty set has no elements.
  supportedOn := by simp only [mem_empty_iff_false, and_self, imp_self, implies_true]
  refl := by simp
  antisymm := by simp
  trans := by simp
  exists_min := by
    -- unfortunately, `simp` isn't smart enough for this one.
    -- You need to tell it what the subsets of the empty set are.
    simp [subset_empty_iff]

-- By default, `W` and `W'` refer to well-ordered sets.
variable {W W' : WOSet α}


/-- If `h : W.le x y`, then we want to be able to quickly produce the proofs that
`x ∈ W.S` and `y ∈ W.S`. The following two lemmas let us do this by writing `h.mem_left`
and `h.mem_right` rather than using `W.supportedOn` with underscores. -/
theorem WOSet.le.mem_left (h : W.le x y) : x ∈ W.S :=
  (W.supportedOn x y h).1

theorem WOSet.le.mem_right (h : W.le x y) : y ∈ W.S :=
  (W.supportedOn x y h).2

/-- This lets us write `h.trans h'` instead of `W.trans _ _ _ h h'`. -/
theorem WOSet.le.trans {W : WOSet α} (h : W.le x y) (h' : W.le y z) : W.le x z :=
  W.trans x y z h h'

/-- This lets us write `h.antiysmm h'` instead of `W.antisymm _ _ h h'`. -/
theorem WOSet.le.antisymm (h : W.le x y) (h' : W.le y x) : x = y :=
  W.antisymm x y h h'

/-- The 'less-than' relation induced by a well-ordered set. `W.lt x y` means `W.le x y` and `x ≠ y`.
The lemmas ahead are isomorphic to existing stuff for `≤` and `<` in mathlib,
but it is a good exercise to figure out the proofs yourself, if only once.
Try to use the dot notation we just enabled where possible, rather than
the structure fields of `WOSet` directly. Underscores can get old. -/
def WOSet.lt (W : WOSet α) (x y : α) := W.le x y ∧ x ≠ y

/-- If `h : W.lt x y`, we want to be able to easily say that `W.le x y` and that `x ≠ y`.
We could use `h.1` and `h.2` for this, but it is more readable to allow `h.le` and `h.ne` instead.
These next two lemmas enable this.-/
theorem WOSet.lt.le (h : W.lt x y) : W.le x y :=
  h.1

theorem WOSet.lt.ne (h : W.lt x y) : x ≠ y :=
  h.2

theorem WOSet.lt.trans_le (h : W.lt x y) (h' : W.le y z) : W.lt x z := by
  constructor
  · exact h.le.trans h'
  rintro rfl
  apply h.ne
  exact h.le.antisymm h'

theorem WOSet.le.trans_lt (h : W.le x y) (h' : W.lt y z) : W.lt x z := by
  constructor
  . exact h.trans h'.le
  rintro rfl
  apply h'.ne
  exact h'.le.antisymm h

theorem WOSet.lt.trans (h : W.lt x y) (h' : W.lt y z) : W.lt x z :=
  h.trans_le h'.le
  /- the proof can be a term that is this long:
  ________________ -/

theorem WOSet.le_or_lt (hx : x ∈ W.S) (hy : y ∈ W.S) : W.le x y ∨ W.lt y x := by
  set S :=  {z | (z=x ∨ z=y)}
  have SsubW: S ⊆ W.S := by
    intro z zS
    rcases zS with (zh|zh) <;> rwa[zh]

  have xS: x∈S := by left; rfl
  have yS: y∈S := by right; rfl

  have SnEmpty : S.Nonempty := by
    use x;

  obtain ⟨b,bS,bh⟩  := W.exists_min S SsubW SnEmpty
  by_cases bvalue: b = x
  . rw[bvalue] at bS bh
    apply Or.inl (bh y (yS))
  . rcases bS with (beqx|beqy)
    . contradiction
    . by_cases h : x=y
      . rw[h]; left; apply (W.refl y hy)
      . right; constructor;
        . rw[beqy] at bh
          apply bh x (xS)
        . push_neg at h; symm; assumption

  -- prove this by applying `W.exists_min` to the set `{x,y}`.

  -- `Mass comment`: why was this proof so terrible?

theorem WOSet.le.not_lt (h : W.le x y) : ¬ W.lt y x := by
  -- this `intro` line is nice. To prove a negation, we `intro` it. But `W.lt y x` is definitionally
  -- `(W.le y x) ∧ y ≠ x`, and we can deconstruct and introduce it at the same time.
  -- (If this is vertigo-inducing, `intro hlt` + `obtain ⟨hle,hne⟩ := hlt` does this same thing.)
  intro ⟨hle, hne⟩
  apply hne
  exact hle.antisymm h

theorem WOSet.lt.not_le (h : W.lt x y) : ¬ W.le y x := by
  intro hle
  obtain ⟨xley, xney⟩ := h
  apply xney
  exact xley.antisymm hle

theorem WOSet.le_iff_not_lt {W : WOSet α} (hx : x ∈ W.S) (hy : y ∈ W.S) :
    W.le x y ↔ ¬ W.lt y x := by
  -- a slightly different approach to an `iff` proof here.
  obtain (h | h) := WOSet.le_or_lt hx hy
  · apply iff_of_true
    · exact h
    exact h.not_lt
  apply iff_of_false
  · intro xley
    apply h.not_le
    exact xley
  rwa[not_not]

theorem WOSet.lt_iff_not_le {W : WOSet α} (hx : x ∈ W.S) (hy : y ∈ W.S) :
    W.lt x y ↔ ¬ W.le y x := by
  rw [le_iff_not_lt hy hx, not_not]

/-- A cute way to prove two `WOSet`s are equal. -/
theorem WOSet.eq_iff : W = W' ↔ W.S ⊆ W'.S ∧ ∀ x y, W'.le x y → W.le x y := by
  constructor
  · rintro rfl
    simp [Subset.rfl]
  intro ⟨hss, h⟩
  -- Since we tagged the definition `WOSet` with `ext`, we can use the `ext` tactic
  -- to prove two `WOSets` are equal.
  ext x y
  · constructor
    . rintro xW
      apply hss xW
    . rintro xW'
      have xrefl: W'.le x x := W'.refl x xW'
      apply (h x x xrefl).mem_left
  constructor
  . intro xleyW'
    obtain ⟨xW,yW⟩  := hss xleyW'.mem_left, hss xleyW'.mem_right
    rcases W'.le_or_lt xW yW with xley|yltx
    . assumption
    . have : W.le y x := h y x yltx.le
      have xeqy: x=y := xleyW'.antisymm this
      have xneqy: y≠x := yltx.ne
      symm at xeqy
      contradiction
  . intro xleyW'
    apply h x y xleyW'


end WOSet

/-
Now we move onto (1) in our sketch:

(1) Prove that the 'initial segment or equal' ordering `≼` on `Ω` is a partial order.

Instead of `Ω`, we now have `WOSet α`. So we want to define a relation
`IsInitialSegment W W'` for `W W' : WOSet α`, and prove that
the relation `W = W' ∨ IsInitialSegment W W'` is transitive,
reflexive and antisymmetric.

This follows from the fact that `IsInitialSegment` is transitive and irreflexive.
The mathematically least trivial part is the transitivity; The rest is just plumbing.
It will give us some more practice building API, though!

 -/

section Segment

/-- The definition of an initial segment. This differs in appearance from Tao's definition
in two ways. First, he has `W.le x y ↔ W'.le x y` rather than a one-way implication.
Second, Tao has `W.S = {y ∈ W'.S | W'.lt y x}`. In fact, the `y ∈ W'.S` is redundant for us,
because `W'.lt y x` implies it. The fact that we only need `→` for the first part is less
obvious, but we will prove it in a minute with `IsInitialSegment.le_iff_le`.

In general, a weak definition is good! It makes it easier to prove things satisfy the definition,
and the stronger consequences can be written as lemmas. -/
def IsInitialSegment (W W' : WOSet α) :=
  (∀ x y, W.le x y → W'.le x y) ∧ (∃ x ∈ W'.S, W.S = {y | W'.lt y x})

theorem IsInitialSegment.le_of_le (h : IsInitialSegment W W') (hxy : W.le x y) : W'.le x y :=
  h.1 _ _ hxy

theorem IsInitialSegment.eq_setOf_lt (h : IsInitialSegment W W') :
    ∃ x ∈ W'.S, W.S = {y | W'.lt y x} := h.2

theorem IsInitialSegment.le_iff_le (h : IsInitialSegment W W') (hy : y ∈ W.S) :
    W.le x y ↔ W'.le x y := by
  -- this takes a bit of thought. You'll need to use `h.eq_setOf_lt`.
  constructor <;> intro hle
  . apply h.le_of_le hle
  . obtain ⟨b, bW', hb⟩ := h.eq_setOf_lt
    rw[hb] at hy
    have xW: x∈ W.S := by
      rw[hb]
      apply hle.trans_lt hy
    rw[←hb] at hy
    rcases W.le_or_lt xW hy with (h'le|h'le)
    . assumption
    . have : x=y := by
        apply hle.antisymm (h.le_of_le (h'le.le))
      rw[this]
      apply W.refl y hy

      -- `Mass comment`: Is there a way to rewrite for one instance, in the above I had to
      -- rewrite something to use it, and then undo it to use it again.

theorem IsInitialSegment.lt_iff_lt (h : IsInitialSegment W W') (hy : y ∈ W.S) :
    W.lt x y ↔ W'.lt x y := by
  -- this is easier - use the definition of `WOSet.lt` and the previous lemma.
  apply and_congr_left_iff.mpr
  intro _
  apply h.le_iff_le hy

theorem IsInitialSegment.lt_of_lt (h : IsInitialSegment W W') (hxy : W.lt x y) : W'.lt x y := by
  rwa [← h.lt_iff_lt hxy.le.mem_right]

theorem IsInitialSegment.subset (h : IsInitialSegment W W') : W.S ⊆ W'.S := by
  rintro x xW
  exact (h.le_of_le (W.refl x xW)).mem_left

theorem IsInitialSegment.ssubset (h : IsInitialSegment W W') : W.S ⊂ W'.S := by
  rw [ssubset_iff_of_subset h.subset]
  obtain ⟨b, bW, hb⟩ := h.eq_setOf_lt
  refine ⟨b, bW, ?_⟩
  intro bW
  rw[hb] at bW
  apply (ne_self_iff_false b).mp (bW.ne)

theorem IsInitialSegment.irrefl (W : WOSet α) : ¬ IsInitialSegment W W := by
  intro h
  exact h.ssubset.ne rfl

theorem IsInitialSegment.trans {W₁ W₂ W₃ : WOSet α} (h : IsInitialSegment W₁ W₂)
    (h' : IsInitialSegment W₂ W₃) : IsInitialSegment W₁ W₃ := by
  obtain ⟨x₂, hx₂, hW₁⟩ := h.eq_setOf_lt
  constructor
  · intro x y xley₁
    apply h'.le_of_le (h.le_of_le (xley₁))
  . refine ⟨x₂, h'.subset hx₂, ?_⟩
    rw[hW₁]
    apply subset_antisymm_iff.mpr
    constructor <;> intro x xS
    . apply h'.lt_of_lt xS
    . apply (h'.lt_iff_lt hx₂).mpr
      assumption

/-- This shows that the 'initial segment or equal' relation is a partial order, which
  allows us to use `≤` and all the nice API that comes with it. -/
instance (α : Type*) : PartialOrder (WOSet α) where
  le W W' := W = W' ∨ IsInitialSegment W W'
  le_refl W := Or.inl rfl
  le_trans := by
    -- when you are introducing a hypothesis of the form `a = b`, you can use `rintro` with `rfl`
    -- to automatically do the substitutions without having to `rw`.
    -- the line below does this with two hypotheses at once, splitting into four cases.
    rintro W₁ W₂ W₃ (rfl | h) (rfl | h')
    · exact Or.inl rfl
    · exact Or.inr h'
    · exact Or.inr h
    exact Or.inr (h.trans h')
  le_antisymm := by
    rintro W W' (rfl | h)
    · simp
    rintro (rfl | h')
    · rfl
    have : IsInitialSegment W W := (h.trans h')
    exfalso
    apply (IsInitialSegment.irrefl W ) this

/-
Now we are done with (1). But let's write some more lemmas so it is easy to interact with
`≤` and `<`.
-/

/-- This one is true by definition. -/
theorem WOSet.le_iff_eq_or_initialSegment : W ≤ W' ↔ W = W' ∨ IsInitialSegment W W' := Iff.rfl

theorem WOSet.lt_iff_initialSegment : W < W' ↔ IsInitialSegment W W' := by
  rw [lt_iff_le_and_ne, WOSet.le_iff_eq_or_initialSegment, Ne, or_and_right]
  simp only [and_not_self, false_or, and_iff_left_iff_imp]
  rintro h rfl
  exact h.irrefl W

theorem WOSet.subset_of_le (h : W ≤ W') : W.S ⊆ W'.S := by
  obtain (rfl | hlt) := h
  · rfl
  exact hlt.subset


/-- An alternative way to show that `W ≤ W'`. -/
theorem WOSet.le_alt (h : ∀ x y, W.le x y → W'.le x y)
    (h_seg : ∀ x y, W'.le x y → y ∈ W.S → x ∈ W.S) : W ≤ W' := by

  have hss : W.S ⊆ W'.S := by
    intro x hx
    exact (h _ _ (W.refl _ hx)).mem_left

  have h_or := eq_empty_or_nonempty (W'.S \ W.S)
  rw [diff_eq_empty] at h_or
  obtain (hss' | hne) := h_or
  · left; apply (W.eq_iff ).mpr
    refine ⟨hss, ?_⟩
    intro x y xleyW'
    rcases (W.le_or_lt (hss' xleyW'.mem_left) (hss' xleyW'.mem_right)) with (xleyW| yltxW)
    . assumption
    . have : W'.le y x := h y x yltxW.le
      obtain rfl := (xleyW'.antisymm this)
      apply W.refl x ((yltxW.le).mem_left)
    -- In this case, use `WOSet.eq_iff` to show that `W = W'`. Almost all the work is done.
  -- Now show that `W` is an initial segment of `W'`.
  right
  constructor
  · exact h
  -- Show that the minimum `x` of `W'.S \ W.S` works.
  have hmin := W'.exists_min (W'.S \ W.S) (diff_subset _ _) hne
  simp only [mem_diff, and_imp] at hmin
  obtain ⟨x, ⟨hxW', hxW⟩, hx⟩ := hmin

  refine ⟨x,hxW',?_⟩
  apply subset_antisymm_iff.mpr
  constructor <;> rintro z zS
  . constructor
    . obtain (zlex|xltz) := W'.le_or_lt (hss zS) hxW'
      . assumption
      . have xS := h_seg x z xltz.le zS
        contradiction
    . rintro rfl
      contradiction
  . by_cases znS : z∈ W.S
    . assumption
    . have hstuff := hx z (zS.le.mem_left) (znS)
      have  := zS.le.antisymm hstuff
      rw[this]
      exfalso; exact zS.ne this

/-- This gives us the fact that `WOSet α` isn't the empty type.
(If you have removed the `Nonempty α` assumption from our proof of Zorn, you won't need this) -/
instance {α : Type*} : Nonempty (WOSet α) :=
  ⟨WOSet.empty α⟩

end Segment


/- We now skip to the first part of
(4) : Every maximal element `(Y, ≤)` of `Ω` must have `Y = X`

(We do this now because it's a bit easier than working with chains)

The idea here is simple enough; if we had a maximal well-ordered set that wasn't all of `X`,
we could add some element to it to get a larger well-ordered set, by just declaring it to be
the new maximum of the order.

To formalize this, we define a function `WOSEt.insertAbove`, which takes a nonelement `a`
of some `W : WOSet α` for which `ha : a ∉ W.S`, and glues `a` to the top of `W`.
Then we need to show that this gives a larger set wrt `≤`; i.e that `W < W.insertAbove a ha`.
That's what this next section does. -/

section Insert

/-- Given a nonelement of a `WOSet`, we can add it above everything in the set to get
a larger `WOSet`. Of course we actually need to say what the new well-ordering is, and prove
that it's a well-ordering.
This kind of thing tends to be a bit tedious, because it's so obvious intuitively
and involves a lot of case splitting. I've completed most of it. -/
def WOSet.insertAbove (W : WOSet α) (a : α) (ha : a ∉ W.S) : WOSet α where
  S := insert a W.S
  le x y := W.le x y ∨ (x ∈ insert a W.S ∧ y = a)
  supportedOn := by
    simp only [mem_insert_iff]
    rintro x y (hr | hr)
    · -- we know `x, y ∈ W.S`, so just tell this to the simplifier rather than `constructor` etc.
      simp [hr.mem_left, hr.mem_right]

    -- `hr` can be deconstructed further here. Note that we can use `rfl` in the
    -- `obtain` to just identify `y` and `a` everywhere rather than using rewrites.
    obtain ⟨(rfl | hx), rfl⟩ := hr
    · simp
    simp [hx]
  refl := by
    -- `simp?` does quite a lot here.
    simp only [mem_insert_iff, forall_eq_or_imp, true_or, and_self, or_true, true_and]
    intro x hx
    left
    exact W.refl x hx
  antisymm := by
    simp only [mem_insert_iff]
    -- this `rintro` splits into four cases with one command.
    -- We in fact could take this further; try writing
    -- `rintro x y (hxy | ⟨(rfl | hy), rfl⟩) (hyx | ⟨(hy | hy), hxy⟩)` instead of the line below.
    rintro x y (hxy | hxy) (hyx | hyx)
    · exact W.antisymm _ _ hxy hyx
    · obtain ⟨(rfl | -), rfl⟩ := hyx
      · rfl
      have := hxy.mem_left; contradiction
    obtain ⟨(rfl | -), rfl⟩ := hxy
    · rfl
    · have := hyx.mem_left
      contradiction
    rw [hxy.2, hyx.2]
  trans := by
    simp only [mem_insert_iff]
    rintro x y z (hxy | hxy) (hyz | hyz)
    . exact Or.inl (hxy.trans hyz)

    . obtain ⟨(rfl|_), rfl⟩ := hyz
      . exact Or.inl (hxy)
      . right; refine ⟨Or.inr (hxy.mem_left), rfl⟩

    . obtain ⟨(rfl|_), rfl⟩ := hxy
      . exact Or.inl (hyz)
      . have := hyz.mem_left
        contradiction

    . obtain ⟨(rfl|_), rfl⟩ := hyz <;> obtain ⟨(rfl|xS), heq⟩ := hxy
      . simp only [true_or, and_self, or_true]
      . right; refine ⟨(Or.inr xS),rfl⟩
      . simp only [true_or, and_self, or_true]
      . right; refine ⟨Or.inr xS,rfl⟩

  exists_min := by
    intro T hT hTne
    by_cases hTa : T = {a}
    · simp [hTa]
    -- Invoke `W.exists_min` with the set `T \ {a}`.
  -- (So we need that it is a nonempty subset of `W.S`)
    have hss : T \ {a} ⊆ W.S := by
      have h' := diff_subset_diff_left hT (t := {a})
      refine subset_trans h' ?_
      simp

    have hne : (T \ {a}).Nonempty := by
      obtain (eqempty| assum) := eq_empty_or_nonempty (T\ {a})
      . apply diff_eq_empty.mp at eqempty
        have : T = {a} := by
          apply subset_antisymm_iff.mpr; refine ⟨eqempty, ?_⟩
          obtain ⟨b,hb⟩ := hTne
          have : b=a := mem_singleton_iff.mpr (eqempty hb)
          rw[this] at hb
          apply singleton_subset_iff.mpr
          assumption
        contradiction
      . assumption

    have hmin := W.exists_min (T \ {a}) hss hne
    obtain ⟨b, hb⟩ := hmin
    have hbS : b ∈ W.S := mem_of_mem_of_subset hb.1 hss
    simp only [mem_diff, mem_singleton_iff, and_imp] at hb
    use b
    simp only [mem_insert_iff, hbS, or_true, true_and, hb.1]
    intro t ht
    rw [or_iff_not_imp_right]
    exact hb.2 t ht

theorem WOSet.lt_insertAbove (W : WOSet α) (a : α) (ha : a ∉ W.S) : W < W.insertAbove a ha := by
  simp only [insertAbove, mem_insert_iff, lt_iff_initialSegment, IsInitialSegment, WOSet.lt,
    ne_eq, exists_eq_or_imp, and_true]
  constructor
  · tauto
  -- do we want `left` or `right` here?
  . left;
    apply subset_antisymm_iff.mpr;
    constructor <;> intro x xS
    . simp only [mem_setOf_eq]
      refine ⟨Or.inr (Or.inr xS),?_⟩
      by_contra!; rw[this] at xS; contradiction
    . simp only [mem_setOf_eq] at xS
      obtain ⟨(xlea|xeqa|xS),xneqa⟩ := xS
      . exact xlea.mem_left
      . contradiction
      . assumption

/-- Because of the previous lemma, every maximal well-ordered set must contain everything. -/
theorem eq_univ_of_maximal (W : WOSet α) (hW : IsMaximal W) : W.S = univ := by
  by_contra! h
  rw [ne_univ_iff_exists_not_mem] at h
  rw [IsMaximal] at hW
  obtain ⟨a,anS⟩ := h
  have WltIns  := W.lt_insertAbove a anS
  have WeqIns := hW (W.insertAbove a anS) WltIns.le
  obtain ⟨_,WneqIns⟩ := lt_iff_le_and_ne.mp WltIns
  contradiction

end Insert

/-
Now we have to move onto ...

(2) Prove that every chain in `Ω` has an upper bound with respect to `≼`.

That is, we have some `C : Set (WOSet α)` (i.e. a `Set` of `WOSet α`s) for which `IsChain C`.
The upper bound of the chain as a mathematical object should be easy to see;
we define the `U : WOSet α` for which `U.S` the union of `W.S` for all `W ∈ Ws`,
and define a well-ordering on `U` by using the well-orderings on the chain,
which are all consistent with each other by the definition of `≤`.
There is a bit of work here to do, though. What is the actual ordering on `U`?

There are multiple ways to define it; the easiest is probably to say that
`U.le x y` if and only if `W.le x y` for some `W ∈ Ws`.

So now we have to prove that that choice of `le` gives a well-ordering on the union of
all the `W ∈ Ws`. Then we have to prove that the well-ordering defined on the union
is an upper bound for the chain. This is all work, so let's start on it.
-/

section Chain

-- Define a new variable; by default `Ws` means a set of `WOSet`s.
variable {Ws : Set (WOSet α)}

/-- A chain is a set where any two elements are comparable. For our particular partial ordering,
this means that for any `W,W'` in the chain, either they are equal or one is an initial segment
of another. We use this a few times; this lemma streamlines it. -/
theorem IsChain.eq_or_segment_or_segment (hWs : IsChain Ws) (hW : W ∈ Ws) (hW' : W' ∈ Ws) :
    W = W' ∨ IsInitialSegment W W' ∨ IsInitialSegment W' W := by
  have h := hWs.le_or_lt_of_mem_of_mem hW hW'
  rcases h with (WleW'|W'ltW)
  . apply or_assoc.mp; left;
    apply WOSet.le_iff_eq_or_initialSegment.mp WleW'
  . right; right;
    apply WOSet.lt_iff_initialSegment.mp W'ltW
  -- rwa [WOSet.le_iff_eq_or_initialSegment, WOSet.lt_iff_initialSegment, or_assoc] at h

/-- We want to be able to conclude that `W'.le x y` from `W.le x y` for `W,W'` in the chain.
This can be proved just knowing that `y ∈ W'.S`.
(I think) we only use this once, but the proof flows better if we abstract it out. -/
theorem IsChain.le_of_le (hWs : IsChain Ws) (hW : W ∈ Ws) (hW' : W' ∈ Ws) (hxy : W.le x y)
    (hy : y ∈ W'.S) : W'.le x y := by
  obtain (rfl | hseg | hseg) := hWs.eq_or_segment_or_segment hW hW'
  · exact hxy
  · exact hseg.le_of_le hxy
  rwa [hseg.le_iff_le hy]

/-- We can do something similar for `W.lt`. Use copy-paste to prove this. -/
theorem IsChain.lt_of_lt (hWs : IsChain Ws) (hW : W ∈ Ws) (hW' : W' ∈ Ws) (hxy : W.lt x y)
    (hy : y ∈ W'.S) : W'.lt x y := by
  obtain (rfl | hseg | hseg) := hWs.eq_or_segment_or_segment hW hW'
  · exact hxy
  · exact hseg.lt_of_lt hxy
  rwa [hseg.lt_iff_lt hy]

/-- The `WOSet` union of a chain. -/
def unionChain (Ws : Set (WOSet α)) (hWs : IsChain Ws) : WOSet α where
  -- the syntax for the union is a bit complicated here, since it involves subtypes.
  -- luckily, it's basically made invisible by just typing `simp?` at the beginning of
  -- all the proofs, which transforms the goal into something concrete not using unions.
  S := ⋃ (W : Ws), (W : WOSet α).S

  -- to avoid the awkwardness of saying 'choose some W ∈ Ws containing x and y',
  -- we define the `le` relation on the union in terms of existence.
  le x y := ∃ W ∈ Ws, W.le x y

  supportedOn := by
    simp only [iUnion_coe_set, mem_iUnion, exists_prop, forall_exists_index, and_imp]
    intro x y W hW hxy
    refine ⟨⟨W,hW,hxy.mem_left⟩,⟨W,hW,hxy.mem_right⟩⟩

  refl := by
    simp only [iUnion_coe_set, mem_iUnion, exists_prop, forall_exists_index, and_imp]
    intro a W hW ha
    refine ⟨W,hW,W.refl a ha⟩

  antisymm := by
    simp only [forall_exists_index, and_imp]
    intro x y W hW hxy W' hW' hyx
   -- split into cases using `hWs.eq_or_segment_or_segment`:
    -- either `W = W`, or one is a segment of another.
    have h_cases := hWs.eq_or_segment_or_segment hW hW'
    obtain (rfl | hseg | hseg) := h_cases
    · exact hxy.antisymm hyx
    · exact (hseg.le_of_le hxy).antisymm hyx
    exact hxy.antisymm (hseg.le_of_le hyx)

  trans := by
    simp only [forall_exists_index, and_imp]
    intro x y z W hW hxy W' hW' hyz
    -- split into cases like earlier
    have _ := hWs.eq_or_segment_or_segment hW hW'
    have h'xy := hWs.le_of_le hW hW' hxy hyz.mem_left
    refine ⟨W', hW', h'xy.trans hyz⟩

  exists_min := by
    simp only [iUnion_coe_set]
    intro T hT hTne

    have hW : ∃ W ∈ Ws, (W.S ∩ T).Nonempty := by
      by_contra! hcon
      obtain ⟨x, hxT⟩ := hTne
      -- use `hxT` to show find some `W ∈ Ws` for which `W.S ∩ T` contains `x`.
      -- then contradict `hcon`.
      obtain ⟨W,S, ⟨h,rfl⟩, hxS⟩  := mem_iUnion.mp (hT hxT)
      simp only at hxS
      have emp := hcon W h
      have nonemp := nonempty_def.mpr ⟨x, (mem_inter_iff x W.S T).mpr ⟨hxS, hxT⟩ ⟩
      have notemp := nonempty_iff_ne_empty.mp nonemp
      contradiction

    obtain ⟨W, hW, hWT⟩ := hW

    -- use `h_min` to find a minimum `b` of `W.S ∩ T`.
    have h_min := W.exists_min (W.S ∩ T) (inter_subset_left _ _) hWT
    simp only [mem_inter_iff, and_imp] at h_min

    obtain ⟨b, ⟨hbW, hbT⟩, hbmin⟩ := h_min


    -- show that this `b` is actually a minimum of everything
    use b, hbT
    intro t ht
    have htC := mem_of_mem_of_subset ht hT
    simp only [mem_iUnion, exists_prop] at htC
    obtain ⟨W', hW', htW'⟩ := htC

    -- if `t ∈ W.S`, we can just use `W` and `hbmin`.
    by_cases htW : t ∈ W.S
    · refine ⟨W, hW, hbmin t htW ht⟩

    -- Since `t ∈ W'.S \ W.S` but `W` and `W'` are in a chain,
    -- we know `W` is an initial segment of `W'`.
    have hseg : IsInitialSegment W W' := by
      obtain (rfl|h|h) := hWs.eq_or_segment_or_segment hW hW'
      . contradiction
      . assumption
      . have := h.subset htW'
        contradiction

    use W', hW'
    obtain ⟨x,xW',hWS⟩  := hseg.2
    simp only [hWS] at *
    simp only [mem_setOf_eq] at *
    apply (WOSet.le_iff_not_lt xW' htW').mpr at htW
    apply (hbW).le.trans htW

/- Once you define a structure, having little lemmas like this that describe its fields
can save having to unfold a complicated definition in full, and keep the context tidy.
Lemmas like this can be tagged `@[simp]`, which makes the simplifier use them automatically.
(This isn't appropriate for every lemma, but it is here; when would you ever not want to
immediately apply this kind of result?) -/
@[simp] theorem unionChain.le_iff (Ws : Set (WOSet α)) (hWs : IsChain Ws) :
    (unionChain Ws hWs).le x y ↔ ∃ W ∈ Ws, W.le x y := by
  simp [unionChain]

@[simp] theorem unionChain.lt_iff (Ws : Set (WOSet α)) (hWs : IsChain Ws) :
    (unionChain Ws hWs).lt x y ↔ ∃ W ∈ Ws, W.lt x y := by
  simp only [WOSet.lt, le_iff, ne_eq]
  tauto

@[simp] theorem unionChain.S_eq (Ws : Set (WOSet α)) (hWs : IsChain Ws) :
    (unionChain Ws hWs).S = ⋃ (W : Ws), (W : WOSet α).S := rfl

/-- Now we need to show that the union is an upper bound. -/
theorem unionChain_isUB (Ws : Set (WOSet α)) (hWs : IsChain Ws) :
    IsUB Ws (unionChain Ws hWs) := by
  intro W hW
  -- there are really two cases here. One is where `W` is above everything in the chain,
  -- in which case it is equal to the union. The other is where it is an initial segment
  -- of something above it in the chain. In this case, we argue it is also an initial
  -- segment of the whole chain.
  -- we handle the first case via contradiction.
  rw [WOSet.le_iff_eq_or_initialSegment, or_iff_not_imp_left]
  intro hne


  have h : ∃ W' ∈ Ws, IsInitialSegment W W' := by
    by_contra! h'
    apply hne
    have hS : W.S = (unionChain Ws hWs).S := by
      -- use `subset_antisymm_iff` and `simp`.
      apply subset_antisymm_iff.mpr
      constructor <;> intro x hxS <;> simp only [unionChain.S_eq, iUnion_coe_set, mem_iUnion,
        exists_prop] at *
      . refine ⟨W,hW,hxS⟩
      . obtain ⟨W',hW',hxW'⟩ := hxS
        rcases hWs.eq_or_segment_or_segment hW hW' with (rfl|h|h)
        . assumption
        . exfalso
          exact (h' W' hW') h
        . exact h.subset hxW'

    ext x y
    · rw[hS]
    simp only [unionChain.le_iff]
    constructor <;> rintro h
    . refine ⟨W,hW,h⟩
    . obtain ⟨W', hW', hxy⟩ := h
      rcases (hWs W W' hW hW') with (WleW'|W'leW)
      . rcases (WOSet.le_iff_eq_or_initialSegment.mp WleW') with (rfl|hle)
        . assumption
        . exfalso; exact (h' W' hW') hle
      . rcases (WOSet.le_iff_eq_or_initialSegment.mp W'leW) with (rfl|hle)
        . assumption
        . exact hle.le_of_le hxy

  obtain ⟨W', hW', hWW'⟩ := h
  obtain ⟨x, hx, hWS⟩ := hWW'.eq_setOf_lt

  constructor
  · tauto
  use x
  simp only [unionChain.S_eq, iUnion_coe_set, mem_iUnion, exists_prop, hWS, unionChain.lt_iff]
  constructor
  . refine ⟨W',hW',hx⟩
  . apply subset_antisymm_iff.mpr
    constructor <;> intro z hzS
    . refine ⟨W',hW',hzS⟩
    . simp only [mem_setOf_eq] at *
      obtain ⟨W'', hW'',hleW''⟩ := hzS
      exact hWs.lt_of_lt hW'' hW' hleW'' hx


end Chain

section WOSet_univ

/-
There isn't much left :

(3) By Zorn's lemma, conclude that there is a maximal element of `Ω`.

We have done all the hard work already.
-/

theorem exists_WOSet_on_univ (α : Type*) : ∃ (wo : WOSet α), wo.S = univ := by
  -- we have to show there is a maximal well-ordered set. To avoid this being an indented subgoal,
  -- we use the `suffices` tactic.
  suffices hmax : ∃ (W : WOSet α), IsMaximal W by
    -- what do we already know about maximal `WOSet`s?
    obtain ⟨W,WIsMax⟩ := hmax
    refine ⟨W, eq_univ_of_maximal W WIsMax⟩

  -- I know how to prove there is a maximal set!
  apply zorn
  rintro C hC
  refine ⟨unionChain C hC, unionChain_isUB C hC⟩

end WOSet_univ

/-
We are essentially done, but a little bit more tidying up is in order.
What we have produced is an example of own hand-rolled `WOSet` that well-orders the set `Univ`.
A better way to present this result is just that 'every type' has a well-order.

This is just repackaging, not mathematics; I've left a couple of `sorry`s to fill.
-/

section WO_type

-- A well-order on a type.
structure WellOrder (α : Type*) where
  (le : α → α → Prop)
  (refl : ∀ a, le a a)
  (antisymm : ∀ a b, le a b → le b a → a = b)
  (trans : ∀ a b c, le a b → le b c → le a c)
  (exists_min : ∀ (S : Set α), S.Nonempty → ∃ b ∈ S, ∀ x ∈ S, le b x)

noncomputable def WOSet.toWellOrder (W : WOSet α) (hW : W.S = univ) :
    WellOrder α where
  le := W.le
  refl x := W.refl x (by simp [hW])
  antisymm := W.antisymm
  trans := W.trans
  exists_min := by
    intro S
    have := subset_univ S
    rw[← hW] at this
    exact W.exists_min S this

/-- This is a more palatable type-theoretic statement of the well-ordering principle.
Every type has a well-order.-/
theorem exists_wellOrder (α : Type*) : Nonempty (WellOrder α) := by
  obtain ⟨W, hW⟩ := exists_WOSet_on_univ α
  exact ⟨W.toWellOrder hW⟩


/- Finally, Let's double-check that we haven't broken mathematics.
Once you have filled in all the `sorry`s, uncommenting the command below should display the axioms
the proof used, one of which is `Classical.choice`.
I believe the only place this was used is the line `choose b hb using h_strictUB` from the
proof of Zorn's lemma. Once is enough, though!
-/

#print axioms exists_wellOrder

end WO_type
