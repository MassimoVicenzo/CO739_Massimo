import Mathlib.Tactic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Set.Card

/-
Here we are formalizing Zagier's 'one-sentence proof' that each prime congruent to one modulo four
is the sum of two squares. You can find it at

`https://en.wikipedia.org/wiki/Fermat%27s_theorem_on_sums_of_two_squares`

Even informally, there is quite a lot going on in the proof.

One of the challenges with formalizing is that, while it's a proof about natural numbers,
it uses subtraction, and the definition of subtraction in `ℕ` is awkward, since for example
`(4 : ℕ) - (17 : ℕ) = (0 : ℕ)`. There are ways to keep track of this carefully, but we
adopt the alternative approach of working in the integers, where subtraction behaves nicely
and the `ring` tactic works.

Another challenge is that we need to work with cardinality,
which requires thinking about finiteness. Finiteness is more complicated than you might think,
and in fact there are a few different notions of set cardinality.
The most commonly used one is `Finset.card` - a `Finset` is a 'bundled' finite set.
Some of the syntax for finsets is a bit complicated though, so we opt for
We use `Set.ncard`, which looks notationally more like what you would expect.

-/

open Nat

variable {p : Nat}

section Prime

/-
  A few lemmas about primality when working in the integers. What they say is simple enough,
  but the proofs are a bit in the weeds; just read and understand the statements.
-/

lemma Int.eq_one_or_eq_one_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : m = 1 ∨ n = 1 := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  by_contra! hmn
  exact Int.not_prime_of_int_mul (fun hm' ↦ hmn.1 <| by simpa [hm'])
    (fun hn' ↦ hmn.2 <| by simpa [hn']) hmnp hp

lemma Int.eq_or_eq_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : (m = 1 ∧ n = p) ∨ (m = p ∧ n = 1) := by
  obtain (rfl | rfl) := Int.eq_one_or_eq_one_of_mul_prime hm hn hp hmnp
  · simp [← hmnp]
  simp [← hmnp]

lemma Int.square_not_prime (m : ℤ) (p : ℕ) (hmp : m^2 = p) : ¬ p.Prime := by
  have hp' : (m.natAbs)^2 = p := by
    zify; simp [← hmp]
  rw [← hp']
  exact Nat.Prime.not_prime_pow rfl.le

lemma Int.four_mul_not_prime (m : ℤ) (p : ℕ) (hmp : 4*m = p) : ¬ p.Prime := by
  lift m to ℕ using (by linarith)
  norm_cast at hmp
  rw [← hmp, Nat.prime_mul_iff]
  simp [(by decide : ¬ Nat.Prime 4)]


end Prime

section invo

variable {α : Type*}

/-- an involution is a function `f` with `f (f x) = x` for all `x`. -/
def IsInvolution (f : α → α) := ∀ a, f (f a) = a

open Classical in
lemma setOf_not_fixedPoint_even [Fintype α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x ≠ x}.ncard := by
  -- don't worry about this for now.
  sorry

lemma even_iff_ncard_fixedPoint_even [Finite α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x = x}.ncard ↔ Even (Nat.card α) := by
  sorry

end invo

section Triple

/-
The type of triples of nonnegative integers `x,y,z` with `x² + 4yz = p`.
These are what make Zagier's proof work. They are the
-/
@[ext] structure Triple (p : ℕ) where
  (x : ℤ)
  (hx : 0 ≤ x)
  (y : ℤ)
  (hy : 0 ≤ y)
  (z : ℤ)
  (hz : 0 ≤ z)
  (h_eq : x^2 + 4 * y * z = p)

/-- There are only finitely many such triples for a given `p`. Don't worry about the proof for now.-/
instance foo {p : ℕ} (hp : p.Prime) : Fintype (Triple p) := sorry

def Triple.xpos (t : Triple p) (hp : p.Prime) : 0 < t.x := by
  refine t.hx.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  simp only [← h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    mul_assoc] at hmul
  exact Int.four_mul_not_prime _ _ hmul hp

def Triple.ypos (t : Triple p) (hp : p.Prime) : 0 < t.y := by
  refine t.hy.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  simp only [← h0,mul_zero, zero_mul, add_zero] at hmul
  exact (Int.square_not_prime t.x p hmul) hp

def Triple.zpos (t : Triple p) (hp : p.Prime) : 0 < t.z := by
  refine t.hz.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  simp only [← h0,mul_zero, zero_mul, add_zero] at hmul
  exact (Int.square_not_prime t.x p hmul) hp

/-- Define the obvious involution which swaps the values of `y` and `z`. -/
def flipInv (p : ℕ) (t : Triple p) : Triple p where
  x := t.x
  hx := t.hx
  y := t.z
  hy := t.hz
  z := t.y
  hz := t.hy
  h_eq := by
    simp_rw [← t.h_eq]
    ring

/-- Show it is an involution. -/
theorem flipInv_involution (p : ℕ) : IsInvolution (flipInv p) := by
  intro t
  exact rfl

/-
Before defining Zagier's weird involution, we define predicates corresponding to the case split.
This allows us to separate the computation from the logic a bit more easily.
-/

def TypeOne (t : Triple p) := t.x ≤ t.y - t.z

def TypeTwo (t : Triple p) := t.y - t.z < t.x ∧ t.x < 2 * t.y

def TypeThree (t : Triple p) := 2 * t.y ≤ t.x

lemma typeThree_of_not_typeOne_typeTwo (t : Triple p) (h1 : ¬ TypeOne t) (h2 : ¬ TypeTwo t) :
    TypeThree t := by
  rw [TypeOne, not_le] at h1
  rw [TypeTwo, not_and, not_lt] at h2
  unfold TypeThree
  exact h2 h1

lemma TypeTwo.not_typeOne {t : Triple p} (ht : TypeTwo t) : ¬ TypeOne t := by
  rw[TypeOne, not_le]
  rw[TypeTwo] at ht
  exact ht.1

lemma TypeThree.not_typeTwo {t : Triple p} (ht : TypeThree t) : ¬ TypeTwo t := by
  rw[TypeTwo, not_and, not_lt]
  rw[TypeThree] at ht
  intro _
  exact ht

lemma TypeThree.not_typeOne {t : Triple p} (ht : TypeThree t) (hp : p.Prime) : ¬ TypeOne t := by
  rw[TypeOne, not_le]
  rw[TypeThree] at ht
  have := t.zpos hp
  apply sub_lt_iff_lt_add.mpr
  apply lt_add_of_le_of_pos
  have hy2y: t.y ≤ 2*t.y := by
    have := t.ypos hp
    linarith
  exact le_trans hy2y ht
  assumption

@[simps] def A1 (t : Triple p) (ht : TypeOne t) : Triple p where
  x := t.x + 2 * t.z
  hx := by linarith [t.hx, t.hz]
  y := t.z
  hy := t.hz
  z := t.y - t.x - t.z
  hz := by unfold TypeOne at ht; linarith
  h_eq := by simp_rw [← t.h_eq]; ring

lemma A1_typeThree {t : Triple p} (ht : TypeOne t) : TypeThree (A1 t ht) := by
  unfold TypeThree
  unfold TypeOne at ht
  simp [A1, t.hx]

@[simps] def A2 (t : Triple p) (ht : TypeTwo t) : Triple p where
  x := 2 * t.y - t.x
  hx := by rw[TypeTwo] at ht; linarith
  y := t.y
  hy := t.hy
  z := t.x - t.y + t.z
  hz := by rw[TypeTwo] at ht; linarith
  h_eq := by simp_rw[← t.h_eq]; ring

lemma A2_typeTwo (hp : p.Prime) {t : Triple p} (ht : TypeTwo t) : TypeTwo (A2 t ht) := by
  rw[TypeTwo] at *
  simp only [A2, sub_lt_self_iff]
  refine ⟨?_, t.xpos hp⟩
  have := t.zpos hp
  linarith

@[simps] def A3 (t : Triple p) (ht : TypeThree t) : Triple p where
  x := t.x - 2 * t.y
  hx := by rw[TypeThree] at ht; linarith
  y := t.x - t.y + t.z
  hy := by
    rw[TypeThree] at ht
    have hy2y: t.y ≤ 2*t.y := by
      have := t.hy
      linarith
    have hzpos := t.hz
    linarith
  z := t.y
  hz := t.hy
  h_eq := by simp_rw[← t.h_eq]; ring

lemma A3_typeOne {t : Triple p} (ht : TypeThree t) : TypeOne (A3 t ht) := by
  rw[TypeOne]
  rw[TypeThree] at ht
  simp only [A3, tsub_le_iff_right]
  have := t.hz
  linarith


/- The actual definition of `otherInv`. Its value at `t` is `A_i t`, where `t` has type `i`. -/
open Classical in
noncomputable def otherInv (p : ℕ) (t : Triple p) : Triple p :=
  if h1 : TypeOne t then A1 t h1
  else if h2 : TypeTwo t then A2 t h2
  else A3 t (typeThree_of_not_typeOne_typeTwo t h1 h2)

lemma otherInv_apply_typeOne {t : Triple p} (h1 : TypeOne t) : otherInv p t = A1 t h1 := by
  simp [otherInv, h1]

lemma otherInv_apply_typeTwo {t : Triple p} (h2 : TypeTwo t) : otherInv p t = A2 t h2 := by
  simp [otherInv, h2.not_typeOne, h2]

lemma otherInv_apply_typeThree (hp : p.Prime) {t : Triple p} (h3 : TypeThree t) :
    otherInv p t = A3 t h3 := by
  simp [otherInv, h3.not_typeOne hp, h3.not_typeTwo]

lemma otherInv_inv (hp : p.Prime) : IsInvolution (otherInv p) := by
  intro t
  by_cases h1 : TypeOne t
  · rw [otherInv_apply_typeOne h1]
    have h3 := A1_typeThree h1
    rw [otherInv_apply_typeThree hp h3]
    ext <;> simp only [A3, A1, add_sub_cancel_right]
    ring

  by_cases h2 : TypeTwo t
  . rw[otherInv_apply_typeTwo h2]
    have h2' := A2_typeTwo hp h2
    rw[otherInv_apply_typeTwo h2']
    ext <;> simp only [A2, sub_sub_cancel]
    ring

  . have h3 := typeThree_of_not_typeOne_typeTwo t h1 h2
    rw [otherInv_apply_typeThree hp h3]
    have h1 := A3_typeOne h3
    rw [otherInv_apply_typeOne h1]
    ext <;> simp only [A3, A1, add_sub_cancel_right] <;> ring


def otherInvFixedPt {k : ℕ} (hpk : p = 4 * k+1) : Triple p where
  x := 1
  hx := zero_le_one
  y := 1
  hy := zero_le_one
  z := k
  hz := by simp
  h_eq := by linarith

lemma otherInvFixedPt.typeTwo (hp : p.Prime) (hpk : p = 4 * k+1) :
    TypeTwo (otherInvFixedPt hpk) := by
  rw[TypeTwo, otherInvFixedPt]
  simp only [sub_lt_self_iff, cast_pos, mul_one, one_lt_ofNat, and_true]
  linarith [hp.one_lt]

lemma otherInv_fixed_iff {k : ℕ} (hp : p.Prime) (hpk : p = 4 * k+1) (t : Triple p) :
    otherInv p t = t ↔ t = otherInvFixedPt hpk := by
  constructor <;> rintro h
  . by_cases T1 : TypeOne (t)
    . exfalso
      have h1 := otherInv_apply_typeOne T1
      have T3 := A1_typeThree T1
      rw[← h1] at T3 ; rw[← h] at T1
      exact (T3.not_typeOne hp) T1

    by_cases T2 : TypeTwo (t)
    . rw[otherInv_apply_typeTwo T2] at h
      rw[Triple.ext_iff] at h
      simp only [A2, add_left_eq_self, true_and] at h
      obtain ⟨h1,h2⟩ := h
      have xpos := t.xpos hp; have ypos := t.ypos hp; have zpos := t.zpos hp
      have eq := t.h_eq
      obtain ⟨T2a,T2b⟩:= T2
      apply sub_eq_iff_eq_add'.mp at h2
      rw[add_zero] at h2
      have xeqOne :t.x = 1 := by
        rw[h2] at eq T2a T2b
        have eq : t.y * (t.y + 4 * t.z) = ↑p := by linarith
        have : 0<t.y + 4 * t.z := by linarith
        obtain (h|h) := Int.eq_one_or_eq_one_of_mul_prime ypos.le this.le hp eq
        . rw[← h2] at h; exact h
        . exfalso
          simp [h] at eq
          simp [eq] at h
          linarith
      ext <;> simp only [otherInvFixedPt]
      . exact xeqOne
      . rw[h2] at xeqOne
        exact xeqOne
      . simp only [xeqOne, one_pow] at eq T2a T2b
        zify at hpk
        rw[← h2] at eq
        rw[xeqOne] at eq
        linarith

    . have T3 : TypeThree (t) := typeThree_of_not_typeOne_typeTwo t T1 T2
      exfalso
      have h3 := otherInv_apply_typeThree hp T3
      have T1 := A3_typeOne T3
      rw[← h3] at T1 ; rw[← h] at T3
      exact (T3.not_typeOne) hp T1

  . have T2 := otherInvFixedPt.typeTwo hp hpk
    rw[h]
    rw[otherInv_apply_typeTwo T2]
    ext <;> simp only [A2, add_left_eq_self, otherInvFixedPt] <;> ring


lemma exists_fixedPoint (hp : p.Prime) (hpk : p = 4 * k + 1) (f : Triple p → Triple p)
    (hf : IsInvolution f) : ∃ t, f t = t := by
  by_contra! hfix
  set fNFix := {t : (Triple p) | (f t ≠ t)}
  set fFix := {t : (Triple p) | (f t = t)}
  set othInvNFix := {t : (Triple p) | (otherInv p t ≠ t)}
  set othInvFix := {t : (Triple p) | (otherInv p t = t)}

  have h: fNFix = {t : (Triple p) | True} := by
    apply subset_antisymm <;> rintro t ht
    . simp only [Set.setOf_true, Set.mem_univ]
    . apply hfix t

  have := foo hp
  have univEven: Even (fNFix.ncard) := setOf_not_fixedPoint_even f hf

  have uniqueFixed : othInvFix = {otherInvFixedPt hpk}  := by
    apply subset_antisymm <;> rintro t tS
    . apply (otherInv_fixed_iff hp hpk t).mp; assumption
    . apply (otherInv_fixed_iff hp hpk t).mpr; assumption

  have othCardOdd : Odd (othInvFix.ncard) := by
    rw[uniqueFixed]
    have := Set.ncard_singleton (otherInvFixedPt hpk)
    rw[this]
    apply odd_one

  have othNCardEven : Even (othInvNFix.ncard) :=
    setOf_not_fixedPoint_even (otherInv p) (otherInv_inv hp)

  have univOdd : Odd ({t : Triple p| True}.ncard) := by
    have :{t:Triple p| True}.ncard = othInvFix.ncard + othInvNFix.ncard := by
      rw[← Set.ncard_union_add_ncard_inter]
      rw[Set.disjoint_iff_inter_eq_empty.mp]
      simp only [Set.setOf_true, Set.ncard_empty, add_zero]
      have : othInvNFix ∪ othInvFix = Set.univ := by
        apply Set.compl_union_self othInvFix
      rw[Set.union_comm,← this]
      exact Set.disjoint_left.mpr fun ⦃a⦄ a_1 a ↦ a a_1
    rw[this]
    apply Odd.add_even othCardOdd othNCardEven

  apply odd_iff_not_even.mp at univOdd
  rw[← h] at univOdd
  exact univOdd univEven

lemma exists_sum_squares (hp : p.Prime) (hpk : p = 4 * k + 1) : ∃ (a b : ℤ), p = a^2 + b^2 := by
  obtain ⟨t, ht⟩ := exists_fixedPoint hp hpk (flipInv p) (flipInv_involution p)
  refine ⟨t.x, 2 * t.y, ?_⟩
  apply (Triple.ext_iff (flipInv p t) t).mp at ht
  have h : t.z = t.y := ht.2.1
  have h_eq := t.h_eq
  rw[h] at *
  linarith

end Triple
