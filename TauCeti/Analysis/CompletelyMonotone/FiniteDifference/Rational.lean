/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Basic

/-!
# Complete monotonicity in the finite-difference sense, from rational data

`TauCeti.IsDifferenceCompletelyMonotone` quantifies over *all* lists of nonnegative real steps and
all nonnegative real base points. A construction that produces a candidate function as a countable
limit — for instance a fibrewise Radon--Nikodym density, which is only defined up to a null set —
can verify the sign condition on a countable set of data and no more. This file closes that gap:
for a function that is continuous from the right on `[0, ∞)`, the sign condition on **rational
lists at rational base points** already implies the full predicate
(`TauCeti.isDifferenceCompletelyMonotone_of_forall_rat`).

No density argument in several variables is needed. The steps are freed one at a time, each one
costing a single one-variable limit: if every mixed difference of `f` along `l ++ m` alternates
whenever the extra step is rational, then the signed difference along `l ++ m` is nonincreasing
along rational increments, hence — being right-continuous — nonincreasing outright, which is the
sign condition for one further *real* step. The permutation invariance of a mixed difference
(`TauCeti.fwdDiffList_eq_of_perm`) is what lets the new step be peeled off the front.

The right-continuity hypothesis is doing real work: rational data say nothing whatsoever about the
value of `f` at an irrational point, so lowering `f` there below zero leaves every rational datum
untouched while destroying the sign condition for the empty list of steps.

## Main declarations

* `TauCeti.tendsto_fwdDiffList_nhdsGT`: a mixed forward difference of a right-continuous function
  is right-continuous.
* `TauCeti.isDifferenceCompletelyMonotone_of_forall_rat`: rational data suffice.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **A mixed forward difference of a right-continuous function is right-continuous.** The steps
are assumed nonnegative so that the shifted base points stay in `[0, ∞)`, where the hypothesis
lives. -/
theorem tendsto_fwdDiffList_nhdsGT
    (hf : ∀ u : ℝ, 0 ≤ u → Tendsto f (𝓝[>] u) (𝓝 (f u))) {l : List ℝ}
    (hl : ∀ h ∈ l, 0 ≤ h) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fwdDiffList l f) (𝓝[>] u) (𝓝 (fwdDiffList l f u)) := by
  induction l generalizing u with
  | nil => simpa using hf u hu
  | cons h l ih =>
      have hh : 0 ≤ h := hl h (by simp)
      have hrest : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem h hk)
      have hid : Tendsto (fun v : ℝ => v) (𝓝[>] u) (𝓝 u) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hshift : Tendsto (fun v : ℝ => v + h) (𝓝[>] u) (𝓝[>] (u + h)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hid.add_const h) ?_
        filter_upwards [self_mem_nhdsWithin] with v hv
        exact mem_Ioi.2 (by linarith [mem_Ioi.1 hv])
      have h₁ : Tendsto (fun v : ℝ => fwdDiffList l f (v + h)) (𝓝[>] u)
          (𝓝 (fwdDiffList l f (u + h))) := (ih hrest (by linarith)).comp hshift
      have hrw : fwdDiffList (h :: l) f
          = fun v : ℝ => fwdDiffList l f (v + h) - fwdDiffList l f v := by
        funext v
        simp only [fwdDiffList_cons, fwdDiff]
      simp only [hrw]
      exact h₁.sub (ih hrest hu)

/-- A sequence of rationals converging to a real number from the right. -/
private theorem exists_seq_rat_tendsto_nhdsGT (u : ℝ) :
    ∃ r : ℕ → ℚ, (∀ n, u < (r n : ℝ)) ∧ Tendsto (fun n => (r n : ℝ)) atTop (𝓝[>] u) := by
  have hlt : ∀ n : ℕ, ∃ q : ℚ, u < (q : ℝ) ∧ (q : ℝ) < u + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact exists_rat_btwn (by linarith)
  choose r hr₁ hr₂ using hlt
  refine ⟨r, hr₁, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall hr₁)⟩
  have hup : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ) + 1)) atTop (𝓝 (u + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (hr₁ n).le) fun n => (hr₂ n).le

/-- **Rational data suffice for complete monotonicity in the finite-difference sense.** A function
that is continuous from the right at every point of `[0, ∞)` and whose mixed forward differences
along lists of nonnegative *rational* steps alternate at every nonnegative *rational* base point is
completely monotone in the finite-difference sense.

This is the form in which a fibrewise construction verifies the hypothesis of the
Hausdorff--Bernstein--Widder theorem: countably many almost-everywhere statements can be
intersected, whereas the uncountable family of conditions packaged in
`TauCeti.IsDifferenceCompletelyMonotone` cannot. -/
theorem isDifferenceCompletelyMonotone_of_forall_rat
    (hcont : ∀ u : ℝ, 0 ≤ u → Tendsto f (𝓝[>] u) (𝓝 (f u)))
    (hrat : ∀ l : List ℚ, (∀ h ∈ l, 0 ≤ h) → ∀ s : ℚ, 0 ≤ s →
      0 ≤ (-1) ^ l.length * fwdDiffList (l.map (Rat.cast)) f (s : ℝ)) :
    IsDifferenceCompletelyMonotone f := by
  have hmap : ∀ l : List ℚ, (∀ h ∈ l, 0 ≤ h) → ∀ h ∈ l.map (Rat.cast : ℚ → ℝ), (0 : ℝ) ≤ h := by
    intro l hl h hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hh
    exact_mod_cast hl q hq
  -- The base point is freed first: a mixed difference along a fixed list is right-continuous.
  have step₁ : ∀ l : List ℚ, (∀ h ∈ l, 0 ≤ h) → ∀ t : ℝ, 0 ≤ t →
      0 ≤ (-1) ^ l.length * fwdDiffList (l.map (Rat.cast)) f t := by
    intro l hl t ht
    obtain ⟨r, hr, hrt⟩ := exists_seq_rat_tendsto_nhdsGT t
    refine ge_of_tendsto (((tendsto_const_nhds (x := ((-1 : ℝ) ^ l.length))).mul
      (tendsto_fwdDiffList_nhdsGT hcont (hmap l hl) ht)).comp hrt)
      (Eventually.of_forall fun n => ?_)
    simpa using hrat l hl (r n) (by exact_mod_cast (ht.trans (hr n).le))
  -- The steps are freed one at a time.
  have step₂ : ∀ m : List ℝ, (∀ h ∈ m, 0 ≤ h) → ∀ l : List ℚ, (∀ h ∈ l, 0 ≤ h) → ∀ t : ℝ, 0 ≤ t →
      0 ≤ (-1) ^ (l.length + m.length) * fwdDiffList (l.map (Rat.cast) ++ m) f t := by
    intro m
    induction m with
    | nil => intro _ l hl t ht; simpa using step₁ l hl t ht
    | cons h m ih =>
        intro hm l hl t ht
        have hh : 0 ≤ h := hm h (by simp)
        have hmrest : ∀ k ∈ m, 0 ≤ k := fun k hk => hm k (List.mem_cons_of_mem h hk)
        set Φ : ℝ → ℝ := fwdDiffList (l.map (Rat.cast) ++ m) f with hΦ
        have hLnonneg : ∀ k ∈ l.map (Rat.cast : ℚ → ℝ) ++ m, (0 : ℝ) ≤ k := by
          intro k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact hmap l hl k hk
          · exact hmrest k hk
        have hpow : ∀ k : ℕ, ((-1 : ℝ)) ^ (k + 1) = -((-1 : ℝ) ^ k) := by
          intro k; rw [pow_succ]; ring
        -- The two length normalizations needed to match the exponent produced by the inductive
        -- hypothesis against the one in the goal.
        have hlenl : l.length + 1 + m.length = l.length + m.length + 1 := by omega
        have hlenm : l.length + (m.length + 1) = l.length + m.length + 1 := by omega
        -- Rational increments do not increase the signed difference, by the inductive hypothesis
        -- applied to the list with one further rational step.
        have hanti : ∀ u : ℝ, 0 ≤ u → ∀ q : ℚ, 0 ≤ q →
            (-1 : ℝ) ^ (l.length + m.length) * Φ (u + (q : ℝ))
              ≤ (-1 : ℝ) ^ (l.length + m.length) * Φ u := by
          intro u hu q hq
          have hcons : ∀ k ∈ q :: l, (0 : ℚ) ≤ k := by
            intro k hk
            rcases List.mem_cons.1 hk with rfl | hk
            · exact hq
            · exact hl k hk
          have hstep := ih hmrest (q :: l) hcons u hu
          rw [List.map_cons, List.cons_append, List.length_cons] at hstep
          simp only [fwdDiffList_cons, fwdDiff] at hstep
          rw [← hΦ, hlenl, hpow] at hstep
          nlinarith [hstep]
        -- Right-continuity turns rational increments into arbitrary ones.
        have hreal : (-1 : ℝ) ^ (l.length + m.length) * Φ (t + h)
            ≤ (-1 : ℝ) ^ (l.length + m.length) * Φ t := by
          obtain ⟨r, hr, hrt⟩ := exists_seq_rat_tendsto_nhdsGT h
          have hid : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 h) := hrt.mono_right nhdsWithin_le_nhds
          have hshift : Tendsto (fun n => t + (r n : ℝ)) atTop (𝓝[>] (t + h)) := by
            refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              (tendsto_const_nhds.add hid) (Eventually.of_forall fun n => ?_)
            exact mem_Ioi.2 (by linarith [hr n])
          have hΦcont : Tendsto (fun v => (-1 : ℝ) ^ (l.length + m.length) * Φ v)
              (𝓝[>] (t + h)) (𝓝 ((-1 : ℝ) ^ (l.length + m.length) * Φ (t + h))) :=
            tendsto_const_nhds.mul
              (hΦ ▸ tendsto_fwdDiffList_nhdsGT hcont hLnonneg (by linarith : (0 : ℝ) ≤ t + h))
          refine le_of_tendsto (hΦcont.comp hshift) (Eventually.of_forall fun n => ?_)
          exact hanti t ht (r n) (by exact_mod_cast (hh.trans (hr n).le))
        -- Peel the new step off the front and read the sign condition off `hreal`.
        have hpermeq : fwdDiffList (l.map (Rat.cast) ++ h :: m) f = fwdDiffList (h :: (l.map
            (Rat.cast) ++ m)) f := fwdDiffList_eq_of_perm List.perm_middle f
        rw [List.length_cons, hpermeq]
        simp only [fwdDiffList_cons, fwdDiff]
        rw [← hΦ, hlenm, hpow]
        nlinarith [hreal]
  refine isDifferenceCompletelyMonotone_iff.2 fun m hm t ht => ?_
  simpa using step₂ m hm [] (by simp) t ht

end TauCeti

end
