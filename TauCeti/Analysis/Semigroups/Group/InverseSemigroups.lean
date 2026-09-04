/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Basic

/-!
# Gluing inverse semigroups into a strongly continuous group

Two strongly continuous semigroups form the positive and negative halves of a strongly continuous
group when their operators at equal times are mutual inverses. This file constructs the group by
using the first semigroup at nonnegative times and the second one at nonpositive times.

The construction isolates the gluing step used in generation results for two-sided groups. In
particular, a Stone-type construction can generate contraction semigroups for an operator and its
negative separately, prove that their operators are inverse, and then apply
`StronglyContinuousSemigroup.toGroupOfInverse`.

## Main declarations

* `TauCeti.Semigroups.StronglyContinuousSemigroup.comp_comm_of_inverse`: operators from the two
  semigroups commute, even at different times.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse`: glue two mutually inverse
  C₀-semigroups into a C₀-group.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse_toSemigroup`: the positive half
  of the glued group is the first semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse_reflect_toSemigroup`: the
  positive half of the reflected group is the second semigroup.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.3.11.
-/

public section

noncomputable section

open scoped NNReal Topology

namespace TauCeti.Semigroups

namespace StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

variable (S T : StronglyContinuousSemigroup X)

omit [CompleteSpace X] in
/-- The operators of mutually inverse semigroups commute, also when their time parameters differ.
This is the cancellation step needed for the mixed-sign cases in the group law. -/
theorem comp_comm_of_inverse
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    (s t : ℝ≥0) : (S s).comp (T t) = (T t).comp (S s) := by
  ext x
  apply (Function.LeftInverse.injective (g := S s) fun y => by
    have h := congrArg (fun A : X →L[ℝ] X => A y) (hST s)
    simpa using h)
  calc
    T s (S s (T t x)) = T t x := by
      have h := congrArg (fun A : X →L[ℝ] X => A (T t x)) (hTS s)
      simpa using h
    _ = T t (T s (S s x)) := by
      have h := congrArg (fun A : X →L[ℝ] X => A x) (hTS s)
      simpa using congrArg (T t) h.symm
    _ = T s (T t (S s x)) := by
      rw [← T.map_add_apply, ← T.map_add_apply, add_comm]

/-- Evaluation of the piecewise operator family used to glue two semigroups. -/
private def inverseGluingFun (t : ℝ) : X →L[ℝ] X :=
  if 0 ≤ t then S.realOperator t else T.realOperator (-t)

omit [CompleteSpace X] in
private theorem inverseGluingFun_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    inverseGluingFun S T t = S.realOperator t := by
  simp [inverseGluingFun, ht]

omit [CompleteSpace X] in
private theorem inverseGluingFun_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    inverseGluingFun S T t = T.realOperator (-t) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [inverseGluingFun]
  · simp [inverseGluingFun, not_le.mpr ht]

omit [CompleteSpace X] in
private theorem inverseGluingFun_map_add
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    (s t : ℝ) :
    inverseGluingFun S T (s + t) =
      (inverseGluingFun S T s).comp (inverseGluingFun S T t) := by
  -- For equal signs this is one of the original semigroup laws. For mixed signs, split
  -- according to the sign of the sum, factor the longer-time operator, and cancel the inverse
  -- pair. The two mixed orders differ only by cross-commutation.
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · rw [inverseGluingFun_of_nonneg S T hs,
          inverseGluingFun_of_nonneg S T ht,
          inverseGluingFun_of_nonneg S T (add_nonneg hs ht)]
      exact S.realOperator_add s t hs ht
    · have ht' : t ≤ 0 := le_of_lt (not_le.mp ht)
      by_cases hst : 0 ≤ s + t
      · rw [inverseGluingFun_of_nonneg S T hs,
            inverseGluingFun_of_nonpos S T ht',
            inverseGluingFun_of_nonneg S T hst]
        ext x
        have hneg : 0 ≤ -t := neg_nonneg.mpr ht'
        have hmap : S.realOperator s =
            (S.realOperator (s + t)).comp (S.realOperator (-t)) := by
          have h := S.realOperator_add (s + t) (-t) hst hneg
          rw [show s + t + -t = s by ring] at h
          exact h
        rw [hmap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        have hinv : (S.realOperator (-t)).comp (T.realOperator (-t)) =
            ContinuousLinearMap.id ℝ X := by
          simpa only [S.realOperator_def, T.realOperator_def,
            Real.toNNReal_of_nonneg hneg] using hST (-t).toNNReal
        have hinvApply := congrArg (fun A : X →L[ℝ] X => A x) hinv
        rw [ContinuousLinearMap.comp_apply] at hinvApply
        simpa using (congrArg (S.realOperator (s + t)) hinvApply).symm
      · have hst' : s + t ≤ 0 := le_of_lt (not_le.mp hst)
        rw [inverseGluingFun_of_nonneg S T hs,
          inverseGluingFun_of_nonpos S T ht',
          inverseGluingFun_of_nonpos S T hst']
        ext x
        have hnegSum : 0 ≤ -(s + t) := neg_nonneg.mpr hst'
        have hmap : T.realOperator (-t) =
            (T.realOperator (-(s + t))).comp (T.realOperator s) := by
          have h := T.realOperator_add (-(s + t)) s hnegSum hs
          rw [show -(s + t) + s = -t by ring] at h
          exact h
        rw [hmap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        have hcomm : (S.realOperator s).comp (T.realOperator (-(s + t))) =
            (T.realOperator (-(s + t))).comp (S.realOperator s) := by
          simpa only [S.realOperator_def, T.realOperator_def, Real.toNNReal_of_nonneg hs,
            Real.toNNReal_of_nonneg hnegSum] using
            S.comp_comm_of_inverse T hST hTS s.toNNReal (-(s + t)).toNNReal
        have hcommApply := congrArg
          (fun A : X →L[ℝ] X => A (T.realOperator s x)) hcomm
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hcommApply
        rw [hcommApply]
        have hinv : (S.realOperator s).comp (T.realOperator s) =
            ContinuousLinearMap.id ℝ X := by
          simpa only [S.realOperator_def, T.realOperator_def,
            Real.toNNReal_of_nonneg hs] using hST s.toNNReal
        have hinvApply := congrArg (fun A : X →L[ℝ] X => A x) hinv
        rw [ContinuousLinearMap.comp_apply] at hinvApply
        simpa using (congrArg (T.realOperator (-(s + t))) hinvApply).symm
  · have hs' : s ≤ 0 := le_of_lt (not_le.mp hs)
    by_cases ht : 0 ≤ t
    · by_cases hst : 0 ≤ s + t
      · rw [inverseGluingFun_of_nonpos S T hs',
          inverseGluingFun_of_nonneg S T ht,
          inverseGluingFun_of_nonneg S T hst]
        ext x
        have hsneg : 0 ≤ -s := neg_nonneg.mpr hs'
        have hmap : S.realOperator t =
            (S.realOperator (s + t)).comp (S.realOperator (-s)) := by
          have h := S.realOperator_add (s + t) (-s) hst hsneg
          rw [show s + t + -s = t by ring] at h
          exact h
        have hcomm : (S.realOperator t).comp (T.realOperator (-s)) =
            (T.realOperator (-s)).comp (S.realOperator t) := by
          simpa only [S.realOperator_def, T.realOperator_def,
            Real.toNNReal_of_nonneg ht, Real.toNNReal_of_nonneg hsneg] using
            S.comp_comm_of_inverse T hST hTS t.toNNReal (-s).toNNReal
        rw [← hcomm, hmap, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.comp_apply]
        have hinv : (S.realOperator (-s)).comp (T.realOperator (-s)) =
            ContinuousLinearMap.id ℝ X := by
          simpa only [S.realOperator_def, T.realOperator_def,
            Real.toNNReal_of_nonneg hsneg] using hST (-s).toNNReal
        have hinvApply := congrArg (fun A : X →L[ℝ] X => A x) hinv
        rw [ContinuousLinearMap.comp_apply] at hinvApply
        simpa using (congrArg (S.realOperator (s + t)) hinvApply).symm
      · have hst' : s + t ≤ 0 := le_of_lt (not_le.mp hst)
        rw [inverseGluingFun_of_nonpos S T hs',
          inverseGluingFun_of_nonneg S T ht,
          inverseGluingFun_of_nonpos S T hst']
        ext x
        have hnegSum : 0 ≤ -(s + t) := neg_nonneg.mpr hst'
        have hsneg : 0 ≤ -s := neg_nonneg.mpr hs'
        have hmap : T.realOperator (-s) =
            (T.realOperator (-(s + t))).comp (T.realOperator t) := by
          have h := T.realOperator_add (-(s + t)) t hnegSum ht
          rw [show -(s + t) + t = -s by ring] at h
          exact h
        rw [hmap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        have hinv : (T.realOperator t).comp (S.realOperator t) =
            ContinuousLinearMap.id ℝ X := by
          simpa only [S.realOperator_def, T.realOperator_def,
            Real.toNNReal_of_nonneg ht] using hTS t.toNNReal
        have hinvApply := congrArg (fun A : X →L[ℝ] X => A x) hinv
        rw [ContinuousLinearMap.comp_apply] at hinvApply
        simpa using (congrArg (T.realOperator (-(s + t))) hinvApply).symm
    · have ht' : t ≤ 0 := le_of_lt (not_le.mp ht)
      have hst : s + t ≤ 0 := add_nonpos hs' ht'
      rw [inverseGluingFun_of_nonpos S T hs',
        inverseGluingFun_of_nonpos S T ht',
        inverseGluingFun_of_nonpos S T hst]
      have hsneg : 0 ≤ -s := neg_nonneg.mpr hs'
      have htneg : 0 ≤ -t := neg_nonneg.mpr ht'
      have hsum : -(s + t) = -s + -t := by ring
      rw [hsum, T.realOperator_add (-s) (-t) hsneg htneg]

private theorem continuous_inverseGluingFun_apply (x : X) :
    Continuous fun t : ℝ => inverseGluingFun S T t x := by
  have h := continuous_if_le (f := fun _ : ℝ => (0 : ℝ)) (g := id)
    (f' := fun t : ℝ => S.realOperator t x)
    (g' := fun t : ℝ => T.realOperator (-t) x)
    continuous_const continuous_id (S.realOperator_continuousOn_Ici x)
    ((T.realOperator_continuousOn_Ici x).comp continuous_neg.continuousOn fun t ht => by
      simpa only [Set.mem_Ici] using neg_nonneg.mpr ht)
    (fun t ht => by simp only [id_eq] at ht; subst t; simp)
  simpa only [inverseGluingFun, id_eq, DFunLike.ite_apply] using h

/-- Glue two strongly continuous semigroups whose equal-time operators are mutual inverses into a
strongly continuous group. The first semigroup supplies nonnegative times and the second supplies
negative times, with time reflected at zero. -/
def toGroupOfInverse
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X) :
    StronglyContinuousGroup X where
  toFun := inverseGluingFun S T
  map_zero' := by simp [inverseGluingFun]
  map_add' := inverseGluingFun_map_add S T hST hTS
  continuousAt_zero' x := (continuous_inverseGluingFun_apply S T x).continuousAt

/-- At nonnegative time, the group obtained by gluing inverse semigroups is the first semigroup. -/
@[simp]
theorem toGroupOfInverse_apply_of_nonneg
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    {t : ℝ} (ht : 0 ≤ t) :
    S.toGroupOfInverse T hST hTS t = S.realOperator t :=
  inverseGluingFun_of_nonneg S T ht

/-- At nonpositive time, the group obtained by gluing inverse semigroups is the second semigroup
at the reflected time. -/
@[simp]
theorem toGroupOfInverse_apply_of_nonpos
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    {t : ℝ} (ht : t ≤ 0) :
    S.toGroupOfInverse T hST hTS t = T.realOperator (-t) :=
  inverseGluingFun_of_nonpos S T ht

/-- The forward semigroup of the group obtained by gluing inverse semigroups is the first
semigroup. -/
@[simp]
theorem toGroupOfInverse_toSemigroup
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X) :
    (S.toGroupOfInverse T hST hTS).toSemigroup = S := by
  ext t
  rw [StronglyContinuousGroup.toSemigroup_apply,
    toGroupOfInverse_apply_of_nonneg S T hST hTS t.coe_nonneg,
    S.realOperator_coe]

/-- The forward semigroup of the reflected group obtained by gluing inverse semigroups is the
second semigroup. -/
@[simp]
theorem toGroupOfInverse_reflect_toSemigroup
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X) :
    (S.toGroupOfInverse T hST hTS).reflect.toSemigroup = T := by
  ext t
  rw [StronglyContinuousGroup.toSemigroup_apply, StronglyContinuousGroup.reflect_apply,
    toGroupOfInverse_apply_of_nonpos S T hST hTS (neg_nonpos.mpr t.coe_nonneg), neg_neg,
    T.realOperator_coe]

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
