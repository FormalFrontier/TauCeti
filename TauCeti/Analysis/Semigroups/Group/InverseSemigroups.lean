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
* `TauCeti.Semigroups.StronglyContinuousGroup.eq_toGroupOfInverse`: conversely, a C₀-group is the
  group glued from its own two halves, so gluing is inverse to splitting.

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
/-- The real-time, pointwise form of the inverse hypothesis. Negative times are covered too, both
operators then being the identity. -/
private theorem realOperator_apply_realOperator_of_inverse
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X) (a : ℝ) (x : X) :
    S.realOperator a (T.realOperator a x) = x := by
  have h := congrArg (fun A : X →L[ℝ] X => A x) (hST a.toNNReal)
  simpa [S.realOperator_def, T.realOperator_def] using h

omit [CompleteSpace X] in
/-- The real-time form of `comp_comm_of_inverse`. -/
private theorem realOperator_comp_comm_of_inverse
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X) (a b : ℝ) :
    (S.realOperator a).comp (T.realOperator b) = (T.realOperator b).comp (S.realOperator a) := by
  rw [S.realOperator_def, T.realOperator_def]
  exact S.comp_comm_of_inverse T hST hTS a.toNNReal b.toNNReal

omit [CompleteSpace X] in
/-- Mixed-sign cancellation when the forward time is the longer one: the backward operator eats
part of the forward one and leaves the forward operator at the difference. -/
private theorem realOperator_comp_realOperator_of_le
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    (S.realOperator a).comp (T.realOperator b) = S.realOperator (a - b) := by
  have hsplit : S.realOperator a = (S.realOperator (a - b)).comp (S.realOperator b) := by
    have h := S.realOperator_add (a - b) b (sub_nonneg.mpr hab) hb
    rwa [show a - b + b = a by ring] at h
  ext x
  rw [ContinuousLinearMap.comp_apply, hsplit, ContinuousLinearMap.comp_apply,
    realOperator_apply_realOperator_of_inverse S T hST b]

omit [CompleteSpace X] in
/-- Mixed-sign cancellation when the backward time is the longer one: the forward operator is
absorbed and leaves the backward operator at the difference. -/
private theorem realOperator_comp_realOperator_of_ge
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (S.realOperator a).comp (T.realOperator b) = T.realOperator (b - a) := by
  have hsplit : T.realOperator b = (T.realOperator (b - a)).comp (T.realOperator a) := by
    have h := T.realOperator_add (b - a) a (sub_nonneg.mpr hab) ha
    rwa [show b - a + a = b by ring] at h
  ext x
  rw [ContinuousLinearMap.comp_apply, hsplit, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply,
    realOperator_comp_comm_of_inverse S T hST hTS a (b - a),
    ContinuousLinearMap.comp_apply,
    realOperator_apply_realOperator_of_inverse S T hST a]

omit [CompleteSpace X] in
private theorem inverseGluingFun_map_add
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    (s t : ℝ) :
    inverseGluingFun S T (s + t) =
      (inverseGluingFun S T s).comp (inverseGluingFun S T t) := by
  -- For equal signs this is one of the original semigroup laws. For mixed signs, put the two
  -- operators in the order `S ∘ T` and cancel the shorter time against the longer one; which of
  -- the two survives is decided by the sign of the sum.
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · rw [inverseGluingFun_of_nonneg S T hs,
          inverseGluingFun_of_nonneg S T ht,
          inverseGluingFun_of_nonneg S T (add_nonneg hs ht)]
      exact S.realOperator_add s t hs ht
    · have ht' : t ≤ 0 := le_of_lt (not_le.mp ht)
      rw [inverseGluingFun_of_nonneg S T hs, inverseGluingFun_of_nonpos S T ht']
      by_cases hst : 0 ≤ s + t
      · rw [inverseGluingFun_of_nonneg S T hst,
          realOperator_comp_realOperator_of_le S T hST (neg_nonneg.mpr ht') (by linarith),
          show s - -t = s + t by ring]
      · have hst' : s + t ≤ 0 := le_of_lt (not_le.mp hst)
        rw [inverseGluingFun_of_nonpos S T hst',
          realOperator_comp_realOperator_of_ge S T hST hTS hs (by linarith),
          show -t - s = -(s + t) by ring]
  · have hs' : s ≤ 0 := le_of_lt (not_le.mp hs)
    by_cases ht : 0 ≤ t
    · rw [inverseGluingFun_of_nonpos S T hs', inverseGluingFun_of_nonneg S T ht,
        ← realOperator_comp_comm_of_inverse S T hST hTS t (-s)]
      by_cases hst : 0 ≤ s + t
      · rw [inverseGluingFun_of_nonneg S T hst,
          realOperator_comp_realOperator_of_le S T hST (neg_nonneg.mpr hs') (by linarith),
          show t - -s = s + t by ring]
      · have hst' : s + t ≤ 0 := le_of_lt (not_le.mp hst)
        rw [inverseGluingFun_of_nonpos S T hst',
          realOperator_comp_realOperator_of_ge S T hST hTS ht (by linarith),
          show -s - t = -(s + t) by ring]
    · have ht' : t ≤ 0 := le_of_lt (not_le.mp ht)
      rw [inverseGluingFun_of_nonpos S T hs',
        inverseGluingFun_of_nonpos S T ht',
        inverseGluingFun_of_nonpos S T (add_nonpos hs' ht'),
        show -(s + t) = -s + -t by ring,
        T.realOperator_add (-s) (-t) (neg_nonneg.mpr hs') (neg_nonneg.mpr ht')]

omit [CompleteSpace X] in
private theorem continuousAt_inverseGluingFun_apply (x : X) :
    ContinuousAt (fun t : ℝ => inverseGluingFun S T t x) 0 := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · have hneg : ContinuousWithinAt (fun t : ℝ => -t) (Set.Iic 0) 0 :=
      continuousAt_neg.continuousWithinAt
    have hT := ContinuousWithinAt.comp_of_eq (f := fun t : ℝ => -t)
      (g := fun t : ℝ => T.realOperator t x) (s := Set.Iic 0) (t := Set.Ici 0)
      (x := 0) (y := 0) (T.realOperator_continuousWithinAt_zero x) hneg
      (fun t ht => by
        simp only [Set.mem_Iic] at ht
        simpa only [Set.mem_Ici] using neg_nonneg.mpr ht)
      neg_zero
    apply hT.congr
    · intro t ht
      rw [inverseGluingFun_of_nonpos S T ht]
      rfl
    · simp [inverseGluingFun]
  · apply (S.realOperator_continuousWithinAt_zero x).congr
    · intro t ht
      rw [inverseGluingFun_of_nonneg S T ht]
    · simp [inverseGluingFun]

omit [CompleteSpace X] in
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
  continuousAt_zero' x := continuousAt_inverseGluingFun_apply S T x

omit [CompleteSpace X] in
/-- At nonnegative time, the group obtained by gluing inverse semigroups is the first semigroup. -/
@[simp]
theorem toGroupOfInverse_apply_of_nonneg
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    {t : ℝ} (ht : 0 ≤ t) :
    S.toGroupOfInverse T hST hTS t = S.realOperator t :=
  inverseGluingFun_of_nonneg S T ht

omit [CompleteSpace X] in
/-- At nonpositive time, the group obtained by gluing inverse semigroups is the second semigroup
at the reflected time. -/
@[simp]
theorem toGroupOfInverse_apply_of_nonpos
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    {t : ℝ} (ht : t ≤ 0) :
    S.toGroupOfInverse T hST hTS t = T.realOperator (-t) :=
  inverseGluingFun_of_nonpos S T ht

omit [CompleteSpace X] in
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

omit [CompleteSpace X] in
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

namespace StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (U : StronglyContinuousGroup X)

/-- The forward semigroup of a C₀-group and the forward semigroup of its reflection satisfy the
first inverse hypothesis of
`TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse`. -/
theorem toSemigroup_comp_reflect_toSemigroup (t : ℝ≥0) :
    (U.toSemigroup t).comp (U.reflect.toSemigroup t) = ContinuousLinearMap.id ℝ X := by
  ext x
  simp

/-- The forward semigroup of a C₀-group and the forward semigroup of its reflection satisfy the
second inverse hypothesis of
`TauCeti.Semigroups.StronglyContinuousSemigroup.toGroupOfInverse`. -/
theorem reflect_toSemigroup_comp_toSemigroup (t : ℝ≥0) :
    (U.reflect.toSemigroup t).comp (U.toSemigroup t) = ContinuousLinearMap.id ℝ X := by
  ext x
  simp

/-- **Gluing is inverse to splitting.** A C₀-group whose forward semigroup is `S` and whose
reflected forward semigroup is `T` is the group glued from `S` and `T`. Together with
`toGroupOfInverse_toSemigroup` and `toGroupOfInverse_reflect_toSemigroup`, this identifies the
gluing construction as the two-sided inverse of splitting a C₀-group into its two halves, so a
group can be recognized as a glued group without repeating a sign split. -/
theorem eq_toGroupOfInverse (S T : StronglyContinuousSemigroup X)
    (hST : ∀ t, (S t).comp (T t) = ContinuousLinearMap.id ℝ X)
    (hTS : ∀ t, (T t).comp (S t) = ContinuousLinearMap.id ℝ X)
    (hS : U.toSemigroup = S) (hT : U.reflect.toSemigroup = T) :
    U = S.toGroupOfInverse T hST hTS := by
  ext t
  rcases le_or_gt 0 t with ht | ht
  · rw [StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonneg S T hST hTS ht, ← hS,
      U.toSemigroup_realOperator_of_nonneg ht]
  · rw [StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonpos S T hST hTS ht.le, ← hT,
      U.reflect_toSemigroup_realOperator_of_nonneg (neg_nonneg.mpr ht.le), neg_neg]

/-- Gluing the two halves of a C₀-group recovers the group. -/
theorem toGroupOfInverse_toSemigroup_reflect_toSemigroup :
    U.toSemigroup.toGroupOfInverse U.reflect.toSemigroup U.toSemigroup_comp_reflect_toSemigroup
      U.reflect_toSemigroup_comp_toSemigroup = U :=
  (U.eq_toGroupOfInverse _ _ _ _ rfl rfl).symm

end StronglyContinuousGroup

end TauCeti.Semigroups

end
