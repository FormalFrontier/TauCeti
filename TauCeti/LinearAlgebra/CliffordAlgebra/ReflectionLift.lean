/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
-- Private: `Algebra.adjoin_eq_span` supplies multiplication closure for the Spin-group span.

/-!
# Lifting reflections to the Pin and Spin groups

When the inverse negative norm of a vector is a square, the vector can be rescaled to have norm
`-1`. It therefore defines an element of the Pin group whose twisted-conjugation action is the
reflection in the original vector. A pair of reflections needs only that the product of the
inverse norms be a square: rescaling one vector then gives a unitary even product and hence a
lift to the Spin group. Over a separably closed field, the required square conditions hold
automatically. When the quadratic form is nondegenerate, the same lifts show that the Spin group
linearly spans the even Clifford algebra, provided `2` is nonzero.

## Main results

* `CliffordAlgebra.reflection_mem_range_pinToOrthogonal_of_isSquare`: a reflection lifts
  through the Pin action when its normalization scalar is a square.
* `CliffordAlgebra.reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare`: a
  product of two reflections lifts through the Spin action when the product of its normalization
  scalars is a square. The version without the suffix is a separably closed-field corollary.
* `CliffordAlgebra.span_spinGroup_eq_even_of_span_anisotropic`: the Spin group spans the even
  Clifford algebra when anisotropic vectors span and pairs admit the required square
  normalization.
* `CliffordAlgebra.span_spinGroup_eq_even_of_isSquare`: the nondegenerate,
  characteristic-not-two corollary.
* `CliffordAlgebra.span_spinGroup_eq_even`: the separably closed-field corollary, for a
  nondegenerate form in characteristic different from two.

## References

This supplies the reflection-lift prerequisite for Layer 2's double-cover target and the
Spin-group spanning prerequisite for Layer 4's irreducibility target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`.
See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

universe u v

namespace CliffordAlgebra

open TauCeti

section Square

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- A chosen square root of a square. Both the single-reflection and the paired-reflection lifts
below rescale a vector by one of these, so the choice is made once here. -/
private noncomputable def sqrtOfIsSquare {a : K} (h : IsSquare a) : K :=
  Classical.choose h

private theorem sqrtOfIsSquare_mul_self {a : K} (h : IsSquare a) :
    sqrtOfIsSquare h * sqrtOfIsSquare h = a :=
  (Classical.choose_spec h).symm

private theorem sqrtOfIsSquare_smul_norm_eq_neg_one (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) : Q (sqrtOfIsSquare hv • v) = -1 := by
  rw [QuadraticMap.map_smul, smul_eq_mul, sqrtOfIsSquare_mul_self hv, neg_mul,
    invOf_mul_self]

private noncomputable def pinReflectionLift (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) : pinGroup Q :=
  ⟨ι Q (sqrtOfIsSquare hv • v), ι_mem_pinGroup (sqrtOfIsSquare_smul_norm_eq_neg_one Q v hv)⟩

private theorem sqrtOfIsSquare_smul_norm_eq_invOf (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    Q (sqrtOfIsSquare h • v) = ⅟(Q w) := by
  rw [QuadraticMap.map_smul, smul_eq_mul, sqrtOfIsSquare_mul_self h, mul_assoc,
    mul_comm (⅟(Q w)) (Q v), ← mul_assoc, invOf_mul_self, one_mul]

private theorem isUnit_sqrtOfIsSquare (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) : IsUnit (sqrtOfIsSquare h) := by
  rw [← isUnit_mul_self_iff, sqrtOfIsSquare_mul_self h]
  exact (isUnit_of_invertible (⅟(Q v))).mul (isUnit_of_invertible (⅟(Q w)))

private theorem reflection_smul_eq (a : K) (v : V) [Invertible (Q v)]
    [Invertible (Q (a • v))] :
    QuadraticMap.reflection Q (a • v) = QuadraticMap.reflection Q v := by
  have hcoeff : ⅟(Q (a • v)) * a * a = ⅟(Q v) := by
    rw [← mul_right_inj_of_invertible (c := Q v)]
    calc
      Q v * (⅟(Q (a • v)) * a * a) = ⅟(Q (a • v)) * (a * a * Q v) := by ring
      _ = ⅟(Q (a • v)) * Q (a • v) := by
        congr 1
        exact (QuadraticMap.map_smul Q a v).symm
      _ = 1 := invOf_mul_self _
      _ = Q v * ⅟(Q v) := (mul_invOf_self _).symm
  ext m
  rw [QuadraticMap.reflection_apply, QuadraticMap.reflection_apply,
    QuadraticMap.polar_smul_left]
  simp only [smul_eq_mul, smul_smul]
  congr 2
  calc
    ⅟(Q (a • v)) * (a * polar Q v m) * a =
        (⅟(Q (a • v)) * a * a) * polar Q v m := by ring
    _ = ⅟(Q v) * polar Q v m := by rw [hcoeff]

private theorem reflectionPairLift_mem_pinGroup (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    ι Q (sqrtOfIsSquare h • v) * ι Q w ∈ pinGroup Q := by
  have : Invertible (sqrtOfIsSquare h) :=
    (isUnit_sqrtOfIsSquare Q v w h).invertible
  have hnorm := sqrtOfIsSquare_smul_norm_eq_invOf Q v w h
  have : Invertible (Q (sqrtOfIsSquare h • v)) := by rw [hnorm]; infer_instance
  have hprod : Q (sqrtOfIsSquare h • v) * Q w = 1 := by
    rw [hnorm, invOf_mul_self]
  let x := unitι Q (sqrtOfIsSquare h • v) * unitι Q w
  have hx : (x : CliffordAlgebra Q) =
      ι Q (sqrtOfIsSquare h • v) * ι Q w := by
    simp only [x, Units.val_mul, coe_unitι]
  refine ⟨⟨x, mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _), hx⟩,
    (hx ▸ x.isUnit).mem_unitary_of_star_mul_self ?_⟩
  rw [star_mul, star_ι, star_ι, neg_mul_neg]
  calc
    (ι Q w * ι Q (sqrtOfIsSquare h • v)) *
        (ι Q (sqrtOfIsSquare h • v) * ι Q w) =
        ι Q w * (ι Q (sqrtOfIsSquare h • v) *
          ι Q (sqrtOfIsSquare h • v)) * ι Q w := by noncomm_ring
    _ = ι Q w * algebraMap K _ (Q (sqrtOfIsSquare h • v)) * ι Q w := by
      rw [ι_sq_scalar]
    _ = algebraMap K _ (Q (sqrtOfIsSquare h • v)) * (ι Q w * ι Q w) := by
      rw [← Algebra.commutes (Q (sqrtOfIsSquare h • v)) (ι Q w)]
      rw [mul_assoc]
    _ = algebraMap K _ (Q (sqrtOfIsSquare h • v)) * algebraMap K _ (Q w) := by
      rw [ι_sq_scalar]
    _ = algebraMap K _ (Q (sqrtOfIsSquare h • v) * Q w) := by rw [map_mul]
    _ = 1 := by rw [hprod, map_one]

private noncomputable def spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] (h : IsSquare (⅟(Q v) * ⅟(Q w))) : spinGroup Q :=
  ⟨ι Q (sqrtOfIsSquare h • v) * ι Q w,
    reflectionPairLift_mem_pinGroup Q v w h, ι_mul_ι_mem_evenOdd_zero Q _ _⟩

variable [Invertible (2 : K)]

private theorem pinToOrthogonal_pinReflectionLift (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) :
    pinToOrthogonal Q (pinReflectionLift Q v hv) =
      QuadraticMap.reflectionOrthogonal Q v := by
  apply Subtype.ext
  rw [QuadraticMap.coe_reflectionOrthogonal]
  apply LinearEquiv.ext
  intro m
  rw [pinReflectionLift, pinToOrthogonal_ι_apply (sqrtOfIsSquare_smul_norm_eq_neg_one Q v hv),
    QuadraticMap.reflection_apply, QuadraticMap.polar_smul_left, smul_eq_mul]
  simp only [smul_smul, sub_eq_add_neg]
  rw [mul_assoc (sqrtOfIsSquare hv) (polar Q v m) (sqrtOfIsSquare hv),
    mul_comm (polar Q v m) (sqrtOfIsSquare hv), ← mul_assoc,
    sqrtOfIsSquare_mul_self hv, neg_mul, neg_smul]

/-- If the required normalization scalar is a square, the reflection in `v` lifts through the Pin
action. -/
theorem reflection_mem_range_pinToOrthogonal_of_isSquare (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) :
    QuadraticMap.reflectionOrthogonal Q v ∈ (pinToOrthogonal Q).range := by
  rw [MonoidHom.mem_range]
  exact ⟨pinReflectionLift Q v hv, pinToOrthogonal_pinReflectionLift Q v hv⟩

/-- If the product of the required normalization scalars is a square, the product of the
reflections in `v` and `w` lifts through the Spin action. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare
    (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w ∈
        (spinToOrthogonal Q).range := by
  have : Invertible (sqrtOfIsSquare h) :=
    (isUnit_sqrtOfIsSquare Q v w h).invertible
  have hnorm := sqrtOfIsSquare_smul_norm_eq_invOf Q v w h
  have : Invertible (Q (sqrtOfIsSquare h • v)) := by rw [hnorm]; infer_instance
  rw [MonoidHom.mem_range]
  refine ⟨spinReflectionPairLift Q v w h, ?_⟩
  have hpin : pinToLipschitz Q (spinToPin Q (spinReflectionPairLift Q v w h)) =
      ⟨unitι Q (sqrtOfIsSquare h • v) * unitι Q w,
        mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ := by
    apply Subtype.ext
    apply Units.ext
    simp only [coe_pinToLipschitz_apply, coe_spinToPin_apply, spinReflectionPairLift,
      Units.val_mul, coe_unitι]
  have hlipschitz : lipschitzToOrthogonal Q
      ⟨unitι Q (sqrtOfIsSquare h • v) * unitι Q w,
        mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ =
      QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w := by
    have hmul :
        (⟨unitι Q (sqrtOfIsSquare h • v) * unitι Q w,
          mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ : lipschitzGroup Q) =
          (⟨unitι Q (sqrtOfIsSquare h • v),
            unitι_mem_lipschitzGroup _⟩ : lipschitzGroup Q) *
            ⟨unitι Q w, unitι_mem_lipschitzGroup _⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
    rw [hmul, map_mul, lipschitzToOrthogonal_unitι, lipschitzToOrthogonal_unitι]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal]
    exact congrArg (fun x : V ≃ₗ[K] V => x * QuadraticMap.reflection Q w)
      (reflection_smul_eq Q (sqrtOfIsSquare h) v)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [← pinToOrthogonal_spinToPin, coe_pinToOrthogonal_apply, hpin]
  exact (coe_lipschitzToOrthogonal_apply Q _ m).symm.trans
    (congrArg (fun y : QuadraticMap.orthogonalGroup Q => (y : V ≃ₗ[K] V) m) hlipschitz)

end Square

section IsSepClosed

variable {K : Type u} {V : Type v} [Field K] [IsSepClosed K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)] (Q : QuadraticForm K V)

/-- Over a separably closed field, every reflection in a vector of invertible norm lifts to
the Pin group. -/
theorem reflection_mem_range_pinToOrthogonal (v : V) [Invertible (Q v)] :
    QuadraticMap.reflectionOrthogonal Q v ∈ (pinToOrthogonal Q).range := by
  exact reflection_mem_range_pinToOrthogonal_of_isSquare Q v
    (IsSepClosed.exists_eq_mul_self (-⅟(Q v)))

/-- Over a separably closed field, every product of two reflections in vectors of invertible
norm lifts to the Spin group. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal
    (v w : V) [Invertible (Q v)] [Invertible (Q w)] :
    QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w ∈
        (spinToOrthogonal Q).range := by
  exact reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare Q v w
    (IsSepClosed.exists_eq_mul_self (⅟(Q v) * ⅟(Q w)))

/-! ### Linear generation of the even Clifford algebra -/

omit [IsSepClosed K] [Invertible (2 : K)] in
private theorem mem_span_anisotropic [NeZero (2 : K)] (hQ : Q.Nondegenerate) (x : V) :
    x ∈ Submodule.span K {v | Q v ≠ 0} := by
  classical
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  rcases eq_or_ne x 0 with rfl | hx
  · exact Submodule.zero_mem _
  by_cases hxQ : Q x = 0
  · have hxrad : x ∉ Q.radical := by
      rw [hQ.radical_eq_bot, Submodule.mem_bot]
      exact hx
    have hxker : x ∉ Q.polarBilin.ker := by
      rw [← Q.radical_eq_ker_polarBilin]
      exact hxrad
    obtain ⟨y, hxy⟩ : ∃ y, polar Q x y ≠ 0 := by
      rw [LinearMap.mem_ker, LinearMap.ext_iff] at hxker
      push Not at hxker
      simpa only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] using hxker
    let y' := if _hy : Q y = 0 then x + y else y
    have hy'Q : Q y' ≠ 0 := by
      dsimp only [y']
      split_ifs with hyQ
      · simpa only [polar, hxQ, hyQ, sub_zero, sub_self] using hxy
      · exact hyQ
    have hxy' : polar Q x y' ≠ 0 := by
      dsimp only [y']
      split_ifs with hyQ
      · simpa only [polar_add_right, polar_self, hxQ, smul_zero, zero_add] using hxy
      · exact hxy
    let a := polar Q x y' / Q y'
    have ha : a ≠ 0 := div_ne_zero hxy' hy'Q
    let z := x + a • y'
    have hzQ_eq : Q z = 2 * (polar Q x y') ^ 2 / Q y' := by
      dsimp only [z, a]
      rw [QuadraticMap.map_add Q, Q.map_smul, polar_smul_right, hxQ, zero_add]
      simp only [smul_eq_mul]
      field_simp [hy'Q]
      ring
    have hzQ : Q z ≠ 0 := by
      rw [hzQ_eq]
      exact div_ne_zero (mul_ne_zero (NeZero.ne (2 : K)) (pow_ne_zero 2 hxy')) hy'Q
    have hy'mem : y' ∈ Submodule.span K {v | Q v ≠ 0} :=
      Submodule.subset_span hy'Q
    have hzmem : z ∈ Submodule.span K {v | Q v ≠ 0} :=
      Submodule.subset_span hzQ
    have hsub := Submodule.sub_mem _ hzmem (Submodule.smul_mem _ a hy'mem)
    simpa only [z, add_sub_cancel_right] using hsub
  · exact Submodule.subset_span hxQ

omit [IsSepClosed K] [Invertible (2 : K)] in
private theorem mul_mem_span_spinGroup {x y : CliffordAlgebra Q}
    (hx : x ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)))
    (hy : y ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q))) :
    x * y ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) := by
  rw [← Submonoid.closure_eq (spinGroup Q), ← Algebra.adjoin_eq_span] at hx hy ⊢
  exact (Algebra.adjoin K (spinGroup Q : Set (CliffordAlgebra Q))).mul_mem hx hy

omit [IsSepClosed K] [Invertible (2 : K)] in
private theorem ι_mul_ι_mem_span_spinGroup_of_ne_zero
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (v w : V) (hv : Q v ≠ 0)
    (hw : Q w ≠ 0) :
    ι Q v * ι Q w ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) := by
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  let h : IsSquare (⅟(Q v) * ⅟(Q w)) := by
    simpa only [invOf_eq_inv] using hsq v w hv hw
  let a := sqrtOfIsSquare h
  have ha : IsUnit a := isUnit_sqrtOfIsSquare Q v w h
  let _ : Invertible a := ha.invertible
  let g := spinReflectionPairLift Q v w h
  have hg : (g : CliffordAlgebra Q) ∈
      Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) :=
    Submodule.subset_span g.2
  have hcoe : (g : CliffordAlgebra Q) = a • (ι Q v * ι Q w) := by
    simp only [g, spinReflectionPairLift, a, map_smul, smul_mul_assoc]
  have := Submodule.smul_mem _ (⅟a) hg
  rw [hcoe, invOf_smul_smul] at this
  exact this

omit [IsSepClosed K] [Invertible (2 : K)] in
private theorem ι_mul_ι_mem_span_spinGroup_of_span_anisotropic
    (hspan : Submodule.span K {v | Q v ≠ 0} = ⊤)
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (v w : V) :
    ι Q v * ι Q w ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) := by
  have hv : v ∈ Submodule.span K {x | Q x ≠ 0} := hspan.symm ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span K {x | Q x ≠ 0} := hspan.symm ▸ Submodule.mem_top
  induction hv, hw using Submodule.span_induction₂ with
  | mem_mem v w hv hw => exact ι_mul_ι_mem_span_spinGroup_of_ne_zero Q hsq v w hv hw
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ hx hy =>
      simpa only [map_add, add_mul] using Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy =>
      simpa only [map_add, mul_add] using Submodule.add_mem _ hx hy
  | smul_left r x y _ _ h =>
      simpa only [map_smul, smul_mul_assoc] using Submodule.smul_mem _ r h
  | smul_right r x y _ _ h =>
      simpa only [map_smul, mul_smul_comm] using Submodule.smul_mem _ r h

omit [IsSepClosed K] [Invertible (2 : K)] in
/-- **The Spin group linearly spans the even Clifford algebra** when anisotropic vectors span and
every pair of them admits the square normalization needed to lift it to the Spin group. -/
theorem span_spinGroup_eq_even_of_span_anisotropic
    (hspan : Submodule.span K {v | Q v ≠ 0} = ⊤)
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹)) :
    Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) = (even Q).toSubmodule := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun _ hx => spinGroup.mem_even hx
  · rintro x hx
    have hx' : x ∈ evenOdd Q 0 := by
      rw [← even_toSubmodule Q]
      exact hx
    refine even_induction (Q := Q) (motive := fun x _ =>
      x ∈ Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q))) ?_ ?_ ?_ x hx'
    · intro r
      have hone : (1 : CliffordAlgebra Q) ∈
          Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) :=
        Submodule.subset_span (one_mem (spinGroup Q))
      simpa only [Algebra.smul_def, mul_one] using Submodule.smul_mem _ r hone
    · intro x y hx hy ihx ihy
      exact Submodule.add_mem _ ihx ihy
    · intro v w x hx ih
      exact mul_mem_span_spinGroup (Q := Q)
        (ι_mul_ι_mem_span_spinGroup_of_span_anisotropic Q hspan hsq v w) ih

omit [IsSepClosed K] [Invertible (2 : K)] in
/-- **The Spin group linearly spans the even Clifford algebra** when every pair of anisotropic
vectors admits the square normalization, the form is nondegenerate, and `2` is nonzero. -/
theorem span_spinGroup_eq_even_of_isSquare [NeZero (2 : K)] (hQ : Q.Nondegenerate)
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹)) :
    Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) = (even Q).toSubmodule := by
  apply span_spinGroup_eq_even_of_span_anisotropic Q _ hsq
  exact eq_top_iff.2 fun x _ => mem_span_anisotropic Q hQ x

omit [Invertible (2 : K)] in
/-- **The Spin group linearly spans the even Clifford algebra** for a nondegenerate quadratic
form over a separably closed field of characteristic different from two. -/
theorem span_spinGroup_eq_even [NeZero (2 : K)] (hQ : Q.Nondegenerate) :
    Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) = (even Q).toSubmodule := by
  exact span_spinGroup_eq_even_of_isSquare Q hQ fun v w _ _ =>
    IsSepClosed.exists_eq_mul_self ((Q v)⁻¹ * (Q w)⁻¹)

end IsSepClosed

end CliffordAlgebra
