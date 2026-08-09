/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.PinAction

/-!
# Lifting reflections to the Pin and Spin groups

When the inverse negative norm of a vector is a square, the vector can be rescaled to have norm
`-1`. It therefore defines an element of the Pin group whose twisted-conjugation action is the
reflection in the original vector. A pair of reflections needs only that the product of the
inverse norms be a square: rescaling one vector then gives a unitary even product and hence a
lift to the Spin group. Over a separably closed field, the required square conditions hold
automatically.

## Main results

* `TauCeti.CliffordAlgebra.reflection_mem_range_pinToOrthogonal_of_isSquare`: a reflection lifts
  through the Pin action when its normalization scalar is a square.
* `TauCeti.CliffordAlgebra.reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare`: a
  product of two reflections lifts through the Spin action when the product of its normalization
  scalars is a square. The version without the suffix is a separably closed-field corollary.

## References

This supplies the reflection-lift prerequisite for Layer 2's "The double cover (the summit of the
layer), over ℂ" target in `TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`.
See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace CliffordAlgebra

section Square

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

private noncomputable def reflectionScale (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) : K :=
  Classical.choose hv

private theorem reflectionScale_mul_self (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) :
    reflectionScale Q v hv * reflectionScale Q v hv = -⅟(Q v) := by
  simpa only [reflectionScale] using (Classical.choose_spec hv).symm

private theorem reflectionScale_norm (v : V) [Invertible (Q v)] (hv : IsSquare (-⅟(Q v))) :
    Q (reflectionScale Q v hv • v) = -1 := by
  rw [QuadraticMap.map_smul, smul_eq_mul, reflectionScale_mul_self Q v hv, neg_mul,
    invOf_mul_self]

private noncomputable def pinReflectionLift (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) : pinGroup Q :=
  ⟨ι Q (reflectionScale Q v hv • v), ι_mem_pinGroup (reflectionScale_norm Q v hv)⟩

private noncomputable def reflectionPairScale (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) : K :=
  Classical.choose h

private theorem reflectionPairScale_mul_self (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    reflectionPairScale Q v w h * reflectionPairScale Q v w h = ⅟(Q v) * ⅟(Q w) := by
  simpa only [reflectionPairScale] using (Classical.choose_spec h).symm

private theorem reflectionPairScale_norm (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    Q (reflectionPairScale Q v w h • v) = ⅟(Q w) := by
  rw [QuadraticMap.map_smul, smul_eq_mul, reflectionPairScale_mul_self Q v w h, mul_assoc,
    mul_comm (⅟(Q w)) (Q v), ← mul_assoc, invOf_mul_self, one_mul]

private theorem reflectionPairScale_isUnit (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) : IsUnit (reflectionPairScale Q v w h) := by
  rw [← isUnit_mul_self_iff, reflectionPairScale_mul_self Q v w h]
  exact (isUnit_of_invertible (⅟(Q v))).mul (isUnit_of_invertible (⅟(Q w)))

private theorem reflection_smul_eq (a : K) [Invertible a] (v : V) [Invertible (Q v)]
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
    ι Q (reflectionPairScale Q v w h • v) * ι Q w ∈ pinGroup Q := by
  have : Invertible (reflectionPairScale Q v w h) :=
    (reflectionPairScale_isUnit Q v w h).invertible
  have hnorm := reflectionPairScale_norm Q v w h
  have : Invertible (Q (reflectionPairScale Q v w h • v)) := hnorm ▸ inferInstance
  have hprod : Q (reflectionPairScale Q v w h • v) * Q w = 1 := by
    rw [hnorm, invOf_mul_self]
  let x := unitι Q (reflectionPairScale Q v w h • v) * unitι Q w
  have hx : (x : CliffordAlgebra Q) =
      ι Q (reflectionPairScale Q v w h • v) * ι Q w := by
    simp only [x, Units.val_mul, coe_unitι]
  refine ⟨⟨x, mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _), hx⟩,
    (hx ▸ x.isUnit).mem_unitary_of_star_mul_self ?_⟩
  rw [star_mul, star_ι, star_ι, neg_mul_neg]
  calc
    (ι Q w * ι Q (reflectionPairScale Q v w h • v)) *
        (ι Q (reflectionPairScale Q v w h • v) * ι Q w) =
        ι Q w * (ι Q (reflectionPairScale Q v w h • v) *
          ι Q (reflectionPairScale Q v w h • v)) * ι Q w := by noncomm_ring
    _ = ι Q w * algebraMap K _ (Q (reflectionPairScale Q v w h • v)) * ι Q w := by
      rw [ι_sq_scalar]
    _ = algebraMap K _ (Q (reflectionPairScale Q v w h • v)) * (ι Q w * ι Q w) := by
      rw [← Algebra.commutes (Q (reflectionPairScale Q v w h • v)) (ι Q w)]
      rw [mul_assoc]
    _ = algebraMap K _ (Q (reflectionPairScale Q v w h • v)) * algebraMap K _ (Q w) := by
      rw [ι_sq_scalar]
    _ = algebraMap K _ (Q (reflectionPairScale Q v w h • v) * Q w) := by rw [map_mul]
    _ = 1 := by rw [hprod, map_one]

private noncomputable def spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] (h : IsSquare (⅟(Q v) * ⅟(Q w))) : spinGroup Q :=
  ⟨ι Q (reflectionPairScale Q v w h • v) * ι Q w,
    reflectionPairLift_mem_pinGroup Q v w h, ι_mul_ι_mem_evenOdd_zero Q _ _⟩

variable [Invertible (2 : K)]

private theorem pinToOrthogonal_pinReflectionLift (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) :
    pinToOrthogonal Q (pinReflectionLift Q v hv) =
      ⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [pinReflectionLift, pinToOrthogonal_ι_apply (reflectionScale_norm Q v hv),
    QuadraticMap.reflection_apply, QuadraticMap.polar_smul_left, smul_eq_mul]
  simp only [smul_smul, sub_eq_add_neg]
  rw [mul_assoc (reflectionScale Q v hv) (polar Q v m) (reflectionScale Q v hv),
    mul_comm (polar Q v m) (reflectionScale Q v hv), ← mul_assoc,
    reflectionScale_mul_self Q v hv, neg_mul, neg_smul]

/-- If the required normalization scalar is a square, the reflection in `v` lifts through the Pin
action. -/
theorem reflection_mem_range_pinToOrthogonal_of_isSquare (v : V) [Invertible (Q v)]
    (hv : IsSquare (-⅟(Q v))) :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) ∈ (pinToOrthogonal Q).range := by
  rw [MonoidHom.mem_range]
  exact ⟨pinReflectionLift Q v hv, pinToOrthogonal_pinReflectionLift Q v hv⟩

private theorem lipschitzToOrthogonal_unitι_eq (v : V) [Invertible (Q v)] :
    lipschitzToOrthogonal Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ =
      ⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_lipschitzToOrthogonal_apply, lipschitzVectorAction_unitι]

/-- If the product of the required normalization scalars is a square, the product of the
reflections in `v` and `w` lifts through the Spin action. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare
    (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (h : IsSquare (⅟(Q v) * ⅟(Q w))) :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ ∈
        (spinToOrthogonal Q).range := by
  have : Invertible (reflectionPairScale Q v w h) :=
    (reflectionPairScale_isUnit Q v w h).invertible
  have hnorm := reflectionPairScale_norm Q v w h
  have : Invertible (Q (reflectionPairScale Q v w h • v)) := hnorm ▸ inferInstance
  rw [MonoidHom.mem_range]
  refine ⟨spinReflectionPairLift Q v w h, ?_⟩
  have hpin : pinToLipschitz Q (spinToPin Q (spinReflectionPairLift Q v w h)) =
      ⟨unitι Q (reflectionPairScale Q v w h • v) * unitι Q w,
        mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ := by
    apply Subtype.ext
    apply Units.ext
    simp only [coe_pinToLipschitz_apply, coe_spinToPin_apply, spinReflectionPairLift,
      Units.val_mul, coe_unitι]
  have hlipschitz : lipschitzToOrthogonal Q
      ⟨unitι Q (reflectionPairScale Q v w h • v) * unitι Q w,
        mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ =
      (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ := by
    have hmul :
        (⟨unitι Q (reflectionPairScale Q v w h • v) * unitι Q w,
          mul_mem (unitι_mem_lipschitzGroup _) (unitι_mem_lipschitzGroup _)⟩ : lipschitzGroup Q) =
          (⟨unitι Q (reflectionPairScale Q v w h • v),
            unitι_mem_lipschitzGroup _⟩ : lipschitzGroup Q) *
            ⟨unitι Q w, unitι_mem_lipschitzGroup _⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
    rw [hmul,
      map_mul, lipschitzToOrthogonal_unitι_eq, lipschitzToOrthogonal_unitι_eq]
    apply Subtype.ext
    exact congrArg (fun x : V ≃ₗ[K] V => x * QuadraticMap.reflection Q w)
      (reflection_smul_eq Q (reflectionPairScale Q v w h) v)
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
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) ∈ (pinToOrthogonal Q).range := by
  exact reflection_mem_range_pinToOrthogonal_of_isSquare Q v
    (IsSepClosed.exists_eq_mul_self (-⅟(Q v)))

/-- Over a separably closed field, every product of two reflections in vectors of invertible
norm lifts to the Spin group. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal
    (v w : V) [Invertible (Q v)] [Invertible (Q w)] :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ ∈
        (spinToOrthogonal Q).range := by
  exact reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare Q v w
    (IsSepClosed.exists_eq_mul_self (⅟(Q v) * ⅟(Q w)))

end IsSepClosed

end CliffordAlgebra
end TauCeti
