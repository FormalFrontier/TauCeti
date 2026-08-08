/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.PinAction

/-!
# Lifting reflections to the Pin and Spin groups

When the inverse negative norm of a vector is a square, the vector can be rescaled to have norm
`-1`. It therefore defines an element of the Pin group whose twisted-conjugation action is the
reflection in the original vector. Multiplying two such lifts gives an even element and hence a
lift to the Spin group of the product of the two reflections. Over an algebraically closed field,
the required square conditions hold automatically.

## Main results

* `TauCeti.CliffordAlgebra.reflection_mem_range_pinToOrthogonal_of_isSquare`: a reflection lifts
  through the Pin action when its normalization scalar is a square.
* `TauCeti.CliffordAlgebra.reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare`: a
  product of two reflections lifts through the Spin action under the corresponding square
  conditions. The versions without the suffix are algebraically closed-field corollaries.

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

private noncomputable def spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] (hv : IsSquare (-⅟(Q v))) (hw : IsSquare (-⅟(Q w))) : spinGroup Q :=
  ⟨ι Q (reflectionScale Q v hv • v) * ι Q (reflectionScale Q w hw • w),
    ⟨mul_mem (ι_mem_pinGroup (reflectionScale_norm Q v hv))
        (ι_mem_pinGroup (reflectionScale_norm Q w hw)),
      ι_mul_ι_mem_evenOdd_zero Q _ _⟩⟩

omit [Invertible (2 : K)] in
private theorem spinToPin_spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] (hv : IsSquare (-⅟(Q v))) (hw : IsSquare (-⅟(Q w))) :
    spinToPin Q (spinReflectionPairLift Q v w hv hw) =
      pinReflectionLift Q v hv * pinReflectionLift Q w hw := by
  apply Subtype.ext
  rw [coe_spinToPin_apply]
  rfl

/-- If the two required normalization scalars are squares, the product of the reflections in `v`
and `w` lifts through the Spin action. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare
    (v w : V) [Invertible (Q v)] [Invertible (Q w)]
    (hv : IsSquare (-⅟(Q v))) (hw : IsSquare (-⅟(Q w))) :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ ∈
        (spinToOrthogonal Q).range := by
  rw [MonoidHom.mem_range]
  refine ⟨spinReflectionPairLift Q v w hv hw, ?_⟩
  rw [← pinToOrthogonal_spinToPin, spinToPin_spinReflectionPairLift Q v w hv hw, map_mul,
    pinToOrthogonal_pinReflectionLift Q v hv, pinToOrthogonal_pinReflectionLift Q w hw]

end Square

section IsAlgClosed

variable {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)] (Q : QuadraticForm K V)

/-- Over an algebraically closed field, every reflection in a vector of invertible norm lifts to
the Pin group. -/
theorem reflection_mem_range_pinToOrthogonal (v : V) [Invertible (Q v)] :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) ∈ (pinToOrthogonal Q).range := by
  exact reflection_mem_range_pinToOrthogonal_of_isSquare Q v
    (IsAlgClosed.exists_eq_mul_self (-⅟(Q v)))

/-- Over an algebraically closed field, every product of two reflections in vectors of invertible
norm lifts to the Spin group. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal
    (v w : V) [Invertible (Q v)] [Invertible (Q w)] :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ ∈
        (spinToOrthogonal Q).range := by
  exact reflection_mul_reflection_mem_range_spinToOrthogonal_of_isSquare Q v w
    (IsAlgClosed.exists_eq_mul_self (-⅟(Q v))) (IsAlgClosed.exists_eq_mul_self (-⅟(Q w)))

end IsAlgClosed

end CliffordAlgebra
end TauCeti
