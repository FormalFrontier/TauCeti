/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.PinAction

/-!
# Lifting reflections to the Pin and Spin groups

Over an algebraically closed field, a vector of invertible norm can be rescaled to have norm
`-1`. It therefore defines an element of the Pin group whose twisted-conjugation action is the
reflection in the original vector. Multiplying two such lifts gives an even element and hence a
lift to the Spin group of the product of the two reflections.

## Main results

* `TauCeti.CliffordAlgebra.reflection_mem_range_pinToOrthogonal`: a reflection in a vector of
  invertible norm belongs to the range of the Pin action.
* `TauCeti.CliffordAlgebra.reflection_mul_reflection_mem_range_spinToOrthogonal`: a product of two
  such reflections belongs to the range of the Spin action.

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

variable {K : Type u} {V : Type v} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

private noncomputable def reflectionScale (v : V) [Invertible (Q v)] : K :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self (-⅟(Q v)))

private theorem reflectionScale_mul_self (v : V) [Invertible (Q v)] :
    reflectionScale Q v * reflectionScale Q v = -⅟(Q v) := by
  simpa only [reflectionScale] using
    (Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (-⅟(Q v)))).symm

private theorem reflectionScale_norm (v : V) [Invertible (Q v)] :
    Q (reflectionScale Q v • v) = -1 := by
  rw [QuadraticMap.map_smul, smul_eq_mul, reflectionScale_mul_self, neg_mul,
    invOf_mul_self]

private noncomputable def pinReflectionLift (v : V) [Invertible (Q v)] : pinGroup Q :=
  ⟨ι Q (reflectionScale Q v • v), ι_mem_pinGroup (reflectionScale_norm Q v)⟩

variable [Invertible (2 : K)]

private theorem pinToOrthogonal_pinReflectionLift (v : V) [Invertible (Q v)] :
    pinToOrthogonal Q (pinReflectionLift Q v) =
      ⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [pinReflectionLift, pinToOrthogonal_ι_apply (reflectionScale_norm Q v),
    QuadraticMap.reflection_apply, QuadraticMap.polar_smul_left, smul_eq_mul]
  simp only [smul_smul, sub_eq_add_neg]
  rw [mul_assoc (reflectionScale Q v) (polar Q v m) (reflectionScale Q v),
    mul_comm (polar Q v m) (reflectionScale Q v), ← mul_assoc,
    reflectionScale_mul_self, neg_mul, neg_smul]

/-- Over an algebraically closed field, every reflection in a vector of invertible norm lifts to
the Pin group. -/
theorem reflection_mem_range_pinToOrthogonal (v : V) [Invertible (Q v)] :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) ∈ (pinToOrthogonal Q).range := by
  rw [MonoidHom.mem_range]
  exact ⟨pinReflectionLift Q v, pinToOrthogonal_pinReflectionLift Q v⟩

private noncomputable def spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] : spinGroup Q :=
  ⟨ι Q (reflectionScale Q v • v) * ι Q (reflectionScale Q w • w),
    ⟨mul_mem (ι_mem_pinGroup (reflectionScale_norm Q v))
        (ι_mem_pinGroup (reflectionScale_norm Q w)),
      ι_mul_ι_mem_evenOdd_zero Q _ _⟩⟩

omit [Invertible (2 : K)] in
private theorem spinToPin_spinReflectionPairLift (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] :
    spinToPin Q (spinReflectionPairLift Q v w) = pinReflectionLift Q v * pinReflectionLift Q w := by
  apply Subtype.ext
  rw [coe_spinToPin_apply]
  rfl

/-- Over an algebraically closed field, every product of two reflections in vectors of invertible
norm lifts to the Spin group. -/
theorem reflection_mul_reflection_mem_range_spinToOrthogonal (v w : V) [Invertible (Q v)]
    [Invertible (Q w)] :
    (⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q v⟩ :
        QuadraticMap.orthogonalGroup Q) *
      ⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ ∈
        (spinToOrthogonal Q).range := by
  rw [MonoidHom.mem_range]
  refine ⟨spinReflectionPairLift Q v w, ?_⟩
  rw [← pinToOrthogonal_spinToPin, spinToPin_spinReflectionPairLift, map_mul,
    pinToOrthogonal_pinReflectionLift, pinToOrthogonal_pinReflectionLift]

end CliffordAlgebra
end TauCeti
