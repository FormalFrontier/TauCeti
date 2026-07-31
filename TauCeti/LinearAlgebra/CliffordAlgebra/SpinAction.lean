/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
# The spin group acting on its quadratic space

Mathlib defines `spinGroup Q` inside `CliffordAlgebra Q` and proves that its conjugation action
preserves the range of the generating map `CliffordAlgebra.ι Q`. This file transports that action
through `TauCeti.CliffordAlgebra.ιRangeEquiv`, proves that it preserves `Q`, and packages the result
as `spinToOrthogonal Q : spinGroup Q →* QuadraticMap.orthogonalGroup Q`.

This is the representation underlying the double cover from the spin group to the special
orthogonal group. The determinant-one property and surjectivity require the later
Cartan--Dieudonné argument and are deliberately not asserted here.

## Main definitions

* `TauCeti.CliffordAlgebra.spinAction Q x` is the linear automorphism induced by conjugation by
  the spin element `x`.
* `TauCeti.CliffordAlgebra.spinToOrthogonal Q` is the resulting homomorphism into `O(Q)`.

## References

This supplies the action prerequisite for Layer 2, "The Pin and Spin groups and the double
covers", of `TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson
and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra

namespace TauCeti

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private def spinActionLinear (x : spinGroup Q) : M →ₗ[R] M where
  toFun m := ιInv Q ((x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q))
  map_add' a b := by simp [map_add, mul_add, add_mul]
  map_smul' r m := by
    rw [map_smul]
    rw [show (x : CliffordAlgebra Q) * (r • ι Q m) * star (x : CliffordAlgebra Q) =
      r • ((x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q)) by
        simp only [Algebra.smul_def, mul_assoc]
        simp_rw [Algebra.commutes r]
        noncomm_ring]
    exact map_smul (ιInv Q) r _

private theorem ι_spinActionLinear (x : spinGroup Q) (m : M) :
    ι Q (spinActionLinear Q x m) =
      (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) := by
  apply ι_ιInv_of_mem Q
  have h := spinGroup.involute_act_ι_mem_range_ι (x := spinGroup.toUnits x) x.2 m
  change involute (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) ∈ _ at h
  rwa [spinGroup.involute_eq x.2] at h

private theorem spinActionLinear_inv_apply (x : spinGroup Q) (m : M) :
    spinActionLinear Q x⁻¹ (spinActionLinear Q x m) = m := by
  apply ι_injective Q
  rw [ι_spinActionLinear, ι_spinActionLinear]
  change star (x : CliffordAlgebra Q) *
      ((x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q)) *
        star (star (x : CliffordAlgebra Q)) = ι Q m
  rw [star_star]
  calc
    star (x : CliffordAlgebra Q) *
          ((x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q)) *
          (x : CliffordAlgebra Q) =
        (star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q)) * ι Q m *
          (star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q)) := by noncomm_ring
    _ = ι Q m := by rw [spinGroup.star_mul_self_of_mem x.2, one_mul, mul_one]

/-- The action of a spin element on the generating vectors of its Clifford algebra, transported
back to the underlying module. It is characterized by
`spinAction_apply`, which identifies it with conjugation inside the Clifford algebra. -/
noncomputable def spinAction (x : spinGroup Q) : M ≃ₗ[R] M where
  toLinearMap := spinActionLinear Q x
  invFun := spinActionLinear Q x⁻¹
  left_inv := spinActionLinear_inv_apply Q x
  right_inv m := by simpa using spinActionLinear_inv_apply Q x⁻¹ m

/-- A spin element acts on a vector by conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_spinAction_apply (x : spinGroup Q) (m : M) :
    ι Q (spinAction Q x m) =
      (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) :=
  ι_spinActionLinear Q x m

/-- Conjugation by a spin element preserves the quadratic form. -/
@[simp]
theorem spinAction_map_app (x : spinGroup Q) (m : M) : Q (spinAction Q x m) = Q m := by
  apply algebraMap_injective Q
  rw [← ι_sq_scalar Q (spinAction Q x m), ← ι_sq_scalar Q m, ι_spinAction_apply]
  calc
    (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) *
          ((x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q)) =
        (x : CliffordAlgebra Q) * ι Q m *
          (star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q)) * ι Q m *
            star (x : CliffordAlgebra Q) := by noncomm_ring
    _ = (x : CliffordAlgebra Q) * (ι Q m * ι Q m) * star (x : CliffordAlgebra Q) := by
      rw [spinGroup.star_mul_self_of_mem x.2, mul_one]
      noncomm_ring
    _ = ι Q m * ι Q m := by
      rw [ι_sq_scalar]
      calc
        (x : CliffordAlgebra Q) * algebraMap R (CliffordAlgebra Q) (Q m) *
              star (x : CliffordAlgebra Q) =
            algebraMap R (CliffordAlgebra Q) (Q m) *
              ((x : CliffordAlgebra Q) * star (x : CliffordAlgebra Q)) := by
                rw [mul_assoc, Algebra.commutes (Q m) (star (x : CliffordAlgebra Q)), ← mul_assoc,
                  Algebra.commutes]
        _ = algebraMap R (CliffordAlgebra Q) (Q m) := by
          rw [spinGroup.mul_star_self_of_mem x.2, mul_one]

/-- The representation of the spin group on the quadratic space by Clifford conjugation. -/
noncomputable def spinToOrthogonal : spinGroup Q →* QuadraticMap.orthogonalGroup Q where
  toFun x := ⟨spinAction Q x, QuadraticMap.mem_orthogonalGroup_iff.mpr (spinAction_map_app Q x)⟩
  map_one' := by
    ext m
    apply ι_injective Q
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    change spinAction Q (x * y) m = spinAction Q x (spinAction Q y m)
    apply ι_injective Q
    rw [ι_spinAction_apply, ι_spinAction_apply, ι_spinAction_apply]
    change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) * ι Q m *
        star ((x : CliffordAlgebra Q) * (y : CliffordAlgebra Q)) =
      (x : CliffordAlgebra Q) *
        ((y : CliffordAlgebra Q) * ι Q m * star (y : CliffordAlgebra Q)) *
          star (x : CliffordAlgebra Q)
    rw [star_mul]
    noncomm_ring

@[simp]
theorem coe_spinToOrthogonal_apply (x : spinGroup Q) (m : M) :
    ((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      spinAction Q x m := by
  rw [spinToOrthogonal]
  rfl

end CliffordAlgebra
end TauCeti
