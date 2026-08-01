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

* `TauCeti.CliffordAlgebra.spinVectorAction Q x` is the linear automorphism induced by conjugation
  by the spin element `x`.
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

private noncomputable def spinConj :
    spinGroup Q →* CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  (DistribMulAction.toModuleAut R (CliffordAlgebra Q)).comp
    ((ConjAct.toConjAct.toMonoidHom).comp spinGroup.toUnits)

omit [Invertible (2 : R)] in
private theorem spinConj_apply (x : spinGroup Q) (a : CliffordAlgebra Q) :
    spinConj Q x a = (x : CliffordAlgebra Q) * a * star (x : CliffordAlgebra Q) := by
  -- `toModuleAut` has no application theorem reducing through a composed `MonoidHom`, so expose
  -- its underlying conjugation action before applying the public `ConjAct` simplification API.
  change ConjAct.toConjAct (spinGroup.toUnits x) • a = _
  simp [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct,
    ← spinGroup.star_eq_inv]

private theorem spinConj_map_range (x : spinGroup Q) :
    (LinearMap.range (ι Q)).map (spinConj Q x).toLinearMap = LinearMap.range (ι Q) := by
  exact spinGroup.conjAct_smul_range_ι (x := spinGroup.toUnits x) x.2

private noncomputable def spinConjRange (x : spinGroup Q) :
    LinearMap.range (ι Q) ≃ₗ[R] LinearMap.range (ι Q) :=
  (spinConj Q x).ofSubmodules _ _ (spinConj_map_range Q x)

private theorem coe_spinConjRange_apply (x : spinGroup Q) (a : LinearMap.range (ι Q)) :
    (spinConjRange Q x a : CliffordAlgebra Q) = spinConj Q x (a : CliffordAlgebra Q) :=
  by rw [spinConjRange, LinearEquiv.ofSubmodules_apply]

private noncomputable def spinConjRangeHom :
    spinGroup Q →* LinearMap.range (ι Q) ≃ₗ[R] LinearMap.range (ι Q) where
  toFun := spinConjRange Q
  map_one' := by
    ext a
    rw [coe_spinConjRange_apply]
    exact DFunLike.congr_fun (map_one (spinConj Q)) (a : CliffordAlgebra Q)
  map_mul' x y := by
    ext a
    rw [LinearEquiv.mul_apply, coe_spinConjRange_apply, coe_spinConjRange_apply,
      coe_spinConjRange_apply]
    exact DFunLike.congr_fun (map_mul (spinConj Q) x y) (a : CliffordAlgebra Q)

private theorem coe_spinConjRangeHom_apply (x : spinGroup Q) (a : LinearMap.range (ι Q)) :
    (spinConjRangeHom Q x a : CliffordAlgebra Q) = spinConj Q x (a : CliffordAlgebra Q) := by
  exact coe_spinConjRange_apply Q x a

private noncomputable def spinVectorActionHom : spinGroup Q →* M ≃ₗ[R] M where
  toFun x := (ιRangeEquiv Q).trans ((spinConjRangeHom Q x).trans (ιRangeEquiv Q).symm)
  map_one' := by
    ext m
    simp
  map_mul' x y := by
    ext m
    simp

/-- The action of a spin element on the generating vectors of its Clifford algebra, transported
back to the underlying module. It is characterized by
`ι_spinVectorAction_apply`, which identifies it with conjugation inside the Clifford algebra. -/
noncomputable def spinVectorAction (x : spinGroup Q) : M ≃ₗ[R] M :=
  spinVectorActionHom Q x

private theorem spinVectorAction_apply (x : spinGroup Q) (m : M) :
    spinVectorAction Q x m =
      (ιRangeEquiv Q).trans ((spinConjRangeHom Q x).trans (ιRangeEquiv Q).symm) m :=
  rfl

/-- A spin element acts on a vector by conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_spinVectorAction_apply (x : spinGroup Q) (m : M) :
    ι Q (spinVectorAction Q x m) =
      (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) :=
  by
    rw [spinVectorAction_apply, LinearEquiv.trans_apply,
      LinearEquiv.trans_apply, ι_ιRangeEquiv_symm_apply, coe_spinConjRangeHom_apply,
      coe_ιRangeEquiv_apply]
    exact spinConj_apply Q x (ι Q m)

/-- Conjugation by a spin element preserves the quadratic form. -/
@[simp]
theorem spinVectorAction_map_app (x : spinGroup Q) (m : M) :
    Q (spinVectorAction Q x m) = Q m := by
  apply algebraMap_injective Q
  rw [← ι_sq_scalar Q (spinVectorAction Q x m), ← ι_sq_scalar Q m,
    ι_spinVectorAction_apply]
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
  toFun x :=
    ⟨spinVectorAction Q x,
      QuadraticMap.mem_orthogonalGroup_iff.mpr (spinVectorAction_map_app Q x)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (spinVectorActionHom Q)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (spinVectorActionHom Q) x y

@[simp]
theorem coe_spinToOrthogonal_apply (x : spinGroup Q) (m : M) :
    ((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      spinVectorAction Q x m := by
  rw [spinToOrthogonal]
  rfl

end CliffordAlgebra
end TauCeti
