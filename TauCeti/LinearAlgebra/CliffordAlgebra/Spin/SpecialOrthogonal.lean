/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The Spin action on the special orthogonal group

The determinant of the twisted-conjugation action records the parity of a Lipschitz element on a
finite free module. Thus the conjugation action of an even element has determinant one. Outside
the finite-free case, Mathlib defines the determinant to be one, so the codomain restriction
remains canonical.

## Main definitions and results

* `CliffordAlgebra.spinToSpecialOrthogonal` is the Spin action with codomain restricted to
  the special orthogonal group.
* `CliffordAlgebra.ker_spinToSpecialOrthogonal` identifies its kernel with that of the
  orthogonal Spin action.
* `CliffordAlgebra.coe_spinToSpecialOrthogonal_apply` identifies its underlying action
  with the Spin action on the quadratic module.

## References

This advances Layer 2's double-cover target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]

private noncomputable def lipschitzDet (Q : QuadraticForm R M) :
    lipschitzGroup Q →* Rˣ :=
  LinearEquiv.det.comp ((QuadraticMap.orthogonalGroup Q).subtype.comp (lipschitzToOrthogonal Q))

private theorem lipschitzDet_pinToLipschitz (Q : QuadraticForm R M) (p : pinGroup Q) :
    lipschitzDet Q (pinToLipschitz Q p) =
      LinearEquiv.det
        (((pinToOrthogonal Q p : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)) := by
  rw [lipschitzDet]
  simp only [MonoidHom.comp_apply]
  congr 1
  apply LinearEquiv.ext
  intro m
  -- Expose the two underlying linear equivalences before using their public action equations.
  change (((lipschitzToOrthogonal Q (pinToLipschitz Q p) :
    QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m) = _
  rw [coe_lipschitzToOrthogonal_apply]
  rw [← coe_pinToOrthogonal_apply]

private theorem lipschitzDet_unitι [Module.Free R M] [Module.Finite R M]
    (Q : QuadraticForm R M) (v : M) [Invertible (Q v)] :
    lipschitzDet Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ = -1 := by
  rw [lipschitzDet]
  simp only [MonoidHom.comp_apply]
  have haction :
      (QuadraticMap.orthogonalGroup Q).subtype
          (lipschitzToOrthogonal Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩) =
        lipschitzVectorAction Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ := by
    apply LinearEquiv.ext
    exact coe_lipschitzToOrthogonal_apply Q _
  rw [haction, lipschitzVectorAction_unitι]
  exact QuadraticMap.det_reflection Q v

private theorem involute_eq_det_smul_of_mem_lipschitz [Module.Free R M] [Module.Finite R M]
    (Q : QuadraticForm R M) {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) :
    involute (Q := Q) (x : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨x, hx⟩)) * x := by
  -- Prove the parity formula on the generating reflections, then preserve it under the
  -- inverse, identity, and multiplication constructors of the Lipschitz closure.
  induction hx using Subgroup.closure_induction with
  | mem x hgen =>
      have hx : x ∈ lipschitzGroup Q := Subgroup.subset_closure hgen
      obtain ⟨v, hv⟩ := hgen
      let _ := x.invertible
      let _ : Invertible (ι Q v) := by rw [hv]; infer_instance
      let _ := invertibleOfInvertibleι Q v
      have hxv : x = unitι Q v := by
        apply Units.ext
        rw [coe_unitι]
        exact hv.symm
      have hxl : (⟨x, hx⟩ : lipschitzGroup Q) =
          ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ := Subtype.ext hxv
      -- The closure induction presents a unit; the involution theorem is stated on its value.
      change involute (Q := Q) (x : CliffordAlgebra Q) =
        algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨x, hx⟩)) * x
      rw [hxl, hxv, coe_unitι, involute_ι, lipschitzDet_unitι]
      simp
  | inv x hx ihx =>
      have hx' : x ∈ lipschitzGroup Q := hx
      have hu : Units.map (involute (Q := Q)) x =
          Units.map (algebraMap R (CliffordAlgebra Q)) (lipschitzDet Q ⟨x, hx'⟩) * x := by
        apply Units.ext
        simpa using ihx
      have huinv := congrArg Inv.inv hu
      have hval := congrArg Units.val huinv
      -- Expose the inverse subgroup element and unit values so `map_inv` can apply.
      change involute (Q := Q) (↑(x⁻¹) : CliffordAlgebra Q) =
        algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨x⁻¹, inv_mem hx'⟩)) *
          (↑(x⁻¹) : CliffordAlgebra Q)
      -- Identify the inverse in the subgroup before applying multiplicativity of the determinant.
      rw [show (⟨x⁻¹, inv_mem hx'⟩ : lipschitzGroup Q) =
        (⟨x, hx'⟩ : lipschitzGroup Q)⁻¹ from rfl, map_inv]
      rw [Algebra.commutes (↑((lipschitzDet Q ⟨x, hx'⟩)⁻¹) : R)
        (↑(x⁻¹) : CliffordAlgebra Q)]
      simpa using hval
  | one =>
      have hone : (1 : (CliffordAlgebra Q)ˣ) ∈ lipschitzGroup Q := one_mem _
      have honeeq : (⟨1, hone⟩ : lipschitzGroup Q) = 1 := rfl
      rw [honeeq]
      simp
  | mul x y hx hy ihx ihy =>
      have hx' : x ∈ lipschitzGroup Q := hx
      have hy' : y ∈ lipschitzGroup Q := hy
      have ihx' : involute (Q := Q) (x : CliffordAlgebra Q) =
          algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨x, hx'⟩)) * x := by
        simpa only using ihx
      have ihy' : involute (Q := Q) (y : CliffordAlgebra Q) =
          algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨y, hy'⟩)) * y := by
        simpa only using ihy
      -- Expose multiplication in the ambient Clifford algebra before combining the hypotheses.
      change involute (Q := Q) ((x : CliffordAlgebra Q) * y) =
        algebraMap R (CliffordAlgebra Q)
          (↑(lipschitzDet Q ((⟨x, hx'⟩ : lipschitzGroup Q) * ⟨y, hy'⟩))) *
            ((x : CliffordAlgebra Q) * y)
      rw [map_mul, ihx', ihy', map_mul]
      simp only [Units.val_mul, map_mul]
      rw [mul_assoc
        (algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨x, hx'⟩)))
        (x : CliffordAlgebra Q)]
      rw [← mul_assoc (x : CliffordAlgebra Q)
        (algebraMap R (CliffordAlgebra Q) (↑(lipschitzDet Q ⟨y, hy'⟩))) y]
      rw [← Algebra.commutes (↑(lipschitzDet Q ⟨y, hy'⟩) : R) (x : CliffordAlgebra Q)]
      noncomm_ring

private theorem mem_even_of_involute_eq (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx : involute x = x) : x ∈ even Q := by
  have hxmem : x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [(evenOdd_isCompl Q).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, o, ho, hsum⟩ := Submodule.mem_sup.mp hxmem
  rw [← hsum, map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have hozero : o = 0 := by
    apply (isUnit_of_invertible (2 : R)).smul_left_cancel.mp
    rw [smul_zero, two_smul]
    calc
      o + o = (e + o) - (e + -o) := by abel
      _ = 0 := by rw [hx]; abel
  rw [← hsum, hozero, add_zero]
  exact he

private theorem det_spinToOrthogonal_eq_one_of_finite_free
    [Module.Free R M] [Module.Finite R M] (Q : QuadraticForm R M) (x : spinGroup Q) :
    LinearEquiv.det
        (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)) = 1 := by
  let l : lipschitzGroup Q := pinToLipschitz Q (spinToPin Q x)
  have hlcoe : ((l : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (x : CliffordAlgebra Q) := by
    -- Expose both subgroup inclusions as values in the ambient Clifford algebra.
    change (((pinToLipschitz Q (spinToPin Q x) : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) = _
    rw [coe_pinToLipschitz_apply, coe_spinToPin_apply]
  have hdet : lipschitzDet Q l =
      LinearEquiv.det
        (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)) := by
    rw [lipschitzDet_pinToLipschitz, pinToOrthogonal_spinToPin]
  have hinv := involute_eq_det_smul_of_mem_lipschitz Q l.2
  rw [hlcoe, spinGroup.involute_eq x.2, hdet] at hinv
  have hscalar : algebraMap R (CliffordAlgebra Q)
      (↑(LinearEquiv.det
        (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)))) =
      1 := by
    have hxunit : IsUnit (x : CliffordAlgebra Q) := by
      rw [← hlcoe]
      exact (l : (CliffordAlgebra Q)ˣ).isUnit
    apply hxunit.mul_right_cancel
    simpa using hinv.symm
  apply Units.ext
  apply algebraMap_injective Q
  exact hscalar.trans (map_one (algebraMap R (CliffordAlgebra Q))).symm

private theorem det_spinToOrthogonal_eq_one (Q : QuadraticForm R M) (x : spinGroup Q) :
    LinearEquiv.det
        (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)) = 1 := by
  classical
  apply Units.ext
  rw [LinearEquiv.coe_det]
  -- Compare the underlying scalars before splitting on the determinant convention.
  change LinearMap.det
    (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) : M →ₗ[R] M) = 1
  refine LinearMap.det_cases
    (P := fun a : R ↦ a = 1)
    ((((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) : M →ₗ[R] M)) ?_ rfl
  · intro _ b
    let _ := Module.Free.of_basis b
    let _ := Module.Finite.of_basis b
    rw [LinearMap.det_toMatrix]
    simpa [LinearEquiv.coe_det] using
      congrArg Units.val (det_spinToOrthogonal_eq_one_of_finite_free Q x)

/-- A finite-free Pin element whose orthogonal action has determinant one is even. -/
theorem mem_even_of_det_pinToOrthogonal_eq_one [Module.Free R M] [Module.Finite R M]
    (Q : QuadraticForm R M) (p : pinGroup Q)
    (hdet : LinearEquiv.det
      (((pinToOrthogonal Q p : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M)) = 1) :
    (p : CliffordAlgebra Q) ∈ even Q := by
  let l : lipschitzGroup Q := pinToLipschitz Q p
  have hlcoe : ((l : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (p : CliffordAlgebra Q) := by
    -- Expose the nested Pin and Lipschitz subgroup coercions in the ambient Clifford algebra.
    change (((pinToLipschitz Q p : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) = _
    rw [coe_pinToLipschitz_apply]
  have hinv := involute_eq_det_smul_of_mem_lipschitz Q l.2
  rw [hlcoe, lipschitzDet_pinToLipschitz, hdet, Units.val_one, map_one, one_mul] at hinv
  exact mem_even_of_involute_eq Q hinv

/-- The conjugation action of the Spin group, restricted to the determinant-one orthogonal
automorphisms. -/
noncomputable def spinToSpecialOrthogonal (Q : QuadraticForm R M) :
    spinGroup Q →* QuadraticMap.specialOrthogonalGroup Q :=
  (((QuadraticMap.orthogonalGroup Q).subtype.comp (spinToOrthogonal Q)).codRestrict
    (QuadraticMap.specialOrthogonalGroup Q) fun x =>
      (QuadraticMap.mem_specialOrthogonalGroup_iff).2
        ⟨(spinToOrthogonal Q x).2, det_spinToOrthogonal_eq_one Q x⟩)

/-- Restricting the codomain of the Spin action to the special orthogonal group does not change
its kernel. -/
@[simp]
theorem ker_spinToSpecialOrthogonal (Q : QuadraticForm R M) :
    MonoidHom.ker (spinToSpecialOrthogonal Q) = MonoidHom.ker (spinToOrthogonal Q) := by
  rw [spinToSpecialOrthogonal, MonoidHom.ker_codRestrict,
    MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]

/-- A Spin element has the same underlying action whether regarded as orthogonal or special
orthogonal. -/
@[simp]
theorem coe_spinToSpecialOrthogonal_apply (Q : QuadraticForm R M) (x : spinGroup Q) (m : M) :
    (((spinToSpecialOrthogonal Q x : QuadraticMap.specialOrthogonalGroup Q) :
      M ≃ₗ[R] M) m) = spinVectorAction Q x m := by
  -- The codomain restriction does not change the underlying orthogonal action.
  change (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m) = _
  rw [coe_spinToOrthogonal_apply]

end CliffordAlgebra
