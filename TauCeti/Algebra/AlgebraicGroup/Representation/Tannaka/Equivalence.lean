/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Reconstruction
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism

/-!
# Tannakian reconstruction for affine group schemes

Let `H` be a commutative Hopf algebra over a field `k`, and let `A` be a commutative
`k`-algebra. This file identifies the `A`-valued points of `H` with the tensor automorphisms of
scalar extension on finite-dimensional `H`-comodules.

The remaining inverse direction in the reconstruction theorem is detected by matrix
coefficients. For a finite comodule `M`, every coefficient map is a comodule morphism from `M`
to a finite subcomodule of the regular comodule. Naturality compares an arbitrary tensor
automorphism on these two objects. Applying the counit then reads the comparison as the global
functional used to reconstruct the point, and the scalar-extended dual separates elements of
`A ⊗[k] M`.

## Main declarations

* `TauCeti.Tannaka.fgPointTensorIso_reconstructedPoint`: reconstruction is a right inverse to
  the point action.
* `TauCeti.Tannaka.endOfPoint_reconstructedPoint`: a reconstructed point acts through the
  corresponding tensor-automorphism component.
* `TauCeti.Tannaka.fgPointTensorIsoEquiv`: the Tannakian equivalence between algebra-valued
  points and tensor automorphisms of finite-comodule scalar extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
* `Mathlib/RepresentationTheory/Tannaka.lean`: the final `MulEquiv.ofBijective` packaging follows
  the finite-group Tannaka theorem there.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

private theorem counitEvaluation_matrixCoefficientSubcoalgebraHom
    (M : FGComoduleCat.{u, u, u} k H) (phi : Module.Dual k M) (z : A ⊗[k] M) :
    counitEvaluation k H A
        (Comodule.matrixCoefficientSubcoalgebra (R := k) (C := H)
          (M := M)).toRegularSubcomodule
        ((Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi).toLinearMap.baseChange A z) =
      Module.Dual.baseChange A phi z := by
  rw [counitEvaluation_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  have hcomp :
      (Coalgebra.counit (R := k) (A := H)).comp
          (SMulMemClass.subtype
            (Comodule.matrixCoefficientSubcoalgebra (R := k) (C := H)
              (M := M)).toRegularSubcomodule) ∘ₗ
        (Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi).toLinearMap =
      (Coalgebra.counit (R := k) (A := H)).comp
        (Comodule.matrixCoefficientHom (C := H) phi).toLinearMap := by
    ext m
    exact congrArg (Coalgebra.counit (R := k) (A := H))
      (Comodule.matrixCoefficientSubcoalgebraHom_apply_coe phi m)
  rw [hcomp, LinearMap.baseChange_comp]
  exact Comodule.counit_baseChange_matrixCoefficientHom (C := H) A phi z

private theorem scalarExtensionComponent_reconstructedPoint_tmul
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (M : FGComoduleCat.{u, u, u} k H) (m : M) :
    scalarExtensionComponent k H A
        (fgPointTensorIso k H A (reconstructedPoint k H A eta)) M (1 ⊗ₜ[k] m) =
      scalarExtensionComponent k H A eta M (1 ⊗ₜ[k] m) := by
  apply TauCeti.Module.Dual.eq_of_baseChange_eq (A := A)
  intro phi
  let D := Comodule.matrixCoefficientSubcoalgebra (R := k) (C := H) (M := M)
  let N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H) :=
    ⟨D.toRegularSubcomodule, Subcomodule.mem_finiteSubcomodules.mpr inferInstance⟩
  let q := Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi
  let f : M ⟶ finiteRegularObject k H N :=
    ⟨ComoduleCat.ofHom (R := k) (C := H) q⟩
  -- Naturality along the corestricted coefficient morphism moves the comparison from `M`
  -- to the finite regular subcomodule on which reconstruction is defined.
  have hnatural := LinearMap.congr_fun
    (scalarExtensionComponent_natural k H A eta f) (1 ⊗ₜ[k] m)
  simp only [LinearMap.comp_apply] at hnatural
  have hf_baseChange_tmul :
      f.hom.toLinearMap.baseChange A (1 ⊗ₜ[k] m) =
        1 ⊗ₜ[k] Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi m := by
    rw [LinearMap.baseChange_tmul]
    exact congrArg (fun n => (1 : A) ⊗ₜ[k] n)
      (ComoduleCat.ofHom_apply (R := k) (C := H) q m)
  have hpointAction :
      Comodule.pointsAction M (reconstructedPoint k H A eta) (1 ⊗ₜ[k] m) =
        Comodule.endOfPoint M (reconstructedPoint k H A eta).ofConv (1 ⊗ₜ[k] m) :=
    LinearMap.congr_fun
      (Comodule.pointsAction_toLinearMap M (reconstructedPoint k H A eta)) _
  -- Evaluate both components against `phi`: point action gives the reconstructed functional,
  -- while naturality and counit evaluation give the same local functional.
  calc
    Module.Dual.baseChange A phi
        (scalarExtensionComponent k H A
          (fgPointTensorIsoHom k H A (reconstructedPoint k H A eta)) M (1 ⊗ₜ[k] m)) =
        Module.Dual.baseChange A phi
          (Comodule.pointsAction M (reconstructedPoint k H A eta) (1 ⊗ₜ[k] m)) := by
            rw [fgPointTensorIsoHom_apply, scalarExtensionComponent_fgPointTensorIso]
            rfl
    _ = (reconstructedPoint k H A eta).ofConv
          (Comodule.matrixCoefficient (R := k) (C := H) phi m) := by
            rw [← TauCeti.Module.Dual.baseChangeEvaluation_one_tmul phi, hpointAction]
            simpa only [one_mul] using
              Comodule.baseChangeEvaluation_endOfPoint_tmul
                (reconstructedPoint k H A eta).ofConv (1 : A) (1 : A) phi m
    _ = globalFunctional k H A eta
          (Comodule.matrixCoefficient (R := k) (C := H) phi m) := by
            rw [reconstructedPoint_apply]
    _ = localFunctional k H A eta N
          (Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi m) := by
            rw [← globalFunctional_apply k H A eta N]
            congr 1
            simpa only [Comodule.matrixCoefficientHom_apply] using
              (Comodule.matrixCoefficientSubcoalgebraHom_apply_coe phi m).symm
    _ = counitEvaluation k H A N.1
          (scalarExtensionComponent k H A eta (finiteRegularObject k H N)
            (1 ⊗ₜ[k] Comodule.matrixCoefficientSubcoalgebraHom (C := H) phi m)) := by
            rw [localFunctional_apply]
    _ = counitEvaluation k H A N.1
          (f.hom.toLinearMap.baseChange A
            (scalarExtensionComponent k H A eta M (1 ⊗ₜ[k] m))) := by
            rw [← hf_baseChange_tmul, ← hnatural]
    _ = Module.Dual.baseChange A phi
          (scalarExtensionComponent k H A eta M (1 ⊗ₜ[k] m)) := by
            simpa only [f, q, N, D] using
              counitEvaluation_matrixCoefficientSubcoalgebraHom k H A M phi
                (scalarExtensionComponent k H A eta M (1 ⊗ₜ[k] m))

/-- The component of the point reconstructed from a tensor automorphism is the original
component on every finite-dimensional comodule. -/
private theorem scalarExtensionComponent_reconstructedPoint
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (M : FGComoduleCat.{u, u, u} k H) :
    scalarExtensionComponent k H A
        (fgPointTensorIso k H A (reconstructedPoint k H A eta)) M =
      scalarExtensionComponent k H A eta M := by
  apply (LinearMap.liftBaseChangeEquiv A).symm.injective
  apply LinearMap.ext
  intro m
  simpa only [LinearMap.liftBaseChangeEquiv_symm_apply] using
    scalarExtensionComponent_reconstructedPoint_tmul k H A eta M m

/-- The tensor automorphism induced by a reconstructed point is the original tensor
automorphism. Thus reconstruction is a right inverse to the tensor action of points. -/
@[simp]
theorem fgPointTensorIso_reconstructedPoint
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    fgPointTensorIso k H A (reconstructedPoint k H A eta) = eta := by
  apply scalarExtensionComponent_ext
  exact scalarExtensionComponent_reconstructedPoint k H A eta

/-- The action of a point reconstructed from a tensor automorphism is that automorphism's
component on every finite-dimensional comodule. -/
@[simp]
theorem endOfPoint_reconstructedPoint
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (M : FGComoduleCat.{u, u, u} k H) :
    Comodule.endOfPoint M (reconstructedPoint k H A eta).ofConv =
      scalarExtensionComponent k H A eta M := by
  rw [← Comodule.pointsAction_toLinearMap,
    ← scalarExtensionComponent_fgPointTensorIso,
    fgPointTensorIso_reconstructedPoint]

/-- Algebra-valued points of a commutative Hopf algebra over a field are equivalent to tensor
automorphisms of scalar extension on its finite-dimensional comodules. -/
noncomputable def fgPointTensorIsoEquiv :
    WithConv (H →ₐ[k] A) ≃*
      Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A) :=
  MulEquiv.ofBijective (fgPointTensorIsoHom k H A) ⟨
    Function.LeftInverse.injective (reconstructedPoint_fgPointTensorIso k H A),
    Function.RightInverse.surjective (fgPointTensorIso_reconstructedPoint k H A)⟩

/-- The Tannakian equivalence sends a point to its tensor action. -/
@[simp]
theorem fgPointTensorIsoEquiv_apply (g : WithConv (H →ₐ[k] A)) :
    fgPointTensorIsoEquiv k H A g = fgPointTensorIso k H A g :=
  (rfl)

/-- The inverse Tannakian equivalence reconstructs the point of a tensor automorphism. -/
@[simp]
theorem fgPointTensorIsoEquiv_symm_apply
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    (fgPointTensorIsoEquiv k H A).symm eta = reconstructedPoint k H A eta := by
  apply (fgPointTensorIsoEquiv k H A).injective
  rw [MulEquiv.apply_symm_apply, fgPointTensorIsoEquiv_apply,
    fgPointTensorIso_reconstructedPoint]

end TauCeti.Tannaka
