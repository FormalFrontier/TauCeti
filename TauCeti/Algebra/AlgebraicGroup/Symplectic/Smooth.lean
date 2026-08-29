/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lift

/-!
# Smoothness of the symplectic group

The coordinate algebra of the standard symplectic group `Sp_{2m}` is smooth over every
commutative ring. The infinitesimal lifting criterion turns a lift of a coordinate-algebra map
through a square-zero quotient into a lift of the corresponding symplectic matrix. The matrix
lift is supplied by
`TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`.

Finite presentation follows from the finite set of entries of the matrix equation
`X J_m X^T = J_m` cutting the symplectic group out of `GL_{2m}`.

## Main declarations

* `TauCeti.Symplectic.instSmoothCoordinateHopfAlgebra`: the coordinate algebra of `Sp_{2m}` is
  smooth over its ground ring.
* `TauCeti.Symplectic.smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`: the same result
  for the bundled finite-type commutative Hopf algebra.

## References

* SGA 3, Exposé XXII, for the split symplectic group scheme.
* The Stacks Project, Tags 00TH, 00TI, 00T2, and 00TN, for formal smoothness and smooth algebras.

This supplies the smoothness prerequisite for the `Sp_{2n}` reductivity worked example in Layer 6
of the ReductiveGroups roadmap.
-/

public section

open WithConv

namespace TauCeti.Symplectic

universe u v

noncomputable section

variable (R : Type u) [CommRing R] (m : Nat)

private theorem pointsMulEquivGLSymplectic_mapValue
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (phi : A →ₐ[R] B)
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointsMulEquivGLSymplectic R m (A := B)
        (AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi f) =
      GLSymplectic.map (Fin m) phi.toRingHom
        (pointsMulEquivGLSymplectic R m (A := A) f) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hlhs := coe_pointsMulEquivGLSymplectic R m
    (AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi f)
  have hrhs := coe_pointsMulEquivGLSymplectic R m f
  rw [pointsMulEquiv_mapValue] at hlhs
  rw [GLSymplecticFin.coe_map] at hlhs
  rw [GLSymplectic.coe_map]
  rw [hlhs, hrhs]
  simp only [coe_reindexGL, Matrix.GeneralLinearGroup.map_apply, Matrix.submatrix_apply]

/-- The symplectic coordinate algebra is formally smooth over its ground ring. -/
private instance instFormallySmoothCoordinateHopfAlgebra :
    Algebra.FormallySmooth R (coordinateHopfAlgebra R m) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  obtain ⟨t, ht⟩ :=
    GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot (l := Fin m) I hI
      (pointsMulEquivGLSymplectic R m (A := B ⧸ I) (toConv f))
  let g : WithConv (coordinateHopfAlgebra R m →ₐ[R] B) :=
    (pointsMulEquivGLSymplectic R m (A := B)).symm t
  refine ⟨g.ofConv, ?_⟩
  apply toConv_injective
  apply (pointsMulEquivGLSymplectic R m (A := B ⧸ I)).injective
  rw [← AlgHom.mapValue_apply]
  rw [pointsMulEquivGLSymplectic_mapValue]
  have hg : pointsMulEquivGLSymplectic R m (A := B) g = t :=
    (pointsMulEquivGLSymplectic R m (A := B)).apply_symm_apply t
  rw [hg]
  exact ht

/-- The coordinate algebra of `Sp_{2m}` is smooth over every commutative ring. -/
instance instSmoothCoordinateHopfAlgebra :
    Algebra.Smooth R (coordinateHopfAlgebra R m) := by
  have hfg : (definingHopfIdeal R m).toIdeal.FG := by
    rw [ConstantForm.definingHopfIdeal_toIdeal]
    apply Submodule.fg_span
    let f := fun ij : Fin (m + m) × Fin (m + m) ↦
      ConstantForm.relationMatrix R (m + m) (JFin m R) ij.1 ij.2
    refine (Set.finite_range f).subset ?_
    intro x hx
    obtain ⟨i, j, hij⟩ :=
      (ConstantForm.mem_relationSet_iff (R := R) (n := m + m) (C := JFin m R)).mp hx
    exact ⟨(i, j), hij⟩
  let _ : Algebra.FinitePresentation R (coordinateHopfAlgebra R m) :=
    Algebra.FinitePresentation.quotient hfg
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-type commutative Hopf algebra representing `Sp_{2m}` has smooth coordinate ring. -/
theorem smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra :
    smoothCommHopfAlgProperty R (finiteTypeCoordinateHopfAlgebra R m).obj := by
  rw [smoothCommHopfAlgProperty_iff, finiteTypeCoordinateHopfAlgebra_obj]
  infer_instance

end

end TauCeti.Symplectic
