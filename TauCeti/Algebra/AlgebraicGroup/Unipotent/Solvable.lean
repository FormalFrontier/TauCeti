/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.RepresentationTheory.Unipotent.Solvable

/-!
# Solvability of geometrically unipotent affine groups

A finite-type affine group admits a faithful finite-dimensional comodule. If all its geometric
points are unipotent, their induced operators on this comodule are unipotent. Kolchin's theorem
then embeds the geometric point group in an upper-unitriangular matrix group, proving that it is
solvable.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable`: a
  geometrically unipotent finite-type affine group has a solvable group of geometric points.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This completes the point-group solvability implication needed in Layer 5 of the ReductiveGroups
roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- A geometrically unipotent finite-type affine group has a solvable group of geometric points.

No reducedness hypothesis is needed: faithfulness is used only to inject the abstract geometric
point group into its linear action, while Kolchin's theorem simultaneously upper-unitriangularizes
that action. -/
theorem geometricallySolvable [Algebra.FiniteType k H]
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H)) :
    geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.of k H) := by
  have hpoints := (geometricallyUnipotentPointsCommHopfAlgProperty_iff k
    (CommHopfAlgCat.of k H)).mp hH
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  let A := AlgebraicClosure k
  obtain ⟨M, n, b, hb⟩ :=
    Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hfaithful : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr hb
  let rho : Representation A (WithConv (H →ₐ[k] A)) (A ⊗[k] M) :=
    Comodule.pointsRepresentation (R := k) (H := H) (A := A) M
  have hinjective : Function.Injective rho.asGroupHom := by
    intro g h hgh
    apply Comodule.pointsAction_injective_of_isFaithful hfaithful
    have hrho : rho g = rho h := by
      simpa only [Representation.asGroupHom_apply] using congrArg Units.val hgh
    apply LinearEquiv.ext
    intro x
    have hlinear :
        (Comodule.pointsAction M g : A ⊗[k] M →ₗ[A] A ⊗[k] M) =
          (Comodule.pointsAction M h : A ⊗[k] M →ₗ[A] A ⊗[k] M) := by
      rw [Comodule.pointsAction_toLinearMap, Comodule.pointsAction_toLinearMap]
      simpa only [rho, Comodule.pointsRepresentation_apply] using hrho
    exact LinearMap.congr_fun hlinear x
  apply Representation.isSolvable_of_injective_of_isUnipotent rho hinjective
  intro g
  rw [Comodule.pointsRepresentation_apply]
  exact (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
    (hpoints g) (FGComoduleCat.of (R := k) (C := H) M)

end geometricallyUnipotentPointsCommHopfAlgProperty

end

end TauCeti
