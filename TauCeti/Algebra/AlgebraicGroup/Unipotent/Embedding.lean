/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UpperUnitriangular
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Induction
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Unipotent
import TauCeti.Algebra.Coalgebra.Comodule.PointAction
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin

/-!
# Embedding unipotent affine groups in upper-unitriangular groups

Let `H` be a reduced finite-type commutative Hopf algebra over an algebraically closed field `k`.
If every `k`-valued point of `H` is unipotent, Kolchin's common fixed vector theorem gives a
nonzero fixed vector in every nonzero finite-dimensional `H`-comodule. Point separation promotes
the pointwise fixed-vector equation to the comodule equation `v ↦ v ⊗ 1`. Induction on dimension
then produces a basis in which the coefficient matrix is upper unitriangular.

Applying this to a faithful finite-dimensional subcomodule of the regular comodule gives a closed
immersion of the represented affine group into some upper-unitriangular group `U_n`. The geometric
unipotence property implies the required hypothesis on `k`-points by extension to the chosen
algebraic closure.

Reducedness is explicit in this file because it is exactly the hypothesis used by point
separation. A future smooth-implies-geometrically-reduced theorem will discharge it for the
roadmap's smooth formulation.

## Main declarations

* `TauCeti.Comodule.hasNonzeroFixedVector_of_forall_isUnipotentPoint`: Kolchin's theorem promoted
  from point actions to a comodule fixed vector.
* `TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperUnitriangular_of_forall_isUnipotentPoint`:
  every finite-dimensional comodule has an upper-unitriangular basis.
* `TauCeti.Comodule.exists_isClosedImmersion_upperUnitriangular_of_forall_isUnipotentPoint`:
  the represented affine group embeds as a closed subgroup of some `U_n`.
* `TauCeti.Comodule.exists_isClosedImmersion_upperUnitriangular_of_geometricallyUnipotentPoints`:
  the same conclusion from the roadmap's geometric-point predicate.
* `TauCeti.Comodule.geometricallyUnipotentPoints_iff_exists_isClosedImmersion_upperUnitriangular`:
  the upper-unitriangular embedding characterization.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This closes the Kolchin and faithful-embedding step of Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap for reduced groups over an algebraically closed field.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open AlgebraicGeometry WithConv

universe u

noncomputable section

variable {k H M : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
variable [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- If every point of a reduced finite-type commutative Hopf algebra over an algebraically closed
field is unipotent, then every nonzero finite-dimensional comodule has a nonzero fixed vector. -/
theorem hasNonzeroFixedVector_of_forall_isUnipotentPoint
    [FiniteDimensional k M] [Nontrivial M]
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    HasNonzeroFixedVector k H M := by
  obtain ⟨w, hw, hfixed⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent
      (pointsRepresentation (A := k) M) fun g ↦ by
        rw [pointsRepresentation_apply]
        exact (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
          (hH g) (FGComoduleCat.of (R := k) (C := H) M)
  let e := TensorProduct.lid k M
  let v := e w
  rw [hasNonzeroFixedVector_iff]
  refine ⟨v, fun hv ↦ hw (e.injective hv), ?_⟩
  rw [coact_eq_tmul_one_iff_forall_pointsAction_tmul_eq (K := k)]
  intro g
  have haction := hfixed g
  rw [pointsRepresentation_apply] at haction
  rw [← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap]
  have hv : (1 : k) ⊗ₜ[k] v = w := by
    exact e.symm_apply_apply w
  simpa only [hv] using haction

/-- If all points are unipotent, every finite-dimensional comodule has a basis with upper
unitriangular coefficient matrix. -/
theorem exists_basis_coefficientMatrix_isUpperUnitriangular_of_forall_isUnipotentPoint
    [FiniteDimensional k M]
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    ∃ (n : ℕ) (b : _root_.Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperUnitriangular :=
  exists_basis_coefficientMatrix_isUpperUnitriangular_of_fixed_vectors fun V _ _ _ _ _ ↦
    hasNonzeroFixedVector_of_forall_isUnipotentPoint (M := V) hH

/-- A reduced finite-type affine group over an algebraically closed field whose points are all
unipotent embeds as a closed subgroup of an upper-unitriangular group. The witness includes the
faithful comodule and its upper-unitriangular basis. -/
theorem exists_isClosedImmersion_upperUnitriangular_of_forall_isUnipotentPoint
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    ∃ (M : Subcomodule k H H) (n : ℕ) (b : _root_.Module.Basis (Fin n) k M)
      (hb : (coefficientMatrix (C := H) b).IsUpperUnitriangular),
      IsClosedImmersion
        (upperUnitriangularCoordinateGroupSchemeHom (H := H) b hb).hom.hom.left := by
  obtain ⟨M, n, b, hb⟩ := exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := H)
  let _ : AddCommGroup M := _root_.Module.addCommMonoidToAddCommGroup k
  let _ : _root_.Module.Finite k M := _root_.Module.Finite.of_basis b
  have hfaithful : IsFaithful (k := k) (H := H) (V := M) :=
    (isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr hb
  obtain ⟨m, b', hb'⟩ :=
    exists_basis_coefficientMatrix_isUpperUnitriangular_of_forall_isUnipotentPoint
      (M := M) hH
  exact ⟨M, m, b', hb',
    (isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff_isFaithful b' hb').mpr
      hfaithful⟩

/-- Geometric unipotence implies that the represented reduced affine group embeds as a closed
subgroup of an upper-unitriangular group. -/
theorem exists_isClosedImmersion_upperUnitriangular_of_geometricallyUnipotentPoints
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H)) :
    ∃ (M : Subcomodule k H H) (n : ℕ) (b : _root_.Module.Basis (Fin n) k M)
      (hb : (coefficientMatrix (C := H) b).IsUpperUnitriangular),
      IsClosedImmersion
        (upperUnitriangularCoordinateGroupSchemeHom (H := H) b hb).hom.hom.left := by
  apply exists_isClosedImmersion_upperUnitriangular_of_forall_isUnipotentPoint
  intro g
  let φ : k →ₐ[k] AlgebraicClosure k := _root_.Algebra.ofId k (AlgebraicClosure k)
  have hgeom := (geometricallyUnipotentPointsCommHopfAlgProperty_iff k
    (CommHopfAlgCat.of k H)).mp hH
  exact (HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g φ φ.injective).mp
    (hgeom (AlgHom.mapValue (H := H) φ g))

/-- A reduced finite-type affine group over an algebraically closed field has only unipotent
points if and only if it admits a faithful upper-unitriangular representation, equivalently a
closed immersion into some `U_n`. -/
theorem geometricallyUnipotentPoints_iff_exists_isClosedImmersion_upperUnitriangular :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H) ↔
      ∃ (M : Subcomodule k H H) (n : ℕ) (b : _root_.Module.Basis (Fin n) k M)
        (hb : (coefficientMatrix (C := H) b).IsUpperUnitriangular),
        IsClosedImmersion
          (upperUnitriangularCoordinateGroupSchemeHom (H := H) b hb).hom.hom.left := by
  constructor
  · exact exists_isClosedImmersion_upperUnitriangular_of_geometricallyUnipotentPoints
  · rintro ⟨M, n, b, hb, hclosed⟩
    apply geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective k
      (CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom (H := H) b hb))
    · exact (isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff b hb).mp hclosed
    · exact UpperUnitriangular.geometricallyUnipotentPointsCommHopfAlgProperty_coordinateHopfAlgebra
        n k

end

end TauCeti.Comodule
