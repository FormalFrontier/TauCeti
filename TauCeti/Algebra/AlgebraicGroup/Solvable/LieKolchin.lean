/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Trigonalizable
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.RepresentationTheory.Unipotent.DerivedEigenvector
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Lie--Kolchin reduction to the derived subgroup

Let `H` be the coordinate Hopf algebra of a reduced affine group of finite type over an
algebraically closed field. This file proves the representation-theoretic reduction at the heart
of Lie--Kolchin: if the derived closed subgroup has only unipotent points, then every nonzero
finite-dimensional `H`-comodule has a weight vector, and every finite-dimensional comodule is
upper triangularizable.

The abstract argument applies to a representation `ρ` and a normal subgroup `N` containing the
commutator subgroup. Kolchin gives a nonzero vector fixed by `N`. The whole group preserves the
space of `N`-fixed vectors, and its action there factors through the commutative quotient `G/N`.
Simultaneous triangularization of commuting operators then gives a common eigenvector. For an
affine group, take `N` to be the points of the scheme-theoretic derived subgroup. Point
separation promotes the resulting point-stable eigenline to a one-dimensional subcomodule.

The remaining geometric step in the general Lie--Kolchin theorem is to prove that the derived
subgroup of a connected solvable affine group is unipotent.

## Main declarations

* `TauCeti.Comodule.hasNonzeroWeightVector_of_forall_isUnipotentPoint_derived`: unipotence of the
  derived subgroup supplies a weight vector in every nonzero finite-dimensional comodule.
* `TauCeti.Comodule.hasNonzeroWeightVector_of_geometricallyUnipotent_derived`: the same conclusion
  phrased using the geometric-unipotence object property.
* `exists_basis_coefficientMatrix_isUpperTriangular_of_forall_isUnipotentPoint_derived`:
  the resulting Lie--Kolchin upper-triangular basis.
* `exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallyUnipotent_derived`:
  the geometric-unipotence formulation of that basis theorem.

The corresponding declarations taking `I` and `hID` apply to any closed subgroup containing the
derived subgroup.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.
* A. Borel, *Linear Algebraic Groups*, Section 10.5.
-/

public section

open scoped TensorProduct

namespace TauCeti

open CategoryTheory WithConv

universe u v w

noncomputable section

namespace Comodule

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
variable [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

private theorem hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal_aux
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    [FiniteDimensional k V] [Nontrivial V]
    (I : HopfIdeal k H) (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H)
    (hI : ∀ g : WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    HasNonzeroWeightVector k H V := by
  let A := _root_.CommHopfAlgCat.of k H
  let Q := CommHopfAlgCat.quotient A I
  let q : H →ₐc[k] Q := (CommHopfAlgCat.mkQuotient A I).hom
  let G := HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)
  let N := CommHopfAlgCat.quotientPointsSubgroup A I (CommAlgCat.of k k)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal A I
    (CommHopfAlgCat.isNormal_of_le_derivedDefiningIdeal A I hID) (CommAlgCat.of k k)
  let rho : _root_.Representation k G (k ⊗[k] V) :=
    pointsRepresentation (R := k) (H := H) (A := k) V
  have hrho (g : G) : rho g = endOfPoint V g.ofConv := by
    simp only [rho, G, pointsRepresentation_apply]
  have hcomm : _root_.commutator G ≤ N :=
    CommHopfAlgCat.commutator_le_quotientPointsSubgroup_of_le_derivedDefiningIdeal
      A I hID (CommAlgCat.of k k)
  have hunipotent (n : N) : IsNilpotent (rho n - 1) := by
    obtain ⟨g, hg⟩ := n.2
    have hg' : HopfAlgebra.IsUnipotentPoint (AlgHom.mapDomain q g) :=
      (hI g).mapDomain q
    have hnil :=
      (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one
        (AlgHom.mapDomain q g)).mp hg'
        (FGComoduleCat.of (R := k) (C := H) V)
    have hinclude : CommHopfAlgCat.quotientPointsHom A I (CommAlgCat.of k k) g =
        AlgHom.mapDomain q g := by
      rw [CommHopfAlgCat.quotientPointsHom_apply, AlgHom.mapDomain_apply]
    have hn : (n : G) = AlgHom.mapDomain q g := hg.symm.trans hinclude
    rw [hrho n, hn]
    exact hnil
  obtain ⟨χ, w, hw, haction⟩ :=
    rho.exists_unitHom_jointEigenvector_of_commutator_le_of_isUnipotent N hcomm hunipotent
  let e := TensorProduct.lid k V
  let v := e w
  have hv : v ≠ 0 := e.map_ne_zero_iff.mpr hw
  have hv' : (1 : k) ⊗ₜ[k] v = w := by
    exact (TensorProduct.lid_symm_apply (R := k) v).symm.trans (e.symm_apply_apply w)
  have haction' (g : WithConv (H →ₐ[k] k)) :
      basePointsRepresentation (R := k) (H := H) V g v = (χ g : k) • v := by
    rw [basePointsRepresentation_apply, hv']
    have hg := haction g
    rw [hrho g] at hg
    rw [hg, map_smul]
  let p : Submodule k V := k ∙ v
  have hact (g : WithConv (H →ₐ[k] k)) {m : V} (hm : m ∈ p) :
      basePointsRepresentation (R := k) (H := H) V g m ∈ p := by
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    rw [map_smul, haction' g]
    exact p.smul_mem _ (p.smul_mem _ (Submodule.mem_span_singleton_self v))
  exact hasNonzeroWeightVector_of_basePointsRepresentation_stable p v hv rfl hact

/-- If a closed subgroup containing the derived subgroup acts unipotently, then every nonzero
finite-dimensional representation has a nonzero weight vector. -/
theorem hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal
    [FiniteDimensional k M] [Nontrivial M]
    (I : HopfIdeal k H) (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H)
    (hI : ∀ g : WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    HasNonzeroWeightVector k H M := by
  let e : M ≃ₗ[k] (Fin (Module.finrank k M) → k) := (Module.finBasis k M).equivFun
  let _ : Comodule k H (Fin (Module.finrank k M) → k) := Comodule.Transport e
  let _ : Nontrivial (Fin (Module.finrank k M) → k) := e.symm.toEquiv.nontrivial
  have hweight : HasNonzeroWeightVector k H (Fin (Module.finrank k M) → k) :=
    hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal_aux I hID hI
  obtain ⟨v, c, hv, hc, hvc⟩ := (hasNonzeroWeightVector_iff (k := k) (C := H)).mp hweight
  refine (hasNonzeroWeightVector_iff (k := k) (C := H)).mpr
    ⟨e.symm v, c, e.symm.map_ne_zero_iff.mpr hv, hc, ?_⟩
  have hmap := (Comodule.transportInvHom (R := k) (C := H) e).map_coact_apply v
  rw [hvc] at hmap
  simpa only [Comodule.transportInvHom_apply, Comodule.transportInvHom_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.map_tmul, LinearMap.id_apply] using hmap.symm

/-- If every point of the derived closed subgroup acts unipotently, then every nonzero
finite-dimensional representation has a nonzero weight vector.

This is the representation-theoretic reduction in Lie--Kolchin. The hypothesis concerns the
coordinate algebra `H / derivedDefiningIdeal H` of the scheme-theoretic derived subgroup, not
merely the abstract commutator subgroup of `H(k)`.
-/
theorem hasNonzeroWeightVector_of_forall_isUnipotentPoint_derived
    [FiniteDimensional k M] [Nontrivial M]
    (hderived : ∀ g : WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (CommHopfAlgCat.derivedDefiningIdeal (R := k) H) →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    HasNonzeroWeightVector k H M :=
  hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal
    (CommHopfAlgCat.derivedDefiningIdeal H) le_rfl hderived

/-- If a geometrically unipotent closed subgroup contains the derived subgroup, then every nonzero
finite-dimensional representation has a nonzero weight vector. -/
theorem hasNonzeroWeightVector_of_geometricallyUnipotent_of_le_derivedDefiningIdeal
    [FiniteDimensional k M] [Nontrivial M]
    (I : HopfIdeal k H) (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H)
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)) :
    HasNonzeroWeightVector k H M := by
  apply hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal I hID
  intro g
  let φ : k →ₐ[k] AlgebraicClosure k := _root_.Algebra.ofId k (AlgebraicClosure k)
  have hgeom := (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mp hI
  exact (HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g φ φ.injective).mp
    (hgeom (AlgHom.mapValue φ g))

/-- If the derived closed subgroup is geometrically unipotent, then every nonzero
finite-dimensional representation has a nonzero weight vector. -/
theorem hasNonzeroWeightVector_of_geometricallyUnipotent_derived
    [FiniteDimensional k M] [Nontrivial M]
    (hderived : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (CommHopfAlgCat.derivedDefiningIdeal (R := k) H))) :
    HasNonzeroWeightVector k H M :=
  hasNonzeroWeightVector_of_geometricallyUnipotent_of_le_derivedDefiningIdeal
    (CommHopfAlgCat.derivedDefiningIdeal H) le_rfl hderived

/-- If a unipotent closed subgroup contains the derived subgroup, then every finite-dimensional
representation admits an upper-triangular basis with characters on the diagonal. -/
theorem exists_basis_upperTriangular_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal
    [FiniteDimensional k M]
    (I : HopfIdeal k H) (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H)
    (hI : ∀ g : WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
    fun V _ _ _ _ _ ↦
      hasNonzeroWeightVector_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal
        (M := V) I hID hI

/-- **Lie--Kolchin under unipotence of the derived subgroup.** If every point of the derived
closed subgroup of a reduced finite-type affine group over an algebraically closed field is
unipotent, then every finite-dimensional representation admits a basis in which its coefficient
matrix is upper triangular, with characters on the diagonal. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_of_forall_isUnipotentPoint_derived
    [FiniteDimensional k M]
    (hderived : ∀ g : WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (CommHopfAlgCat.derivedDefiningIdeal (R := k) H) →ₐ[k] k),
      HopfAlgebra.IsUnipotentPoint g) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_upperTriangular_of_forall_isUnipotentPoint_of_le_derivedDefiningIdeal
    (CommHopfAlgCat.derivedDefiningIdeal H) le_rfl hderived

/-- If a geometrically unipotent closed subgroup contains the derived subgroup, then every
finite-dimensional representation admits an upper-triangular basis with characters on the
diagonal. -/
theorem exists_basis_upperTriangular_of_geometricallyUnipotent_of_le_derivedDefiningIdeal
    [FiniteDimensional k M]
    (I : HopfIdeal k H) (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H)
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
    fun V _ _ _ _ _ ↦
      hasNonzeroWeightVector_of_geometricallyUnipotent_of_le_derivedDefiningIdeal
        (M := V) I hID hI

/-- **Geometric Lie--Kolchin reduction.** If the derived closed subgroup of a reduced
finite-type affine group over an algebraically closed field is geometrically unipotent, then every
finite-dimensional representation admits an upper-triangular basis with characters on the
diagonal. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallyUnipotent_derived
    [FiniteDimensional k M]
    (hderived : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
        (CommHopfAlgCat.derivedDefiningIdeal (R := k) H))) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_upperTriangular_of_geometricallyUnipotent_of_le_derivedDefiningIdeal
    (CommHopfAlgCat.derivedDefiningIdeal H) le_rfl hderived

end Comodule

end

end TauCeti
