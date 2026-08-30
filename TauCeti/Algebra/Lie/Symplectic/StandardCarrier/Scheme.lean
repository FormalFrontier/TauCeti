/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight type-C carrier scheme

This file feeds the standard type-C Chevalley generators, integral lattice, and full set of
weights into the Kostant toral-closure construction. It defines the carrier, its numbered root
subgroups and weight torus, their bundled matrix-valued points, and the scheme-level pinning
relation.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, or that the
carrier is the separately constructed symplectic group scheme. Those statements remain part of
Layer 9 of the reductive-groups roadmap; see the scope disclaimer in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic`.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.SpStd

open LieAlgebra.Symplectic
open scoped TensorProduct
open scoped CategoryTheory.MonObj

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)


/-! ## The pinned carrier -/

section Carrier

open AlgebraicGeometry CategoryTheory

attribute [local instance high] Algebra.toModule

/-- The Hopf ideal cutting out the full-weight type-`C_(n+1)` carrier inside the standard
general linear group. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The defining ideal is the one supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal n =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) := by
  rw [definingIdeal]

/-- The full-weight Chevalley carrier of type `C_(n+1)`, obtained as the smallest closed subgroup
of the standard general linear group containing its numbered root subgroups and weight torus. -/
noncomputable abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The quotient-spectrum presentation of the full-weight type-`C_(n+1)` carrier. -/
theorem groupScheme_def :
    groupScheme n =
      CommHopfAlgCat.quotientSpec
        (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the type-`C_(n+1)` carrier into its ambient general linear group. -/
noncomputable def carrierι :
    groupScheme n ⟶ TauCeti.GeneralLinear.groupScheme ℤ ((n + 1) + (n + 1)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The ambient inclusion is the one supplied by the generic Kostant toral-closure
construction. -/
theorem carrierι_def :
    carrierι n =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) := by
  rw [carrierι]

/-- The type-`C_(n+1)` carrier is a closed subgroup scheme of its ambient general linear group. -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι n).hom.hom.left := by
  rw [carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- A numbered root subgroup of the type `C_(n+1)` carrier. -/
noncomputable def rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k

/-- The root subgroup is the one supplied by the generic Kostant toral-closure construction. -/
theorem rootSubgroup_def (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroup n k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k := by
  rw [rootSubgroup]

/-- The rank-`n+1` split weight torus in the type `C_(n+1)` carrier. Maximality is not asserted
here; see the scope disclaimer in the module documentation. -/
noncomputable def weightTorus :
    SplitTorus.groupScheme ℤ (Fin (n + 1)) ⟶ groupScheme n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The weight torus is the one supplied by the generic Kostant toral-closure construction. -/
theorem weightTorus_def :
    weightTorus n =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) := by
  rw [weightTorus]

/-- Including a numbered root subgroup into the ambient general linear group recovers its
represented Kostant root subgroup. -/
@[simp] theorem rootSubgroup_comp_carrierι (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroup n k ≫ carrierι n =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
        (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n) := by
  rw [rootSubgroup, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) k

/-- Including the split weight torus into the ambient general linear group recovers the torus of
the standard-module weights. -/
@[simp] theorem weightTorus_comp_carrierι :
    weightTorus n ≫ carrierι n =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) := by
  rw [weightTorus, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- Two morphisms out of the type-`C_(n+1)` carrier agree when they agree on every numbered root
subgroup and on the split weight torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (φ ψ : groupScheme n ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup n k ≫ φ = rootSubgroup n k ≫ ψ)
    (htorus : weightTorus n ≫ φ = weightTorus n ≫ ψ) :
    φ = ψ := by
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) φ ψ hroot htorus

/-- The matrix-valued points of the type `C_(n+1)` carrier. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- The points of the type-`C_(n+1)` carrier are cut out by its defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points n A =
      TauCeti.GeneralLinear.hopfIdealPointsSubgroup ((n + 1) + (n + 1)) (definingIdeal n) A := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def
    _ _ _ _ _ _ _ _ A

/-- A matrix is a point of the type-`C_(n+1)` carrier exactly when its associated convolution
point kills the carrier's defining Hopf ideal. -/
@[simp] theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
    g ∈ points n A ↔
      ∀ x ∈ definingIdeal n,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) ((n + 1) + (n + 1))).symm g).ofConv x =
          0 := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-- **The parametrized numbered root subgroup inside the type-`C_(n+1)` carrier points.** The
parameter is read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def rootSubgroupPoints (k : Fin (n + 1) ⊕ Fin (n + 1)) (A : Type v) [CommRing A] :
    Multiplicative A →* points n A :=
  MonoidHom.codRestrict
    ((TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator n)
      (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k (isNilpotent_rep_rootGenerator n k)
      (latticeBasis n)).comp
        (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom)
    (points n A) fun u => by
      rw [points]
      exact TauCeti.UniversalEnvelopingAlgebra.kostantGeneratedPointsSubgroup_le_toralPoints
        (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
        (latticeBasis n) (basisWeight n) A
        (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_mem_generatedPoints
          (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
          (latticeBasis n) A k _)

/-- A numbered root-subgroup point is the corresponding divided-power exponential matrix. -/
@[simp] theorem coe_rootSubgroupPoints (k : Fin (n + 1) ⊕ Fin (n + 1)) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints n k A u :
        _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
        (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := (rfl)

/-- **The split weight torus inside the type-`C_(n+1)` carrier points.** -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin (n + 1) → Aˣ) →* points n A :=
  MonoidHom.codRestrict
    (TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
      (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n))
    (points n A) fun s => by
      rw [points]
      exact TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_mem_toralPoints
        (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) (isNilpotent_rep_rootGenerator n)
        (latticeBasis n) (basisWeight n) A s

/-- A split-torus point is the diagonal matrix whose entries are its values on the standard-module
weights. -/
@[simp] theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) :
    (weightTorusPoints n A s :
        _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n) s := (rfl)

/-- The coordinate-algebra map representing a numbered root subgroup is surjective. -/
private theorem representedRootCoordinateMap_surjective
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        k (isNilpotent_rep_rootGenerator n k) (latticeBasis n)).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap_surjective _ _ _ _ _ _ _ _
    isUnit_one (rep_rootGenerator_latticeBasis n k)
    (rep_rootGenerator_rep_rootGenerator_eq_zero n k _)

/-- The root-subgroup coordinate map remains surjective after adjoining the weight torus. -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
    _ _ _ _ _ _ _ _ k (representedRootCoordinateMap_surjective n k)

/-- Every numbered root subgroup is a closed copy of the additive group. -/
instance isClosedImmersion_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsClosedImmersion (rootSubgroup n k).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral_of_surjective
    (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k
    (rootSubgroupCoordinateMap_surjective n k)

/-- The full-weight torus is a closed immersion into the type `C_(n+1)` carrier. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion (weightTorus n).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_basisWeight_eq_top n)

/-- The scheme-level pinning equation: conjugation by the weight torus acts on each numbered root
subgroup through the corresponding row of the type-`C` Cartan matrix, with negative rows on
lowering generators. -/
@[simp] theorem weightTorus_conj_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (rootSubgroup n k).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (rootGeneratorWeight n k) : A) * u)) ≫
        (rootSubgroup n k).hom.hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n) (isNilpotent_rep_rootGenerator n) A
    (fun j => lie_cartanGenerator_rootGenerator n k j) s u

end Carrier

end TauCeti.SpStd
