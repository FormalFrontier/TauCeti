/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.GeneratorRelations
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.KostantLattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.SpinWeight
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight type-B spin carrier

This file specializes the type-`Bₙ₊₁` spin representation to the canonical split quadratic
space `(M* × M) × ℚ`, where `M = Fin (n + 1) → ℚ`. Its exterior coordinate lattice has a
basis indexed by `Finset (Fin (n + 1))`; the simple-root Kostant form preserves this lattice,
and the resulting spin weights span the full simply connected character lattice.

These data define an explicit affine group scheme over `ℤ`: the smallest closed subgroup of
`GL_(2^(n+1))` containing the represented numbered root subgroups and the spin weight torus.
The same data provide its matrix-valued points and the conjugation equation expressing the
Cartan action on each numbered root subgroup.

No smoothness, reductivity, Borel subgroup, or comparison with an all-root Kostant form is
asserted. In particular, constructing and comparing the remaining nonsimple type-`B` root
subgroups is separate from this carrier construction.

## Main declarations

* `TauCeti.TypeBSpinCarrier.groupScheme`: the full-weight type-`B` spin carrier over `ℤ`.
* `TauCeti.TypeBSpinCarrier.rootSubgroup`: its numbered simple-root subgroup morphisms.
* `TauCeti.TypeBSpinCarrier.weightTorus`: its closed split weight torus.
* `TauCeti.TypeBSpinCarrier.points`: its matrix-valued points over a commutative ring.
* `TauCeti.TypeBSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints`: the torus conjugation
  equation on matrix-valued points.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate II.
* `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic`, for the corresponding type-`D`
  carrier. The type-`B` carrier instead uses the split odd representation, type-`B` lattice,
  and type-`B` root data.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.TypeBSpinCarrier

open AlgebraicGeometry CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ)

/-! ## The split spin representation and its lattice -/

/-- The canonical split polarization used by the type-`Bₙ₊₁` spin carrier. -/
noncomputable abbrev polarization := TauCeti.splitOddPolarization ℚ (n + 1)

/-- The coordinate basis of the first isotropic summand. -/
noncomputable abbrev polarizationBasis := TauCeti.splitOddBasis ℚ (n + 1)

/-- The distinguished norm-one vector in the orthogonal remainder. -/
noncomputable abbrev remainderOne := TauCeti.splitOddRemainderOne ℚ (n + 1)

/-- The rational spin representation of the numbered type-`Bₙ₊₁` generators. -/
noncomputable abbrev rep :=
  (polarization n).typeBSpinRep (polarizationBasis n) (remainderOne n)
    (TauCeti.splitOddForm_remainderOne ℚ (n + 1))

/-- The integral exterior coordinate lattice in the split spin module. -/
noncomputable abbrev lattice :=
  TauCeti.ExteriorAlgebra.integralLattice (polarizationBasis n)

/-- The dimension of the spin module, expressed as the cardinality of its exterior basis. -/
abbrev dimension := Fintype.card (Finset (Fin (n + 1)))

/-- The exterior coordinate basis, reindexed by a finite ordinal for the general-linear carrier. -/
noncomputable def latticeBasis :
    Module.Basis (Fin (dimension n)) ℤ (lattice n).toAddSubgroup :=
  (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n)).reindex
    (Fintype.equivFin (Finset (Fin (n + 1))))

/-- The sign set represented by a finite-ordinal spin-basis index. -/
noncomputable abbrev signSet (i : Fin (dimension n)) : Finset (Fin (n + 1)) :=
  (Fintype.equivFin (Finset (Fin (n + 1)))).symm i

/-- The simply connected type-`Bₙ₊₁` weight of a spin-basis vector. -/
noncomputable abbrev basisWeight (i : Fin (dimension n)) : Fin (n + 1) → ℤ :=
  TauCeti.DynkinType.typeBSpinWeight (signSet n i)

/-- A reindexed lattice-basis vector is the exterior basis vector of its sign set. -/
@[simp]
theorem coe_latticeBasis (i : Fin (dimension n)) :
    ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) =
      (polarizationBasis n).ExteriorAlgebra (signSet n i) := by
  rw [latticeBasis, Module.Basis.reindex_apply, signSet]
  exact TauCeti.ExteriorAlgebra.coe_integralLatticeBasis _ _

/-- Every represented numbered root generator is nilpotent. -/
theorem isNilpotent_rep_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsNilpotent (rep n
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily k))) :=
  ⟨2, (polarization n).typeBSpinRep_simpleRootGenerator_sq
    (polarizationBasis n) (remainderOne n)
    (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) k⟩

/-- The simple-generator type-`B` Kostant form preserves the exterior coordinate lattice. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ))
    (hu : u ∈ kostantForm (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)))
    (v : ExteriorAlgebra ℚ (polarization n).W) (hv : v ∈ lattice n) :
    rep n u v ∈ lattice n :=
  (polarization n).typeBSpinRep_kostantForm_apply_mem_integralLattice
    (polarizationBasis n) (remainderOne n)
    (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) hu hv

/-- The representation-theoretic coroot weight is the simply connected type-`B` spin weight. -/
theorem typeBSpinCorootWeight_eq_typeBSpinWeight (s : Finset (Fin (n + 1))) :
    SpinPolarizationData.typeBSpinCorootWeight s =
      TauCeti.DynkinType.typeBSpinWeight s := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [SpinPolarizationData.typeBSpinCorootWeight_last,
      TauCeti.DynkinType.typeBSpinWeight_apply]
    by_cases h : Fin.last n ∈ s <;> simp [h]
  · rw [SpinPolarizationData.typeBSpinCorootWeight_castSucc,
      TauCeti.DynkinType.typeBSpinWeight_apply]
    simp

/-- Every exterior basis vector has its named integral type-`B` spin weight. -/
theorem isCartanWeightVector_latticeBasis (i : Fin (dimension n)) :
    IsCartanWeightVector (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n)
      (basisWeight n i)
      ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
  rw [isCartanWeightVector_iff]
  intro j
  rw [coe_latticeBasis, _root_.UniversalEnvelopingAlgebra.ι_apply,
    SpinPolarizationData.typeBSpinRep_ι,
    SpinPolarizationData.spinAction_typeBQuadraticEquiv_typeBSimpleCorootGenerator_basis]
  rw [typeBSpinCorootWeight_eq_typeBSpinWeight]

/-- The full spin weights span the simply connected type-`B` character lattice. -/
theorem span_range_basisWeight_eq_top :
    Submodule.span ℤ (Set.range (basisWeight n)) = ⊤ := by
  have hrange :
      Set.range (fun i : Fin (dimension n) ↦
        TauCeti.DynkinType.typeBSpinWeight (signSet n i)) =
        Set.range (TauCeti.DynkinType.typeBSpinWeight (n := n + 1)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨signSet n i, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Fintype.equivFin (Finset (Fin (n + 1))) s, by simp [signSet]⟩
  rw [hrange, TauCeti.DynkinType.span_range_typeBSpinWeight_eq_top]

/-! ## The closed carrier and its pinned generators -/

/-- The Hopf ideal cutting out the full-weight type-`Bₙ₊₁` spin carrier. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  kostantToralDefiningIdeal
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- The full-weight type-`Bₙ₊₁` spin carrier over `ℤ`. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantToralGroupScheme
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- The quotient-spectrum presentation of the type-`Bₙ₊₁` spin carrier. -/
theorem groupScheme_def :
    groupScheme n = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n) := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the type-`Bₙ₊₁` spin carrier into its general-linear carrier. -/
noncomputable def carrierι :
    groupScheme n ⟶ TauCeti.GeneralLinear.groupScheme ℤ (dimension n) :=
  kostantToralGroupSchemeι
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- The spin carrier is a closed subgroup scheme of its ambient general linear group. -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι n).hom.hom.left :=
  isClosedImmersion_kostantToralGroupSchemeι _ _ _ _ _ _ _ _

/-- A positive or negative numbered simple-root subgroup of the spin carrier. -/
noncomputable def rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme n :=
  kostantRootSubgroupToToral
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) k

/-- Including a root subgroup into the ambient general linear group gives its exponential. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroup n k ≫ carrierι n =
      kostantRootSubgroup
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n) :=
  kostantRootSubgroupToToral_comp_ι _ _ _ _ _ _ _ _ k

/-- The represented split weight torus in the type-`Bₙ₊₁` spin carrier. -/
noncomputable def weightTorus :
    SplitTorus.groupScheme ℤ (Fin (n + 1)) ⟶ groupScheme n :=
  kostantWeightTorusToToral
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- Including the weight torus recovers the diagonal torus of spin weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus n ≫ carrierι n =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) :=
  kostantWeightTorusToToral_comp_ι _ _ _ _ _ _ _ _

/-- The full spin weights make the represented torus a closed subgroup scheme. -/
instance isClosedImmersion_weightTorus :
    IsClosedImmersion (weightTorus n).hom.hom.left :=
  isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_basisWeight_eq_top n)

/-- Morphisms out of the carrier agree on its root subgroups and weight torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme n ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup n k ≫ f = rootSubgroup n k ≫ g)
    (htorus : weightTorus n ≫ f = weightTorus n ≫ g) : f = g := by
  exact kostantToralGroupScheme_hom_ext _ _ _ _ _ _ _ _ f g hroot htorus

/-! ## Matrix-valued points -/

/-- The matrix-valued points of the type-`Bₙ₊₁` spin carrier. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :=
  kostantToralPointsSubgroup
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) A

/-- The carrier points are exactly the matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points n A =
      TauCeti.GeneralLinear.hopfIdealPointsSubgroup (dimension n) (definingIdeal n) A := by
  rw [points, definingIdeal]
  exact kostantToralPointsSubgroup_def _ _ _ _ _ _ _ _ A

/-- A matrix is a carrier point exactly when its associated convolution point kills the
defining Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
    g ∈ points n A ↔
      ∀ x ∈ definingIdeal n,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact mem_kostantToralPointsSubgroup_iff _ _ _ _ _ _ _ _ A g

/-- A numbered root-subgroup homomorphism on matrix-valued points. -/
noncomputable def rootSubgroupPoints (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type v) [CommRing A] : Multiplicative A →* points n A :=
  kostantToralRootSubgroupPoints
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) k A

/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (rootSubgroupPoints n k A u :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantRootSubgroupMatrix
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  exact coe_kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ k A u

/-- The split spin weight torus on matrix-valued carrier points. -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin (n + 1) → Aˣ) →* points n A :=
  kostantToralWeightTorusPoints
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) A

/-- A weight-torus point is the diagonal matrix obtained by evaluating each spin weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) :
    (weightTorusPoints n A s :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantTorusMatrix (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n) s := by
  exact coe_kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A s

/-! ## The Cartan action and pinning equation -/

/-- The Cartan weight of a positive or negative numbered simple-root generator. -/
def rootWeight : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) → ℤ
  | .inl i => CartanMatrix.B (n + 1) i
  | .inr i => -CartanMatrix.B (n + 1) i

/-- Each numbered root generator is a weight vector for the simple coroots. -/
theorem lie_coroot_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) (j : Fin (n + 1)) :
    ⁅TauCeti.typeBSimpleCorootGenerator (K := ℚ) j,
        TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k⁆ =
      ((rootWeight n k j : ℤ) : ℚ) •
        TauCeti.typeBSimpleRootGeneratorFamily k := by
  cases k with
  | inl i =>
      rw [TauCeti.typeBSimpleRootGeneratorFamily_inl]
      simpa only [rootWeight, Int.cast_smul_eq_zsmul] using
        TauCeti.typeBSimpleCorootGenerator_lie_root (K := ℚ) j i
  | inr i =>
      rw [TauCeti.typeBSimpleRootGeneratorFamily_inr]
      simpa only [rootWeight, Pi.neg_apply, Int.cast_neg, Int.cast_smul_eq_zsmul,
        neg_smul] using TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot (K := ℚ) j i

/-- Conjugation by the spin weight torus rescales each root-subgroup parameter by its root
character, on matrix-valued points. -/
@[simp]
theorem weightTorusPoints_conj_rootSubgroupPoints
    (k : Fin (n + 1) ⊕ Fin (n + 1)) (A : Type v) [CommRing A]
    (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n A s * rootSubgroupPoints n k A u *
        (weightTorusPoints n A s)⁻¹ =
      rootSubgroupPoints n k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (rootWeight n k) : A) * Multiplicative.toAdd u)) := by
  exact kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) (isCartanWeightVector_latticeBasis n)
    (lie_coroot_rootGenerator n k) A s u

/-- Conjugation by the spin weight torus rescales each root subgroup by its root character. -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n k).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (rootWeight n k) : A) * u)) ≫
        (rootSubgroup n k).hom.hom := by
  exact kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n)
    (isNilpotent_rep_rootGenerator n) A (lie_coroot_rootGenerator n k) s u

/-! ## Identification with the named simple roots -/

/-- The raising-generator weight is the corresponding simple root of the uniform pinned
type-`Bₙ₊₁` datum. -/
theorem rootWeight_inl_eq_root_simpleIndex (ht : (TauCeti.DynkinType.B (n + 1)).Valid)
    (i : Fin (n + 1)) :
    rootWeight n (.inl i) =
      ((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
        ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i) := by
  refine Eq.trans ?_
    (TauCeti.DynkinType.root_simpleIndex (TauCeti.DynkinType.B (n + 1)) ht i).symm
  rw [TauCeti.DynkinType.cartanMatrix_B]
  funext j
  rw [rootWeight]

/-- The lowering-generator weight is the negative of the corresponding pinned simple root. -/
theorem rootWeight_inr_eq_neg_root_simpleIndex (ht : (TauCeti.DynkinType.B (n + 1)).Valid)
    (i : Fin (n + 1)) :
    rootWeight n (.inr i) =
      -((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
        ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i) := by
  funext j
  have h := congrArg Neg.neg
    (congrFun (rootWeight_inl_eq_root_simpleIndex n ht i) j)
  rw [rootWeight]
  exact h

/-- On matrix-valued points, the `i`-th raising subgroup transforms through the `i`-th simple
root of the pinned type-`Bₙ₊₁` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex
    (ht : (TauCeti.DynkinType.B (n + 1)).Valid) (i : Fin (n + 1))
    (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n A s * rootSubgroupPoints n (.inl i) A u *
        (weightTorusPoints n A s)⁻¹ =
      rootSubgroupPoints n (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
            (((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
              ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← rootWeight_inl_eq_root_simpleIndex n ht i]
  exact weightTorusPoints_conj_rootSubgroupPoints n (.inl i) A s u

/-- On matrix-valued points, the `i`-th lowering subgroup transforms through the negative of the
`i`-th pinned simple root. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex
    (ht : (TauCeti.DynkinType.B (n + 1)).Valid) (i : Fin (n + 1))
    (A : Type v) [CommRing A] (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n A s * rootSubgroupPoints n (.inr i) A u *
        (weightTorusPoints n A s)⁻¹ =
      rootSubgroupPoints n (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
            (-((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
              ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← rootWeight_inr_eq_neg_root_simpleIndex n ht i]
  exact weightTorusPoints_conj_rootSubgroupPoints n (.inr i) A s u

/-- The `i`-th raising subgroup transforms through the `i`-th simple root on scheme points. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex
    (ht : (TauCeti.DynkinType.B (n + 1)).Valid) (i : Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n (.inl i)).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
                ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup n (.inl i)).hom.hom := by
  rw [← rootWeight_inl_eq_root_simpleIndex n ht i]
  exact weightTorus_conj_rootSubgroup n (.inl i) A s u

/-- The `i`-th lowering subgroup transforms through the negative pinned simple root on scheme
points. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex
    (ht : (TauCeti.DynkinType.B (n + 1)).Valid) (i : Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n (.inr i)).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (-((TauCeti.DynkinType.B (n + 1)).simplyConnectedRootDatum ht).root
                ((TauCeti.DynkinType.B (n + 1)).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup n (.inr i)).hom.hom := by
  rw [← rootWeight_inr_eq_neg_root_simpleIndex n ht i]
  exact weightTorus_conj_rootSubgroup n (.inr i) A s u

end TauCeti.TypeBSpinCarrier
