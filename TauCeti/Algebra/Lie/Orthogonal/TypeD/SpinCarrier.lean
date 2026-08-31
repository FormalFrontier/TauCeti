/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.SplitEven
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight type-D spin carrier

For `4 ≤ n`, this file specializes the type-`Dₙ` spin representation to the canonical split
quadratic space `M* × M`, where `M = Fin n → ℚ`. Its exterior coordinate lattice has basis
indexed by the sign sets `Finset (Fin n)` and is stable under the type-`D` Serre Kostant form.
The corresponding spin weights span the full simply connected character lattice.

These data are fed into the Kostant toral-closure construction. The result is an explicit affine
group scheme over `ℤ`, cut out inside `GL_(2^n)` by the largest Hopf ideal killed by the numbered
simple-root subgroups and the represented rank-`n` split torus. In particular, the construction
uses the full spin module rather than one half-spin summand, so its weights see both spinor cosets
of the type-`D` root lattice.

No smoothness, reductivity, maximality of the torus, or identification of the carrier's root datum
is asserted here. Those are subsequent steps in the pinned Chevalley--Demazure construction.

## Main declarations

* `TauCeti.TypeDSpinCarrier.groupScheme`: the full-weight spin carrier over `ℤ`.
* `TauCeti.TypeDSpinCarrier.rootSubgroup`: its numbered simple-root subgroup morphisms.
* `TauCeti.TypeDSpinCarrier.weightTorus`: its closed rank-`n` split torus.
* `TauCeti.TypeDSpinCarrier.points`: its matrix-valued points over a commutative ring.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

The carrier API follows the formal template of
`TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme`; the split spin representation, exterior lattice,
and type-`D` weights are specific to this construction. This advances Layer 9, "The
Chevalley--Demazure construction", of the ReductiveGroups roadmap and supplies the type-`D`
carrier required by milestone L0 of the CFSGStatement roadmap.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.TypeDSpinCarrier

open AlgebraicGeometry CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n)

/-! ## The split spin representation and its lattice -/

/-- The canonical split polarization used by the type-`Dₙ` spin carrier. -/
noncomputable abbrev polarization := TauCeti.splitEvenPolarization ℚ n

/-- The coordinate basis of the first isotropic summand in the split polarization. -/
noncomputable abbrev polarizationBasis := TauCeti.splitEvenBasis ℚ n

/-- The rational spin representation of the type-`Dₙ` Serre presentation, extended to its
universal enveloping algebra. -/
noncomputable abbrev rep :=
  (polarization n).typeDSpinRep (polarizationBasis n) hn

/-- The integral exterior coordinate lattice in the split spin module. -/
noncomputable abbrev lattice :=
  TauCeti.ExteriorAlgebra.integralLattice (polarizationBasis n)

/-- The dimension of the full spin module, expressed as the cardinality of its exterior basis. -/
abbrev dimension := Fintype.card (Finset (Fin n))

/-- The exterior coordinate basis, reindexed by a finite ordinal for the general-linear carrier. -/
noncomputable def latticeBasis :
    Module.Basis (Fin (dimension n)) ℤ (lattice n).toAddSubgroup :=
  (TauCeti.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n)).reindex
    (Fintype.equivFin (Finset (Fin n)))

/-- The sign set represented by a finite-ordinal spin-basis index. -/
noncomputable abbrev signSet (i : Fin (dimension n)) : Finset (Fin n) :=
  (Fintype.equivFin (Finset (Fin n))).symm i

/-- The simply connected type-`Dₙ` weight of a finite-ordinal spin-basis vector. -/
noncomputable abbrev basisWeight (i : Fin (dimension n)) : Fin n → ℤ :=
  TauCeti.DynkinType.typeDSpinWeight (signSet n i)

/-- A reindexed lattice-basis vector is the exterior basis vector of its sign set. -/
@[simp]
theorem coe_latticeBasis (i : Fin (dimension n)) :
    ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) =
      (polarizationBasis n).ExteriorAlgebra (signSet n i) := by
  rw [latticeBasis, Module.Basis.reindex_apply, signSet]
  exact TauCeti.ExteriorAlgebra.coe_integralLatticeBasis _ _

/-- Every represented numbered root generator is nilpotent. -/
theorem isNilpotent_rep_rootGenerator (k : Fin n ⊕ Fin n) :
    IsNilpotent (rep n hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))) :=
  (polarization n).isNilpotent_typeDSpinRep_rootGenerator (polarizationBasis n) hn k

/-- The type-`D` Serre Kostant form preserves the split exterior coordinate lattice. -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n))}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.D n))
    {v : ExteriorAlgebra ℚ (polarization n).W} (hv : v ∈ lattice n) :
    rep n hn u v ∈ lattice n :=
  (polarization n).typeDSpinRep_serreKostantForm_apply_mem_integralLattice
    (polarizationBasis n) hn hu hv

/-- The generic Kostant form for the numbered type-`D` generators preserves the split exterior
coordinate lattice. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)))
    (hu : u ∈ kostantForm (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)))
    (v : ExteriorAlgebra ℚ (polarization n).W) (hv : v ∈ lattice n) :
    rep n hn u v ∈ lattice n :=
  rep_serreKostantForm_mem_lattice n hn (by
    rw [TauCeti.serreKostantForm_def]
    exact hu) hv

/-- Every finite-ordinal exterior basis vector has its named integral type-`D` spin weight. -/
theorem isCartanWeightVector_latticeBasis (i : Fin (dimension n)) :
    IsCartanWeightVector (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
      (basisWeight n i)
      ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
  rw [coe_latticeBasis]
  exact (polarization n).isCartanWeightVector_typeDSpinRep_exteriorBasis
    (polarizationBasis n) hn (signSet n i)

/-- The weights of the full spin basis span the simply connected type-`D` character lattice. -/
theorem span_range_basisWeight_eq_top :
    Submodule.span ℤ (Set.range (basisWeight n)) = ⊤ := by
  have hrange :
      Set.range (fun i : Fin (dimension n) ↦
        TauCeti.DynkinType.typeDSpinWeight (signSet n i)) =
        Set.range (TauCeti.DynkinType.typeDSpinWeight (n := n)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨signSet n i, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Fintype.equivFin (Finset (Fin n)) s, by simp [signSet]⟩
  rw [hrange, TauCeti.DynkinType.span_range_typeDSpinWeight_eq_top]

/-! ## The closed carrier and its pinned generators -/

/-- The Hopf ideal cutting out the full-weight type-`Dₙ` spin carrier inside `GL_(2^n)`. -/
noncomputable def definingIdeal (hn : 4 ≤ n) :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  kostantToralDefiningIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The full-weight type-`Dₙ` spin carrier over `ℤ`, obtained as the smallest closed subgroup
scheme containing the represented numbered root subgroups and weight torus. -/
noncomputable def groupScheme (hn : 4 ≤ n) : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantToralGroupScheme
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The quotient-spectrum presentation of the type-`Dₙ` spin carrier. -/
theorem groupScheme_def :
    groupScheme n hn = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the type-`Dₙ` spin carrier into `GL_(2^n)`. -/
noncomputable def carrierι (hn : 4 ≤ n) :
    groupScheme n hn ⟶ TauCeti.GeneralLinear.groupScheme ℤ (dimension n) :=
  eqToHom (by rfl : groupScheme n hn = kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)) ≫
    kostantToralGroupSchemeι
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The type-`Dₙ` spin carrier is a closed subgroup scheme of its ambient general linear group. -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι n hn).hom.hom.left := by
  rw [carrierι]
  exact isClosedImmersion_kostantToralGroupSchemeι _ _ _ _ _ _ _ _

/-- A positive or negative numbered simple-root subgroup of the type-`Dₙ` spin carrier. -/
noncomputable def rootSubgroup (hn : 4 ≤ n) (k : Fin n ⊕ Fin n) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme n hn :=
  kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) k ≫
  eqToHom (by rfl : kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) =
        groupScheme n hn)

/-- Including a numbered root subgroup into the ambient general linear group recovers its
represented Kostant root subgroup. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn k ≫ carrierι n hn =
      kostantRootSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) k
        (isNilpotent_rep_rootGenerator n hn k) (latticeBasis n) := by
  rw [rootSubgroup, carrierι]
  exact kostantRootSubgroupToToral_comp_ι _ _ _ _ _ _ _ _ k

/-- The represented rank-`n` split weight torus in the type-`Dₙ` spin carrier. -/
noncomputable def weightTorus (hn : 4 ≤ n) :
    SplitTorus.groupScheme ℤ (Fin n) ⟶ groupScheme n hn :=
  kostantWeightTorusToToral
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) ≫
  eqToHom (by rfl : kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) =
        groupScheme n hn)

/-- Including the weight torus into the ambient general linear group recovers the diagonal torus
of the spin weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus n hn ≫ carrierι n hn =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) := by
  rw [weightTorus, carrierι]
  exact kostantWeightTorusToToral_comp_ι _ _ _ _ _ _ _ _

/-- The full spin weights make the represented split torus a closed subgroup scheme of the
carrier. -/
instance isClosedImmersion_weightTorus :
    IsClosedImmersion (weightTorus n hn).hom.hom.left :=
  isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_basisWeight_eq_top n)

/-- Two morphisms out of the type-`Dₙ` spin carrier agree when they agree on its numbered root
subgroups and represented split torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme n hn ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup n hn k ≫ f = rootSubgroup n hn k ≫ g)
    (htorus : weightTorus n hn ≫ f = weightTorus n hn ≫ g) : f = g := by
  exact kostantToralGroupScheme_hom_ext _ _ _ _ _ _ _ _ f g hroot htorus

/-! ## Matrix-valued points -/

/-- The matrix-valued points of the type-`Dₙ` spin carrier. -/
noncomputable def points (hn : 4 ≤ n) (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :=
  kostantToralPointsSubgroup
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A

/-- The carrier points are exactly the invertible matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points n hn A =
      TauCeti.GeneralLinear.hopfIdealPointsSubgroup (dimension n) (definingIdeal n hn) A := by
  rw [points, definingIdeal]
  exact kostantToralPointsSubgroup_def _ _ _ _ _ _ _ _ A

/-- A matrix is a carrier point exactly when its associated convolution point kills the
defining Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
    g ∈ points n hn A ↔
      ∀ x ∈ definingIdeal n hn,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact mem_kostantToralPointsSubgroup_iff _ _ _ _ _ _ _ _ A g

end TauCeti.TypeDSpinCarrier
