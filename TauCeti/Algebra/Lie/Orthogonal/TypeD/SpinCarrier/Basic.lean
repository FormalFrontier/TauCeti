/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.RepresentationTheory.Spin.Polarization.SplitEven
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
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

Those data are then carried onto matrix-valued points: the numbered root subgroups and the weight
torus become homomorphisms into `TauCeti.TypeDSpinCarrier.points`, and conjugating one by the
other rescales its parameter through a character. That character is named: it is the positive or
negative `i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at
`TauCeti.DynkinType.D n`, the uniform pinned datum a consumer reaches holding only a Dynkin type.
That naming is what makes the carrier's pinning conventions statable without reference to its
`2 ^ n`-dimensional spin realization.

No smoothness, reductivity, maximality of the torus, or identification of the carrier's whole root
datum is asserted here: the equations below concern the simple root characters alone, and exhibit
neither a Borel subgroup nor a root subgroup for a non-simple root. Those are subsequent steps in
the pinned Chevalley--Demazure construction.

## Main declarations

* `TauCeti.TypeDSpinCarrier.groupScheme`: the full-weight spin carrier over `ℤ`.
* `TauCeti.TypeDSpinCarrier.rootSubgroup`: its numbered simple-root subgroup morphisms.
* `TauCeti.TypeDSpinCarrier.weightTorus`: its closed rank-`n` split torus.
* `TauCeti.TypeDSpinCarrier.points`: its matrix-valued points over a commutative ring.
* `TauCeti.TypeDSpinCarrier.rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.weightTorusPoints`: the numbered root subgroups and the weight torus
  on those matrix-valued points.

## Main results

* `TauCeti.TypeDSpinCarrier.lie_serreH_rootGenerator`: each numbered Serre root generator is a
  Cartan weight vector, with weight the corresponding row of the type-`D` Cartan matrix for a
  raising generator and its negative for a lowering generator.
* `TauCeti.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.weightTorus_conj_rootSubgroup`: conjugation by the weight torus
  rescales the parameter of each numbered root subgroup through that character, on matrix-valued
  points and on scheme points respectively.
* `TauCeti.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex`,
  `TauCeti.TypeDSpinCarrier.weightTorus_conj_rootSubgroup_root_simpleIndex`, and their
  negative-root counterparts: the same equations with the named simple root of
  `TauCeti.DynkinType.simplyConnectedRootDatum` as their exponent.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

The carrier API follows the formal template of
`TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme` and
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme`, and the pinning equations below follow
that of `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum`; the split spin representation,
exterior lattice, and type-`D` weights are specific to this construction. This advances Layer 9,
"The Chevalley--Demazure construction", of the ReductiveGroups roadmap and supplies the type-`D`
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

/-- The type-`Dₙ` carrier is the generic Kostant toral closure for its spin representation. -/
theorem groupScheme_eq_kostantToralGroupScheme :
    groupScheme n hn = kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [groupScheme]

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

/-- The root subgroup is the generic Kostant root subgroup, transported across the carrier's
quotient-spectrum presentation. -/
theorem rootSubgroup_def (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn k =
      kostantRootSubgroupToToral
          (TauCeti.serreRootGenerator (CartanMatrix.D n))
          (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) k ≫
        eqToHom (groupScheme_eq_kostantToralGroupScheme n hn).symm := by
  rw [rootSubgroup]

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

/-- **The parametrized numbered root subgroup inside the type-`Dₙ` spin carrier points.** The
parameter is read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def rootSubgroupPoints (hn : 4 ≤ n) (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A] :
    Multiplicative A →* points n hn A :=
  kostantToralRootSubgroupPoints
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) k A

/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints n hn k A u :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantRootSubgroupMatrix
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn k)
        (latticeBasis n)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  exact coe_kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ k A u

/-- **The split spin weight torus inside the type-`Dₙ` spin carrier points.** -/
noncomputable def weightTorusPoints (hn : 4 ≤ n) (A : Type v) [CommRing A] :
    (Fin n → Aˣ) →* points n hn A :=
  kostantToralWeightTorusPoints
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) A

/-- A weight-torus point is the diagonal matrix obtained by evaluating each spin weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin n → Aˣ) :
    (weightTorusPoints n hn A s :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantTorusMatrix (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n) s := by
  exact coe_kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A s

/-! ## The Cartan action on the numbered root generators -/

/-- The numbered Serre root generators of the type-`Dₙ` presentation are weight vectors for its
Cartan generators, with the integral weight `TauCeti.TypeDStd.rootGeneratorWeight` already attached
to the numbering by the split orthogonal Lie algebra. The type-`D` Cartan matrix is symmetric, so
its row and column readings of that weight agree. -/
theorem lie_serreH_rootGenerator (k : Fin n ⊕ Fin n) (j : Fin n) :
    ⁅TauCeti.serreH ℚ (CartanMatrix.D n) j,
        TauCeti.serreRootGenerator (CartanMatrix.D n) k⁆ =
      ((TypeDStd.rootGeneratorWeight n k j : ℤ) : ℚ) •
        TauCeti.serreRootGenerator (CartanMatrix.D n) k := by
  cases k with
  | inl i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inl,
        (CartanMatrix.D_isSymm n).apply i j, TypeDStd.rootGeneratorWeight_inl]
  | inr i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inr,
        (CartanMatrix.D_isSymm n).apply i j, TypeDStd.rootGeneratorWeight_inr]

/-! ## The pinning equation -/

/-- **Conjugation by the spin weight torus acts on each numbered root subgroup through its
positive or negative simple-root character, on matrix-valued points.** A torus point `s` carries
the root-subgroup point of parameter `u` to the one of parameter `α_k(s) u`. -/
@[simp]
theorem weightTorusPoints_conj_rootSubgroupPoints (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A]
    (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn k A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (TypeDStd.rootGeneratorWeight n k) : A) *
            Multiplicative.toAdd u)) := by
  exact kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isCartanWeightVector_latticeBasis n hn)
    (lie_serreH_rootGenerator n k) A s u

/-- **Conjugation by the spin weight torus acts on each numbered root subgroup through its
positive or negative simple-root character.** -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin n ⊕ Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn k).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (TypeDStd.rootGeneratorWeight n k) : A) * u)) ≫
        (rootSubgroup n hn k).hom.hom := by
  rw [weightTorus, rootSubgroup]
  exact kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n hn)
    (isNilpotent_rep_rootGenerator n hn) A (lie_serreH_rootGenerator n k) s u

/-! ## The numbered root subgroups sit at the named simple roots

The two identifications the equations below rewrite with,
`TauCeti.TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and its lowering counterpart, are
proved beside the weight they name, in
`TauCeti/Algebra/Lie/Orthogonal/TypeD/RootGenerators.lean`.

None of the equations below is a `simp` lemma. Their right-hand sides name the character through
`TauCeti.DynkinType.simplyConnectedRootDatum`, which `simp` unfolds at the `D n` branch, so they
are not `simp`-normal; the numbered equations above are, and these are explicit rewrite lemmas for
a consumer holding a Dynkin type, as in
`TauCeti.SpStd.weightTorus_conj_rootSubgroup_root_simpleIndex`. -/

/-- On matrix-valued points, conjugation by the spin weight torus rescales the `i`-th raising root
subgroup through the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex (i : Fin n) (A : Type v)
    [CommRing A] (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn (.inl i) A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
            (((TauCeti.DynkinType.D n).simplyConnectedRootDatum
                (DynkinType.valid_D.mpr hn)).root
              ((TauCeti.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex n hn i]
  exact weightTorusPoints_conj_rootSubgroupPoints n hn (.inl i) A s u

/-- On matrix-valued points, conjugation by the spin weight torus rescales the `i`-th lowering root
subgroup through the negative of the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex (i : Fin n) (A : Type v)
    [CommRing A] (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn (.inr i) A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
            (-((TauCeti.DynkinType.D n).simplyConnectedRootDatum
                (DynkinType.valid_D.mpr hn)).root
              ((TauCeti.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex n hn i]
  exact weightTorusPoints_conj_rootSubgroupPoints n hn (.inr i) A s u

/-- Conjugation by the spin weight torus rescales the `i`-th raising root subgroup through the
`i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (i : Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn (.inl i)).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (((TauCeti.DynkinType.D n).simplyConnectedRootDatum
                  (DynkinType.valid_D.mpr hn)).root
                ((TauCeti.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
              u)) ≫
        (rootSubgroup n hn (.inl i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex n hn i]
  exact weightTorus_conj_rootSubgroup n hn (.inl i) A s u

/-- Conjugation by the spin weight torus rescales the `i`-th lowering root subgroup through the
negative of the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (i : Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn (.inr i)).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (-((TauCeti.DynkinType.D n).simplyConnectedRootDatum
                  (DynkinType.valid_D.mpr hn)).root
                ((TauCeti.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
              u)) ≫
        (rootSubgroup n hn (.inr i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex n hn i]
  exact weightTorus_conj_rootSubgroup n hn (.inr i) A s u

end TauCeti.TypeDSpinCarrier
