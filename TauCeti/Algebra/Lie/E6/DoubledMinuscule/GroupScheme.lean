/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.AdmissibleLattice
public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight doubled type-E6 minuscule carrier

This file feeds the explicit `54`-dimensional type-`E₆` representation `V(ϖ₁) ⊕ V(ϖ₆)`, its
admissible coordinate lattice, and its full set of weights into the Kostant toral-closure
construction. The result is an explicit affine group scheme over `ℤ`, cut out inside `GL₅₄` by the
largest Hopf ideal killed by the twelve numbered simple-root subgroups and the represented rank-six
split torus, together with its matrix-valued points and the scheme-level pinning equation.

The `27`-dimensional carrier `TauCeti.E6Minuscule.groupScheme` already realizes the same root datum
in the same numbering, and the branch `E₆(q)` of the classification list is built on it. What the
doubled carrier adds is the index set. The nontrivial symmetry of the `E₆` diagram exchanges
`V(ϖ₁)` with `V(ϖ₆)`, so it does not permute the twenty-seven minuscule weights, which is what
`TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range` records; on the fifty-four
doubled weights it does, by
`TauCeti.DynkinType.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm`, which is the
equivariance `wt (π x) i = wt x (γ i)` under which a numbered permutation of the coordinates
extends to an automorphism of a Kostant toral-closure carrier. This carrier is therefore the one
on which the `E₆` graph automorphism can be realized. That realization is not performed here, and
no declaration below mentions the diagram symmetry.

The generic construction indexes its lattice basis and its weight family by `Fin n`, while the
representation is indexed by the block set `Fin 27 ⊕ Fin 27`, so `matrixIndexEquiv` fixes the order
in which the two blocks are laid out along the fifty-four matrix coordinates, and `matrixBasis` and
`matrixWeight` are the basis and weight family read in that order. Every declaration below is
stated in the resulting `Fin 54` coordinates.

The root characters are not redefined: `TauCeti.E6Minuscule.rootGeneratorWeight` and
`TauCeti.E6Minuscule.lie_serreH_rootGenerator` are statements about the type-`E₆` Serre algebra
alone, with no reference to a representation of it, so the pinning equation below is stated and
proved against them.

No reductivity, smoothness, maximality of the torus, or identification of the carrier's root datum
is asserted here. Those are subsequent steps in the pinned Chevalley--Demazure construction.

## Main declarations

* `TauCeti.E6DoubledMinuscule.matrixBasis` and `TauCeti.E6DoubledMinuscule.matrixWeight`: the
  admissible lattice basis and the weight family in the fifty-four matrix coordinates.
* `TauCeti.E6DoubledMinuscule.groupScheme`: the doubled minuscule Kostant toral-closure carrier
  over `ℤ`.
* `TauCeti.E6DoubledMinuscule.rootSubgroup`: its twelve numbered simple-root subgroup morphisms.
* `TauCeti.E6DoubledMinuscule.weightTorus`: its closed rank-six split torus.
* `TauCeti.E6DoubledMinuscule.points`: its matrix-valued points over a commutative ring.
* `TauCeti.E6DoubledMinuscule.rootSubgroupPoints`: its numbered root subgroups on matrix-valued
  points.
* `TauCeti.E6DoubledMinuscule.weightTorus_conj_rootSubgroup`: the scheme-level pinning equation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the doubled minuscule realization and the
  diagram symmetry it is built to carry.
* The carrier API follows the formal template of
  `TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme`, specialized here to the doubled minuscule
  representation, lattice, and weights.

## Roadmap

This is a type-`E₆` instance of "The Chevalley--Demazure construction" and "Root subgroup maps" in
Layer 9, "pinned Chevalley--Demazure group schemes over `ℤ`", of
`TauCetiRoadmap/ReductiveGroups/README.md`: an explicitly constructed group scheme over `ℤ` with
its numbered root subgroup maps and the equations pinning them against a split torus. It does not
close that layer on this diagram, which still owes the reductivity, the maximality of the torus,
the identification of the carrier's root datum with
`TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`, and the pinning datum itself.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.E6DoubledMinuscule

open AlgebraicGeometry CategoryTheory
open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-! ## The fifty-four matrix coordinates -/

/-- The order in which the two minuscule blocks are laid out along the matrix coordinates of the
doubled carrier: `finSumFinEquiv` after the numeral identification `27 + 27 = 54`, so that the
twenty-seven coordinates of `V(ϖ₁)` come first and the twenty-seven coordinates of `V(ϖ₆)` after
them. -/
def matrixIndexEquiv : Fin 27 ⊕ Fin 27 ≃ Fin 54 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

/-- The `V(ϖ₁)` block occupies the first twenty-seven matrix coordinates. -/
@[simp]
theorem val_matrixIndexEquiv_inl (a : Fin 27) : (matrixIndexEquiv (.inl a) : ℕ) = a := by
  simp only [matrixIndexEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply,
    Fin.val_cast, Fin.val_castAdd]

/-- The `V(ϖ₆)` block occupies the last twenty-seven matrix coordinates. -/
@[simp]
theorem val_matrixIndexEquiv_inr (a : Fin 27) : (matrixIndexEquiv (.inr a) : ℕ) = 27 + a := by
  simp only [matrixIndexEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
    Fin.val_cast, Fin.val_natAdd]

/-- The admissible doubled minuscule lattice basis, read in the fifty-four matrix coordinates. -/
noncomputable def matrixBasis : Module.Basis (Fin 54) ℤ lattice :=
  latticeBasis.reindex matrixIndexEquiv

/-- The matrix-coordinate basis vector at `a` is the block-coordinate one at the block index that
`matrixIndexEquiv` places at `a`. -/
@[simp]
theorem matrixBasis_apply (a : Fin 54) :
    matrixBasis a = latticeBasis (matrixIndexEquiv.symm a) := by
  rw [matrixBasis, Module.Basis.reindex_apply]

/-- The fifty-four weights of `V(ϖ₁) ⊕ V(ϖ₆)`, read in the fifty-four matrix coordinates. -/
def matrixWeight : Fin 54 → Fin 6 → ℤ :=
  e6DoubledMinusculeWeight ∘ matrixIndexEquiv.symm

/-- The weight at the matrix coordinate `a` is the doubled minuscule weight at the block index
that `matrixIndexEquiv` places at `a`. -/
@[simp]
theorem matrixWeight_apply (a : Fin 54) :
    matrixWeight a = e6DoubledMinusculeWeight (matrixIndexEquiv.symm a) :=
  (rfl)

/-- Every matrix-coordinate basis vector has its named Cartan weight. -/
theorem isCartanWeightVector_matrixBasis (a : Fin 54) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (matrixWeight a)
      ((matrixBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [matrixBasis_apply, matrixWeight_apply]
  exact isCartanWeightVector_latticeBasis _

/-- **The doubled minuscule weights span the full type-`E₆` character lattice.** Reordering the
weight family along `matrixIndexEquiv` does not change its range, so this is
`TauCeti.DynkinType.span_range_e6DoubledMinusculeWeight_eq_top`. -/
theorem span_range_matrixWeight_eq_top :
    Submodule.span ℤ (Set.range matrixWeight) = ⊤ := by
  rw [matrixWeight, matrixIndexEquiv.symm.surjective.range_comp]
  exact span_range_e6DoubledMinusculeWeight_eq_top

/-- **The doubled minuscule coordinate lattice is stable under the Kostant `ℤ`-form of the
type-`E₆` Serre algebra.** This is `TauCeti.E6DoubledMinuscule.rep_serreKostantForm_mem_lattice`
in the shape the generic toral-closure construction consumes it, with the Serre Kostant form
unfolded to the Kostant form of the numbered root and Cartan generators. -/
theorem rep_kostantForm_mem_lattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ),
      ∀ v ∈ lattice.toAddSubgroup, rep u v ∈ lattice.toAddSubgroup :=
  fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice
    (by rw [TauCeti.serreKostantForm_def]; exact hu) hv

/-! ## The pinned carrier -/

/-- The Hopf ideal cutting out the doubled type-`E₆` minuscule carrier inside `GL₅₄`. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 54) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight

/-- The defining ideal is the ideal supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis
        matrixWeight := by
  rw [definingIdeal]

/-- The full-weight doubled type-`E₆` minuscule carrier over `ℤ`, obtained as the smallest closed
subgroup scheme of `GL₅₄` containing the represented numbered root subgroups and weight torus. -/
noncomputable abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight

/-- The quotient-spectrum presentation of the doubled type-`E₆` minuscule carrier. -/
theorem groupScheme_def :
    groupScheme = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the doubled type-`E₆` minuscule carrier into `GL₅₄`. -/
noncomputable def carrierι : groupScheme ⟶ TauCeti.GeneralLinear.groupScheme ℤ 54 :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight

/-- The carrier inclusion is the generic Kostant toral-closure inclusion. -/
theorem carrierι_def :
    carrierι = TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight := by
  rw [carrierι]

/-- The doubled type-`E₆` minuscule carrier is a closed subgroup scheme of `GL₅₄`. -/
instance isClosedImmersion_carrierι : IsClosedImmersion carrierι.hom.hom.left := by
  rw [carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι
    _ _ _ _ _ _ _ _

/-- A positive or negative numbered simple-root subgroup of the doubled type-`E₆` carrier. -/
noncomputable def rootSubgroup (k : Fin 6 ⊕ Fin 6) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight k

/-- The root subgroup is the one supplied by the generic Kostant toral-closure construction. -/
theorem rootSubgroup_def (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
        k := by
  rw [rootSubgroup]

/-- Including a numbered root subgroup into `GL₅₄` recovers its represented divided-power
exponential subgroup. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k ≫ carrierι =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) matrixBasis := by
  rw [rootSubgroup, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι
    _ _ _ _ _ _ _ _ k

/-- The represented rank-six split weight torus in the doubled type-`E₆` carrier. -/
noncomputable def weightTorus : SplitTorus.groupScheme ℤ (Fin 6) ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight

/-- The weight torus is the one supplied by the generic Kostant toral-closure construction. -/
theorem weightTorus_def :
    weightTorus =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis
        matrixWeight := by
  rw [weightTorus]

/-- Including the weight torus into `GL₅₄` recovers the diagonal torus of the doubled minuscule
weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus ≫ carrierι = TauCeti.GeneralLinear.weightTorus (R := ℤ) matrixWeight := by
  rw [weightTorus, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι
    _ _ _ _ _ _ _ _

/-- The doubled minuscule weights make the represented split torus a closed subgroup scheme of the
carrier. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral
    _ _ _ _ _ _ _ _ span_range_matrixWeight_eq_top

/-- Two morphisms out of the doubled type-`E₆` carrier agree when they agree on its numbered root
subgroups and represented split torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup k ≫ f = rootSubgroup k ≫ g)
    (htorus : weightTorus ≫ f = weightTorus ≫ g) : f = g :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    _ _ _ _ _ _ _ _ f g hroot htorus

/-! ## Matrix-valued points -/

/-- The matrix-valued points of the doubled type-`E₆` minuscule carrier. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin 54) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight A

/-- The carrier points are exactly the invertible matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points A = TauCeti.GeneralLinear.hopfIdealPointsSubgroup 54 definingIdeal A := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def
    _ _ _ _ _ _ _ _ A

/-- A matrix is a carrier point exactly when its associated convolution point kills the defining
Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
    g ∈ points A ↔
      ∀ x ∈ definingIdeal,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) 54).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-- The parametrized numbered root subgroup inside the doubled type-`E₆` carrier points. -/
noncomputable def rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  MonoidHom.codRestrict
    ((TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) matrixBasis).comp
        (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom)
    (points A) fun u ↦ by
      rw [points]
      exact TauCeti.UniversalEnvelopingAlgebra.kostantGeneratedPointsSubgroup_le_toralPoints
        _ _ _ _ _ _ _ _ A
        (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_mem_generatedPoints
          _ _ _ _ _ _ _ A k _)

/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 54) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) matrixBasis
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  rw [rootSubgroupPoints]
  rfl

/-- The split weight torus on matrix-valued points of the doubled type-`E₆` carrier. -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin 6 → Aˣ) →* points A :=
  MonoidHom.codRestrict
    (TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
      lattice.toAddSubgroup matrixBasis matrixWeight)
    (points A) fun s ↦ by
      rw [points]
      exact TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_mem_toralPoints
        _ _ _ _ _ _ _ _ A s

/-- A doubled minuscule weight-torus point is the diagonal matrix obtained by evaluating each
weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin 6 → Aˣ) :
    (weightTorusPoints A s : _root_.Matrix.GeneralLinearGroup (Fin 54) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        lattice.toAddSubgroup matrixBasis matrixWeight s := by
  rw [weightTorusPoints]
  rfl

/-! ## The pinning equation -/

/-- **Conjugation by the doubled minuscule weight torus acts on each numbered root subgroup through
its positive or negative pinned simple-root character.** The character is
`TauCeti.E6Minuscule.rootGeneratorWeight`, which reads a row of the type-`E₆` Cartan matrix and
mentions no representation, so it is the same one the `27`-dimensional carrier is pinned by. -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin 6 ⊕ Fin 6) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup k).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (TauCeti.E6Minuscule.rootGeneratorWeight k) : A) * u)) ≫
        (rootSubgroup k).hom.hom :=
  kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
      _ _ _ _ _ _ _ isCartanWeightVector_matrixBasis
      isNilpotent_rep_serreRootGenerator A (TauCeti.E6Minuscule.lie_serreH_rootGenerator k) s u

end TauCeti.E6DoubledMinuscule
