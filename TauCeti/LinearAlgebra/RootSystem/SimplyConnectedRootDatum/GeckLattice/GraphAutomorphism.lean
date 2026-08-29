/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry
public import TauCeti.CategoryTheory.Aut.Basic
public import TauCeti.LinearAlgebra.RootSystem.GeckConstruction.PinnedSymmetry
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor

/-!
# The graph automorphism of the pinned Geck carrier

`TauCeti.DynkinType.geckGroupScheme` is the explicit affine group scheme over `ℤ` attached to a
valid Dynkin type: the smallest closed subgroup scheme of `GLₙ` containing the divided-power
exponential root subgroups of the Bourbaki-numbered Chevalley generators together with the weight
torus of the Geck coordinate lattice. This file equips it with the automorphism attached to a
symmetry `σ` of its Dynkin diagram.

Both halves of the construction already exist. A symmetry of the numbered Kostant data induces an
automorphism of a Kostant toral closure, and Geck's coordinate permutation is such a symmetry: it
preserves the integral lattice, intertwines the represented simple root generators, and permutes
the weights contragrediently. What this file adds is the reading of the second as the first, and
the resulting pinning equations on the carrier itself, namely

```text
γ ∘ x_i = x_{σ i},        γ ∘ (weight torus) = (weight torus) ∘ relabel σ⁻¹.
```

The first equation is the one that pins `γ`: the numbering permutation acts identically on the
raising and the lowering generators and leaves the additive parameter of every root subgroup
alone. The order of `γ` divides that of `σ`, so an involution of the diagram gives `γ ^ 2 = 1` and
the triality of `D₄` gives `γ ^ 3 = 1`; on the identity symmetry `γ` is the identity.

The same coordinate permutation acts on the algebra-valued points of the carrier, by conjugation by
`TauCeti.DynkinType.geckGraphAutMatrix`, its image under `Matrix.permMatrixHom`, which is the
permutation matrix of the inverse permutation because permutation matrices multiply
contravariantly. That is the matrix conjugation by which is the action on points of the coordinate
automorphism of the ambient `GLₙ`; the two pinning equations displayed above, and the order
relation, all hold in the same form on points. The points
of the carrier are read directly off its defining Hopf ideal rather than through the scheme-level
automorphism, so the two constructions are compared rather than defined in terms of each other:
`TauCeti.DynkinType.schemePointsMulEquiv_geckGraphAut_comp_geckGroupSchemeι` says that composing an
algebra-valued point with `TauCeti.DynkinType.geckGraphAut` and including it into `GLₙ` performs
exactly the conjugation which is `TauCeti.DynkinType.geckGraphAutPoints`.

The scheme automorphism is that of the carrier over `ℤ`, before any base change, and it acts on the
whole carrier rather than on the elementary subgroup its root subgroups generate. The Geck weights
span the root lattice rather than, in general, the full character lattice, so this carrier is not
yet the simply connected one a finite group of Lie type is built from. Nothing here asserts
reductivity, maximality of the weight torus, or any finiteness or simplicity statement.

## Main definitions

* `TauCeti.DynkinType.geckGraphAut`: the graph automorphism of the pinned Geck carrier.
* `TauCeti.DynkinType.geckGraphAutMatrix`: the matrix of the pinned coordinate permutation, its
  image under `Matrix.permMatrixHom`.
* `TauCeti.DynkinType.geckGraphAutPoints`: the graph automorphism on the algebra-valued points of
  the carrier.

## Main results

* `TauCeti.DynkinType.geckRootSubgroup_comp_geckGraphAut_hom` and its inverse counterpart: the
  graph automorphism renumbers the pinned root subgroups by `σ`.
* `TauCeti.DynkinType.geckWeightTorus_comp_geckGraphAut_hom` and its inverse counterpart: it
  intertwines the weight torus morphism with the relabelling of its coordinates.
* `TauCeti.DynkinType.geckGraphAut_pow_eq_one`: the order relation.
* `TauCeti.DynkinType.geckGraphAut_one`: the identity symmetry gives the identity automorphism.
* `TauCeti.DynkinType.map_geckPoints_conj_geckGraphAutMatrix`: the pinned symmetry matrix
  normalizes the points of the carrier.
* `TauCeti.DynkinType.schemePointsMulEquiv_geckGraphAut_comp_geckGroupSchemeι`: the automorphism on
  points is the map the carrier automorphism induces.
* `TauCeti.DynkinType.geckGraphAutPoints_geckRootSubgroupMatrix` and
  `TauCeti.DynkinType.geckGraphAutPoints_geckTorusMatrix`: the two pinning equations on points.
* `TauCeti.DynkinType.geckPointsMap_comp_geckGraphAutPoints`: the automorphism on points is natural
  in the value ring.
* `TauCeti.DynkinType.geckGraphAutPoints_pow_eq_one` and
  `TauCeti.DynkinType.geckGraphAutPoints_one`: the order relation on points, and the identity
  symmetry.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.

This is the pinned instance of the graph-automorphism half of "Pinnings ... This is what makes
'the' graph automorphism well defined" in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L1, ordinary and
graph-twisted Steinberg maps, of `TauCetiRoadmap/CFSGStatement/README.md`, whose twisted branches
compose such a `γ` with the field Frobenius.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

universe v v'

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {sigma : Equiv.Perm (Fin t.rank)}

/-- The pinned Geck-module symmetry intertwines the represented simple root generators, stated
through `UniversalEnvelopingAlgebra.ι` as the numbered Kostant symmetry constructions take that
hypothesis. -/
private theorem geckDiagramModuleEquiv_ι_geckRepresentation_rootGenerator
    (hsigma : sigma ∈ t.diagramSymmetry) :
    ∀ (i : Fin t.rank ⊕ Fin t.rank) (v : t.GeckIndex ht → ℚ),
      t.geckDiagramModuleEquiv ht hsigma
          (t.geckRepresentation ht
            (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)) v) =
        t.geckRepresentation ht
            (_root_.UniversalEnvelopingAlgebra.ι ℚ
              ((t.lieBasis ht).rootGenerator (diagramRootGeneratorPerm sigma i)))
          (t.geckDiagramModuleEquiv ht hsigma v) :=
  fun i v => by
    simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using
      t.geckDiagramModuleEquiv_geckRepresentation_rootGenerator ht hsigma i v

/-- The Kostant toral-closure symmetry of the pinned Geck data. -/
private def toralGraphAut (hsigma : sigma ∈ t.diagramSymmetry) :
    Aut (TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralNumberedSymmetryIso
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    ⇑(diagramRootGeneratorPerm sigma) (t.geckDiagramModuleEquiv ht hsigma)
    (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma)
    (geckDiagramModuleEquiv_ι_geckRepresentation_rootGenerator ht hsigma)
    (diagramRootGeneratorPerm sigma).surjective
    (t.geckDiagramFinPerm ht hsigma)
    (t.geckDiagramModuleEquiv_geckCoordinateBasisFin ht hsigma)
    sigma (t.geckWeightFin_geckDiagramFinPerm ht hsigma)

/-- **The graph automorphism of the pinned Geck carrier** attached to a symmetry of its
Bourbaki-numbered Dynkin diagram. It renumbers the pinned root subgroups by the symmetry without
changing their parameters, and relabels the coordinates of the represented weight torus. -/
def geckGraphAut (hsigma : sigma ∈ t.diagramSymmetry) : Aut (t.geckGroupScheme ht) :=
  Aut.autMulEquivOfIso (eqToIso (t.geckGroupScheme_def ht).symm) (toralGraphAut ht hsigma)

private theorem geckGraphAut_hom (hsigma : sigma ∈ t.diagramSymmetry) :
    (t.geckGraphAut ht hsigma).hom =
      eqToHom (t.geckGroupScheme_def ht) ≫ (toralGraphAut ht hsigma).hom ≫
        eqToHom (t.geckGroupScheme_def ht).symm := by
  rw [geckGraphAut, TauCeti.CategoryTheory.autMulEquivOfIso_hom, eqToIso.inv, eqToIso.hom]

/-- The graph automorphism renumbers every pinned raising and lowering root subgroup by the diagram
symmetry, without changing its additive parameter. -/
@[reassoc (attr := simp)]
theorem geckRootSubgroup_comp_geckGraphAut_hom (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckRootSubgroup ht i ≫ (t.geckGraphAut ht hsigma).hom =
      t.geckRootSubgroup ht (diagramRootGeneratorPerm sigma i) := by
  rw [geckGraphAut_hom, geckRootSubgroup_def, geckRootSubgroup_def, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, toralGraphAut, ← Category.assoc,
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom]

/-- The inverse graph automorphism restores the original numbering of a pinned root subgroup. -/
@[reassoc (attr := simp)]
theorem geckRootSubgroup_comp_geckGraphAut_inv (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckRootSubgroup ht (diagramRootGeneratorPerm sigma i) ≫ (t.geckGraphAut ht hsigma).inv =
      t.geckRootSubgroup ht i := by
  rw [← geckRootSubgroup_comp_geckGraphAut_hom ht hsigma i, Category.assoc,
    (t.geckGraphAut ht hsigma).hom_inv_id, Category.comp_id]

/-- **The graph automorphism intertwines the represented weight torus with the relabelling**
attached to the diagram symmetry: composing the torus morphism with `γ` is the same as relabelling
its coordinates by `σ⁻¹` first. Nothing here asserts that this morphism is an immersion, so this
is an equation of morphisms and not a statement that `γ` normalizes a subgroup scheme. -/
@[reassoc (attr := simp)]
theorem geckWeightTorus_comp_geckGraphAut_hom (hsigma : sigma ∈ t.diagramSymmetry) :
    t.geckWeightTorus ht ≫ (t.geckGraphAut ht hsigma).hom =
      SplitTorus.relabel ℤ sigma⁻¹ ≫ t.geckWeightTorus ht := by
  rw [geckGraphAut_hom, geckWeightTorus_def, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, toralGraphAut, ← Category.assoc,
    TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_numberedSymmetryIso_hom,
    Category.assoc]

/-- The inverse graph automorphism relabels the coordinates of the weight torus by `σ` itself,
undoing the relabelling by `σ⁻¹` that the forward automorphism performs. -/
@[reassoc (attr := simp)]
theorem geckWeightTorus_comp_geckGraphAut_inv (hsigma : sigma ∈ t.diagramSymmetry) :
    t.geckWeightTorus ht ≫ (t.geckGraphAut ht hsigma).inv =
      SplitTorus.relabel ℤ sigma ≫ t.geckWeightTorus ht := by
  calc t.geckWeightTorus ht ≫ (t.geckGraphAut ht hsigma).inv
      = (SplitTorus.relabel ℤ sigma ≫ SplitTorus.relabel ℤ sigma⁻¹ ≫ t.geckWeightTorus ht) ≫
          (t.geckGraphAut ht hsigma).inv := by
        simp only [← Category.assoc, SplitTorus.relabel_comp, mul_inv_cancel,
          SplitTorus.relabel_one, Category.id_comp]
    _ = SplitTorus.relabel ℤ sigma ≫
          (t.geckWeightTorus ht ≫ (t.geckGraphAut ht hsigma).hom) ≫
            (t.geckGraphAut ht hsigma).inv := by
        rw [geckWeightTorus_comp_geckGraphAut_hom]
        simp only [Category.assoc]
    _ = SplitTorus.relabel ℤ sigma ≫ t.geckWeightTorus ht := by
        rw [Category.assoc, (t.geckGraphAut ht hsigma).hom_inv_id, Category.comp_id]

/-- **The order of the graph automorphism divides that of the diagram symmetry.** An involution of
the numbered diagram therefore gives `γ ^ 2 = 1`, and the triality of `D₄` gives `γ ^ 3 = 1`. -/
@[simp]
theorem geckGraphAut_pow_eq_one (hsigma : sigma ∈ t.diagramSymmetry) {m : ℕ}
    (hm : sigma ^ m = 1) : t.geckGraphAut ht hsigma ^ m = 1 := by
  have hgen : diagramRootGeneratorPerm sigma ^ m = 1 := diagramRootGeneratorPerm_pow_eq_one hm
  have htoral : toralGraphAut ht hsigma ^ m = 1 :=
    TauCeti.UniversalEnvelopingAlgebra.kostantToralNumberedSymmetryIso_pow_eq_one _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ m (by rw [← Equiv.Perm.coe_pow, hgen]; rfl) hm
  rw [geckGraphAut, ← map_pow, htoral, map_one]

/-- The identity symmetry of the diagram gives the identity automorphism of the Geck carrier. -/
@[simp]
theorem geckGraphAut_one : t.geckGraphAut ht t.diagramSymmetry.one_mem = 1 := by
  simpa using geckGraphAut_pow_eq_one ht t.diagramSymmetry.one_mem (m := 1) (pow_one _)

/-! ## The graph automorphism on algebra-valued points -/

/-- **The matrix of the pinned Geck coordinate permutation** attached to a symmetry of the
Bourbaki-numbered Dynkin diagram. It is the image of `TauCeti.DynkinType.geckDiagramFinPerm` under
`Matrix.permMatrixHom`, that is, the permutation matrix of the inverse coordinate permutation,
since permutation matrices multiply contravariantly. Conjugation by it is the action on points of
the coordinate automorphism of the ambient `GLₙ` which descends to
`TauCeti.DynkinType.geckGraphAut` on the carrier. -/
def geckGraphAutMatrix (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantNumberedSymmetryMatrix
    (t.geckCoordinateLattice ht).toAddSubgroup (t.geckCoordinateBasisFin ht)
    (t.geckDiagramModuleEquiv ht hsigma)
    (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma) A

/-- The matrix of the pinned Geck coordinate permutation is the permutation matrix of the inverse
finite-ordinal coordinate permutation. -/
theorem coe_geckGraphAutMatrix (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    (t.geckGraphAutMatrix ht hsigma A :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) =
      (t.geckDiagramFinPerm ht hsigma)⁻¹.permMatrix A :=
  TauCeti.UniversalEnvelopingAlgebra.coe_kostantNumberedSymmetryMatrix_of_perm _ _ _ _
    (t.geckDiagramFinPerm ht hsigma) (t.geckDiagramModuleEquiv_geckCoordinateBasisFin ht hsigma) A

/-- The matrix of the pinned Geck coordinate permutation commutes with extension of the value
ring. -/
@[simp]
theorem map_geckGraphAutMatrix (hsigma : sigma ∈ t.diagramSymmetry) {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (t.geckGraphAutMatrix ht hsigma A) =
      t.geckGraphAutMatrix ht hsigma B :=
  TauCeti.UniversalEnvelopingAlgebra.map_kostantNumberedSymmetryMatrix _ _ _ _ f

/-- **The matrix of the pinned coordinate permutation satisfies every order relation the diagram
symmetry satisfies.** -/
theorem geckGraphAutMatrix_pow_eq_one (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    {m : ℕ} (hm : sigma ^ m = 1) : t.geckGraphAutMatrix ht hsigma A ^ m = 1 := by
  refine Units.ext ?_
  -- Permutation matrices multiply contravariantly, so `Matrix.permMatrixHom` is the permutation
  -- matrix of the inverse permutation; that is the matrix `coe_geckGraphAutMatrix` produces.
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_geckGraphAutMatrix,
    ← Matrix.permMatrixHom_apply, ← map_pow, geckDiagramFinPerm_pow_eq_one ht hsigma hm, map_one]

/-- The points of the pinned Geck carrier are the points of the Kostant toral closure of the
pinned Geck data. -/
private theorem geckPoints_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    t.geckPoints ht A =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A := by
  rw [t.geckPoints_def ht A,
    TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def, t.geckDefiningIdeal_def ht]

/-- **The matrix of the pinned coordinate permutation normalizes the points of the Geck
carrier.** -/
theorem map_geckPoints_conj_geckGraphAutMatrix (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v)
    [CommRing A] :
    (t.geckPoints ht A).map
        ((MulAut.conj (t.geckGraphAutMatrix ht hsigma A) :
          Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A ≃*
            Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) : _ →* _) =
      t.geckPoints ht A := by
  rw [geckPoints_eq_kostantToralPointsSubgroup]
  exact UniversalEnvelopingAlgebra.map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    ⇑(diagramRootGeneratorPerm sigma) (t.geckDiagramModuleEquiv ht hsigma)
    (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma)
    (geckDiagramModuleEquiv_ι_geckRepresentation_rootGenerator ht hsigma)
    (diagramRootGeneratorPerm sigma).surjective
    (t.geckDiagramFinPerm ht hsigma)
    (t.geckDiagramModuleEquiv_geckCoordinateBasisFin ht hsigma)
    sigma (t.geckWeightFin_geckDiagramFinPerm ht hsigma) A

/-- The matrix of the pinned coordinate permutation, as an element of the normalizer of the points
of the Geck carrier. -/
private def geckGraphAutNormalizer (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    Subgroup.normalizer
      (t.geckPoints ht A : Set (Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)) :=
  ⟨t.geckGraphAutMatrix ht hsigma A, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (t.map_geckPoints_conj_geckGraphAutMatrix ht hsigma A)⟩

/-- **The graph automorphism on the algebra-valued points of the pinned Geck carrier**, namely
conjugation by the matrix of the pinned coordinate permutation. It renumbers the pinned root
subgroups by the diagram symmetry without changing their parameters, and relabels the coordinates
of a pinned weight-torus point. -/
def geckGraphAutPoints (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    MulAut (t.geckPoints ht A) :=
  (t.geckPoints ht A).normalizerMonoidHom (geckGraphAutNormalizer ht hsigma A)

/-- The graph automorphism on points is conjugation by the matrix of the pinned coordinate
permutation. -/
@[simp]
theorem coe_geckGraphAutPoints (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.geckPoints ht A) :
    (t.geckGraphAutPoints ht hsigma A g :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      t.geckGraphAutMatrix ht hsigma A * g * (t.geckGraphAutMatrix ht hsigma A)⁻¹ :=
  (rfl)

/-- The inverse graph automorphism on points is conjugation by the inverse matrix. -/
@[simp]
theorem coe_geckGraphAutPoints_symm (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.geckPoints ht A) :
    ((t.geckGraphAutPoints ht hsigma A).symm g :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      (t.geckGraphAutMatrix ht hsigma A)⁻¹ * g * t.geckGraphAutMatrix ht hsigma A :=
  (rfl)

/-- **The graph automorphism on points is the map the carrier automorphism induces.** On every
algebra-valued point of the carrier, composing with `TauCeti.DynkinType.geckGraphAut` and including
into `GLₙ` conjugates the point's matrix by `TauCeti.DynkinType.geckGraphAutMatrix`, which is what
`TauCeti.DynkinType.geckGraphAutPoints` does by `TauCeti.DynkinType.coe_geckGraphAutPoints`. So the
automorphism read off the defining Hopf ideal and the one obtained from the descended toral-closure
symmetry are the same map. -/
theorem schemePointsMulEquiv_geckGraphAut_comp_geckGroupSchemeι
    (hsigma : sigma ∈ t.diagramSymmetry) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (t.geckGroupScheme ht).X) :
    GeneralLinear.schemePointsMulEquiv (t.geckDim ht) A
        (p ≫ ((t.geckGraphAut ht hsigma).hom ≫ t.geckGroupSchemeι ht).hom.hom) =
      t.geckGraphAutMatrix ht hsigma A *
          GeneralLinear.schemePointsMulEquiv (t.geckDim ht) A
            (p ≫ (t.geckGroupSchemeι ht).hom.hom) *
        (t.geckGraphAutMatrix ht hsigma A)⁻¹ := by
  have hcomp : (t.geckGraphAut ht hsigma).hom ≫ t.geckGroupSchemeι ht =
      eqToHom (t.geckGroupScheme_def ht) ≫ (toralGraphAut ht hsigma).hom ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (t.isNilpotent_geckRepresentation_rootGenerator ht)
          (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) := by
    rw [geckGraphAut_hom, geckGroupSchemeι_def]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hcomp, t.geckGroupSchemeι_def ht, geckGraphAutMatrix]
  simpa only [toralGraphAut, Grp.comp_hom_hom, Category.assoc] using
    TauCeti.UniversalEnvelopingAlgebra.schemePointsMulEquiv_kostantToralNumberedSymmetryIso
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      ⇑(diagramRootGeneratorPerm sigma) (t.geckDiagramModuleEquiv ht hsigma)
      (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma)
      (geckDiagramModuleEquiv_ι_geckRepresentation_rootGenerator ht hsigma)
      (diagramRootGeneratorPerm sigma).surjective
      (t.geckDiagramFinPerm ht hsigma)
      (t.geckDiagramModuleEquiv_geckCoordinateBasisFin ht hsigma)
      sigma (t.geckWeightFin_geckDiagramFinPerm ht hsigma) A
      (p ≫ (eqToHom (t.geckGroupScheme_def ht)).hom.hom)

/-- **The graph automorphism renumbers the pinned root subgroups on points**, without changing
their additive parameter. This is the equation which pins the graph automorphism, read on the
points of the carrier. -/
@[simp]
theorem geckGraphAutPoints_geckRootSubgroupMatrix (hsigma : sigma ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (i : Fin t.rank ⊕ Fin t.rank) (u : Multiplicative A) :
    t.geckGraphAutPoints ht hsigma A
        ⟨t.geckRootSubgroupMatrix ht i
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u),
          t.geckRootSubgroupMatrix_mem_geckPoints ht A i _⟩ =
      ⟨t.geckRootSubgroupMatrix ht (diagramRootGeneratorPerm sigma i)
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u),
        t.geckRootSubgroupMatrix_mem_geckPoints ht A _ _⟩ :=
  Subtype.ext (by
    rw [coe_geckGraphAutPoints]
    exact UniversalEnvelopingAlgebra.kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) ⇑(diagramRootGeneratorPerm sigma)
      (t.geckDiagramModuleEquiv ht hsigma)
      (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma)
      (geckDiagramModuleEquiv_ι_geckRepresentation_rootGenerator ht hsigma)
      A i _)

/-- **The graph automorphism relabels the coordinates of a pinned weight-torus point** by the
inverse of the diagram symmetry. -/
@[simp]
theorem geckGraphAutPoints_geckTorusMatrix (hsigma : sigma ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.geckGraphAutPoints ht hsigma A
        ⟨diagGL fun i => torusCharacter s (t.geckWeightFin ht i), by
          simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
            t.geckTorusMatrix_mem_geckPoints ht A s⟩ =
      ⟨t.geckTorusMatrix ht fun k => s (sigma⁻¹ k),
        t.geckTorusMatrix_mem_geckPoints ht A _⟩ := by
  have hpt : ∀ i, torusCharacter s (t.geckWeightFin ht ((t.geckDiagramFinPerm ht hsigma)⁻¹ i)) =
      torusCharacter (fun k => s (sigma⁻¹ k)) (t.geckWeightFin ht i) := by
    intro i
    have hwt : t.geckWeightFin ht ((t.geckDiagramFinPerm ht hsigma)⁻¹ i) =
        t.geckWeightFin ht i ∘ sigma := by
      funext k
      have := t.geckWeightFin_geckDiagramFinPerm ht hsigma
        ((t.geckDiagramFinPerm ht hsigma)⁻¹ i) k
      rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at this
    rw [hwt, ← torusCharacter_mulEquivArrowCongr sigma s (t.geckWeightFin ht i)]
    exact congrArg (fun z => torusCharacter z (t.geckWeightFin ht i))
      (funext fun j => by
        rw [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, Equiv.Perm.inv_def])
  have hconj := TauCeti.UniversalEnvelopingAlgebra.kostantNumberedSymmetryMatrix_conj_diagGL
    (t.geckCoordinateLattice ht).toAddSubgroup (t.geckCoordinateBasisFin ht)
    (t.geckDiagramModuleEquiv ht hsigma)
    (t.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff ht hsigma)
    (t.geckDiagramFinPerm ht hsigma)
    (t.geckDiagramModuleEquiv_geckCoordinateBasisFin ht hsigma) A
    (fun i => torusCharacter s (t.geckWeightFin ht i))
  refine Subtype.ext ?_
  rw [coe_geckGraphAutPoints]
  simp only [geckGraphAutMatrix]
  simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
    hconj.trans (congrArg diagGL (funext hpt))

/-- **The graph automorphism on points is natural in the value ring.** In particular it commutes
with the Frobenius endomorphism of the points of the carrier. -/
theorem geckPointsMap_comp_geckGraphAutPoints (hsigma : sigma ∈ t.diagramSymmetry)
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B) :
    (t.geckPointsMap ht f).comp (t.geckGraphAutPoints ht hsigma A).toMonoidHom =
      (t.geckGraphAutPoints ht hsigma B).toMonoidHom.comp (t.geckPointsMap ht f) := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, coe_geckPointsMap, coe_geckGraphAutPoints, coe_geckGraphAutPoints,
    coe_geckPointsMap, map_mul, map_mul, map_inv, map_geckGraphAutMatrix]

/-- **The order of the graph automorphism on points divides that of the diagram symmetry.** An
involution of the numbered diagram therefore gives `γ ^ 2 = 1` on points, and the triality of `D₄`
gives `γ ^ 3 = 1`. -/
@[simp]
theorem geckGraphAutPoints_pow_eq_one (hsigma : sigma ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    {m : ℕ} (hm : sigma ^ m = 1) : t.geckGraphAutPoints ht hsigma A ^ m = 1 := by
  have hX : geckGraphAutNormalizer ht hsigma A ^ m = 1 :=
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact geckGraphAutMatrix_pow_eq_one ht hsigma A hm)
  rw [geckGraphAutPoints, ← map_pow, hX, map_one]

/-- The identity symmetry gives the identity automorphism of the points of the Geck carrier. -/
@[simp]
theorem geckGraphAutPoints_one (A : Type v) [CommRing A] :
    t.geckGraphAutPoints ht t.diagramSymmetry.one_mem A = 1 := by
  simpa using geckGraphAutPoints_pow_eq_one ht t.diagramSymmetry.one_mem A (m := 1) (pow_one _)

end

end TauCeti.DynkinType
