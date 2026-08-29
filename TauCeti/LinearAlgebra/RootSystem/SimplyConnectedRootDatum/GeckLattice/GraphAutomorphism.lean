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

The automorphism is that of the carrier over `ℤ`, before any base change or passage to points, and
it acts on the whole carrier rather than on the elementary subgroup its root subgroups generate.
The Geck weights span the root lattice rather than, in general, the full character lattice, so this
carrier is not yet the simply connected one a finite group of Lie type is built from. Nothing here
asserts reductivity, maximality of the weight torus, or any finiteness or simplicity statement.

## Main definitions

* `TauCeti.DynkinType.geckGraphAut`: the graph automorphism of the pinned Geck carrier.

## Main results

* `TauCeti.DynkinType.geckRootSubgroup_comp_geckGraphAut_hom` and its inverse counterpart: the
  graph automorphism renumbers the pinned root subgroups by `σ`.
* `TauCeti.DynkinType.geckWeightTorus_comp_geckGraphAut_hom` and its inverse counterpart: it
  intertwines the weight torus morphism with the relabelling of its coordinates.
* `TauCeti.DynkinType.geckGraphAut_pow_eq_one`: the order relation.
* `TauCeti.DynkinType.geckGraphAut_one`: the identity symmetry gives the identity automorphism.

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

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {sigma : Equiv.Perm (Fin t.rank)}

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
    (fun i v => by
      simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using
        t.geckDiagramModuleEquiv_geckRepresentation_rootGenerator ht hsigma i v)
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

end

end TauCeti.DynkinType
