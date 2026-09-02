/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.GeckConstruction.Symmetry
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Basic

/-!
# Diagram symmetries of the pinned Geck lattice

A symmetry of a Dynkin diagram permutes both the roots of the pinned simply connected root datum
and the Bourbaki-numbered simple roots. Geck's construction turns those two permutations into a
coordinate permutation of its defining module. This file specializes that construction to the
pinned data and proves the two facts needed by the Chevalley--Demazure group-scheme construction:

* the coordinate permutation preserves the integral Geck lattice; and
* it intertwines the represented simple raising and lowering generators.

The first point is not a consequence of an abstract root-datum isomorphism: the group-scheme
construction acts on the concrete lattice `TauCeti.DynkinType.geckCoordinateLattice`. Here it is
proved directly from the integer-coordinate characterization of that lattice. The second point is
the representation-level pinning equation which can be passed to
`TauCeti.UniversalEnvelopingAlgebra.kostantGeneratedNumberedSymmetryIso`.

The weight equation in this file also records how the same coordinate permutation normalizes the
represented split torus. It is the remaining input for extending the root-generated symmetry to
the toral carrier.

## Main definitions

* `TauCeti.DynkinType.geckDiagramIndexEquiv`: the coordinate permutation of the pinned Geck
  module.
* `TauCeti.DynkinType.geckDiagramModuleEquiv`: the resulting rational linear equivalence.
* `TauCeti.DynkinType.geckDiagramFinPerm`: the same coordinate permutation in the finite-ordinal
  indexing used by the group-scheme construction.
* `TauCeti.DynkinType.diagramRootGeneratorPerm`: the induced permutation of the simple raising and
  lowering indices.

## Main results

* `TauCeti.DynkinType.geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff`: the coordinate
  permutation preserves the pinned integral lattice in both directions.
* `TauCeti.DynkinType.geckWeight_geckDiagramIndexEquiv`: the weights are permuted
  contragrediently.
* `TauCeti.DynkinType.geckDiagramModuleEquiv_geckCoordinateBasisFin` and
  `TauCeti.DynkinType.geckWeightFin_geckDiagramFinPerm`: the finite-ordinal basis and weight
  equations consumed by the Kostant toral-closure symmetry construction.
* `TauCeti.DynkinType.geckDiagramModuleEquiv_geckRepresentation_rootGenerator`: the defining
  representation intertwines every numbered root generator with its permuted generator.
* `TauCeti.DynkinType.geckDiagramIndexEquiv_pow_eq_one` and
  `TauCeti.DynkinType.geckDiagramFinPerm_pow_eq_one`: the coordinate permutation satisfies every
  order relation the node permutation satisfies.

## References

The coordinate construction is due to M. Geck, *On the construction of semisimple Lie algebras
and Chevalley groups*, Proc. Amer. Math. Soc. **145** (2017), 3233--3247. The passage from a pinned
diagram symmetry to a graph automorphism follows R. W. Carter, *Finite Groups of Lie Type:
Conjugacy Classes and Complex Characters*, §1.15.

This is a prerequisite for the pinned isomorphism theorem in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L1, ordinary and
graph-twisted Steinberg maps, of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {sigma : Equiv.Perm (Fin t.rank)}

/-- The permutation of the support of the pinned rational base induced by a permutation of its
Bourbaki-numbered nodes. -/
def geckDiagramBaseEquiv (sigma : Equiv.Perm (Fin t.rank)) :
    (t.rationalBase ht).support ≃ (t.rationalBase ht).support :=
  (t.simpleSupportEquiv ht).permCongr sigma

/-- The induced permutation on simple-root support acts through the node permutation. -/
@[simp]
theorem geckDiagramBaseEquiv_apply_simpleSupportEquiv (sigma : Equiv.Perm (Fin t.rank))
    (i : Fin t.rank) :
    t.geckDiagramBaseEquiv ht sigma (t.simpleSupportEquiv ht i) =
      t.simpleSupportEquiv ht (sigma i) := by
  rw [geckDiagramBaseEquiv, Equiv.permCongr_apply, Equiv.symm_apply_apply]

private theorem coe_diagramBaseEquiv_eq_indexEquiv (hsigma : sigma ∈ t.diagramSymmetry)
    (i : (t.rationalBase ht).support) :
    ((t.geckDiagramBaseEquiv ht sigma i : (t.rationalBase ht).support) : Fin t.numRoots) =
      (t.rationalDiagramAut ht hsigma).indexEquiv i := by
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  simp only [geckDiagramBaseEquiv, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    rationalDiagramAut_indexEquiv, coe_simpleSupportEquiv, diagramRootPerm_simpleIndex]

/-- The coordinate permutation of the pinned Geck module induced by a symmetry of its
Bourbaki-numbered Dynkin diagram. It acts by the node permutation on the base-support coordinates
and by `TauCeti.DynkinType.diagramRootPerm` on the root coordinates. -/
def geckDiagramIndexEquiv (hsigma : sigma ∈ t.diagramSymmetry) :
    t.GeckIndex ht ≃ t.GeckIndex ht :=
  geckIndexEquiv (t.rationalDiagramAut ht hsigma) (t.geckDiagramBaseEquiv ht sigma)

/-- The diagram symmetry acts on a base-support coordinate by the transported node permutation. -/
@[simp]
theorem geckDiagramIndexEquiv_apply_inl (hsigma : sigma ∈ t.diagramSymmetry)
    (i : (t.rationalBase ht).support) :
    t.geckDiagramIndexEquiv ht hsigma (Sum.inl i) =
      Sum.inl (t.geckDiagramBaseEquiv ht sigma i) := by
  simpa only [geckDiagramIndexEquiv] using
    geckIndexEquiv_apply_inl (t.rationalDiagramAut ht hsigma)
      (t.geckDiagramBaseEquiv ht sigma) i

/-- The diagram symmetry acts on a root coordinate by the induced root permutation. -/
@[simp]
theorem geckDiagramIndexEquiv_apply_inr (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin t.numRoots) :
    t.geckDiagramIndexEquiv ht hsigma (Sum.inr i) =
      Sum.inr (t.diagramRootPerm ht hsigma i) := by
  simpa only [geckDiagramIndexEquiv, rationalDiagramAut_indexEquiv] using
    geckIndexEquiv_apply_inr (t.rationalDiagramAut ht hsigma)
      (t.geckDiagramBaseEquiv ht sigma) i

/-- The rational linear equivalence of the pinned Geck module induced by a diagram symmetry. It is
the permutation of coordinate functions along `TauCeti.DynkinType.geckDiagramIndexEquiv`. -/
def geckDiagramModuleEquiv (hsigma : sigma ∈ t.diagramSymmetry) :
    (t.GeckIndex ht → ℚ) ≃ₗ[ℚ] (t.GeckIndex ht → ℚ) :=
  geckModuleEquiv (t.rationalDiagramAut ht hsigma) (t.geckDiagramBaseEquiv ht sigma)

/-- The pinned Geck-module equivalence acts by precomposition with the inverse coordinate
permutation. -/
@[simp]
theorem geckDiagramModuleEquiv_apply (hsigma : sigma ∈ t.diagramSymmetry)
    (v : t.GeckIndex ht → ℚ) (i : t.GeckIndex ht) :
    t.geckDiagramModuleEquiv ht hsigma v i =
      v ((t.geckDiagramIndexEquiv ht hsigma).symm i) := by
  simpa only [geckDiagramModuleEquiv, geckDiagramIndexEquiv] using
    geckModuleEquiv_apply (t.rationalDiagramAut ht hsigma)
      (t.geckDiagramBaseEquiv ht sigma) v i

/-- The pinned Geck-module equivalence sends a standard coordinate vector to the standard vector
at the permuted coordinate. -/
@[simp]
theorem geckDiagramModuleEquiv_single (hsigma : sigma ∈ t.diagramSymmetry)
    (i : t.GeckIndex ht) (r : ℚ) :
    t.geckDiagramModuleEquiv ht hsigma (Pi.single i r) =
      Pi.single (t.geckDiagramIndexEquiv ht hsigma i) r := by
  simpa only [geckDiagramModuleEquiv, geckDiagramIndexEquiv] using
    geckModuleEquiv_single (t.rationalDiagramAut ht hsigma)
      (t.geckDiagramBaseEquiv ht sigma) i r

/-- **A diagram symmetry preserves the pinned integral Geck lattice.** Membership is equivalent in
both directions because the symmetry merely permutes the integer-valued coordinates. This is the
lattice-stability hypothesis used by the Kostant group-scheme symmetry construction.

This is deliberately not a `simp` lemma: `TauCeti.DynkinType.mem_geckCoordinateLattice_iff` is
itself `simp`, so both sides are unfolded into coordinate conditions before this statement could
ever fire. -/
theorem geckDiagramModuleEquiv_mem_geckCoordinateLattice_iff
    (hsigma : sigma ∈ t.diagramSymmetry) (v : t.GeckIndex ht → ℚ) :
    t.geckDiagramModuleEquiv ht hsigma v ∈ t.geckCoordinateLattice ht ↔
      v ∈ t.geckCoordinateLattice ht := by
  rw [mem_geckCoordinateLattice_iff, mem_geckCoordinateLattice_iff]
  constructor
  · intro hv i
    obtain ⟨z, hz⟩ := hv (t.geckDiagramIndexEquiv ht hsigma i)
    refine ⟨z, ?_⟩
    simpa using hz
  · intro hv i
    obtain ⟨z, hz⟩ := hv ((t.geckDiagramIndexEquiv ht hsigma).symm i)
    exact ⟨z, by simpa using hz⟩

/-- **The coordinate permutation carries weights contragrediently.** Equivalently, the weight of
the permuted coordinate at node `sigma i` is the original weight at node `i`. This is the equation
which makes the same permutation normalize the represented split torus. -/
@[simp]
theorem geckWeight_geckDiagramIndexEquiv (hsigma : sigma ∈ t.diagramSymmetry)
    (x : t.GeckIndex ht) (i : Fin t.rank) :
    t.geckWeight ht (t.geckDiagramIndexEquiv ht hsigma x) (sigma i) =
      t.geckWeight ht x i := by
  cases x with
  | inl x => simp
  | inr x =>
      rw [geckDiagramIndexEquiv_apply_inr, geckWeight_inr, geckWeight_inr]
      simpa only [rationalDiagramAut_indexEquiv, coe_simpleSupportEquiv,
        diagramRootPerm_simpleIndex] using
          pairingIn_indexEquiv ℤ (t.rationalDiagramAut ht hsigma).toHom x
            (t.simpleSupportEquiv ht i)

/-! ## The coordinate permutation in the finite-ordinal indexing -/

/-- **The coordinate permutation of a diagram symmetry, in the finite-ordinal indexing.** The
group-scheme construction indexes the Geck coordinate basis by `Fin (t.geckDim ht)` through
`Fintype.equivFin`; this is `TauCeti.DynkinType.geckDiagramIndexEquiv` transported along that
reindexing. -/
def geckDiagramFinPerm (hsigma : sigma ∈ t.diagramSymmetry) :
    Equiv.Perm (Fin (t.geckDim ht)) :=
  (Fintype.equivFin (t.GeckIndex ht)).permCongr (t.geckDiagramIndexEquiv ht hsigma)

@[simp]
theorem equivFin_symm_geckDiagramFinPerm (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin (t.geckDim ht)) :
    (Fintype.equivFin (t.GeckIndex ht)).symm (t.geckDiagramFinPerm ht hsigma i) =
      t.geckDiagramIndexEquiv ht hsigma ((Fintype.equivFin (t.GeckIndex ht)).symm i) := by
  simp [geckDiagramFinPerm, Equiv.permCongr_apply]

/-- The pinned Geck-module symmetry permutes the finite-ordinal coordinate basis. This is the
basis-permutation hypothesis of the Kostant toral-closure symmetry construction.

This is deliberately not a `simp` lemma: `TauCeti.DynkinType.coe_geckCoordinateBasisFin` and
`TauCeti.DynkinType.geckDiagramModuleEquiv_single` are themselves `simp`, so both sides are
already rewritten to the same standard coordinate vector and `simp` proves this statement
outright. -/
theorem geckDiagramModuleEquiv_geckCoordinateBasisFin (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin (t.geckDim ht)) :
    t.geckDiagramModuleEquiv ht hsigma
        ((t.geckCoordinateBasisFin ht i : (t.geckCoordinateLattice ht).toAddSubgroup) :
          t.GeckIndex ht → ℚ) =
      ((t.geckCoordinateBasisFin ht (t.geckDiagramFinPerm ht hsigma i) :
          (t.geckCoordinateLattice ht).toAddSubgroup) : t.GeckIndex ht → ℚ) := by
  rw [coe_geckCoordinateBasisFin, coe_geckCoordinateBasisFin, geckDiagramModuleEquiv_single,
    equivFin_symm_geckDiagramFinPerm]

/-- The finite-ordinal Geck weights are equivariant for the coordinate permutation and the node
permutation. This is the weight hypothesis of the Kostant toral-closure symmetry construction, and
it is what makes the same permutation intertwine the represented split torus with relabelling. -/
@[simp]
theorem geckWeightFin_geckDiagramFinPerm (hsigma : sigma ∈ t.diagramSymmetry)
    (i : Fin (t.geckDim ht)) (k : Fin t.rank) :
    t.geckWeightFin ht (t.geckDiagramFinPerm ht hsigma i) (sigma k) = t.geckWeightFin ht i k := by
  simp only [geckWeightFin, equivFin_symm_geckDiagramFinPerm, geckWeight_geckDiagramIndexEquiv]

/-! ## The order of the coordinate permutation -/

/-- The coordinate permutation of the pinned Geck module is multiplicative in the node
permutation. This and the unit law below only build the homomorphism behind the order statements
that follow, which are what consumers use. -/
private theorem geckDiagramIndexEquiv_mul {tau : Equiv.Perm (Fin t.rank)}
    (hsigma : sigma ∈ t.diagramSymmetry) (htau : tau ∈ t.diagramSymmetry) :
    t.geckDiagramIndexEquiv ht (t.diagramSymmetry.mul_mem hsigma htau) =
      t.geckDiagramIndexEquiv ht hsigma * t.geckDiagramIndexEquiv ht htau := by
  ext x
  cases x with
  | inl i =>
      rw [Equiv.Perm.mul_apply, geckDiagramIndexEquiv_apply_inl, geckDiagramIndexEquiv_apply_inl,
        geckDiagramIndexEquiv_apply_inl, geckDiagramBaseEquiv, geckDiagramBaseEquiv,
        geckDiagramBaseEquiv]
      simp [Equiv.Perm.mul_apply]
  | inr i =>
      rw [Equiv.Perm.mul_apply, geckDiagramIndexEquiv_apply_inr, geckDiagramIndexEquiv_apply_inr,
        geckDiagramIndexEquiv_apply_inr, diagramRootPerm_mul, Equiv.Perm.mul_apply]

/-- The identity node permutation induces the identity coordinate permutation. -/
private theorem geckDiagramIndexEquiv_one :
    t.geckDiagramIndexEquiv ht t.diagramSymmetry.one_mem = 1 := by
  ext x
  cases x with
  | inl i =>
      rw [geckDiagramIndexEquiv_apply_inl, geckDiagramBaseEquiv]
      simp
  | inr i =>
      rw [geckDiagramIndexEquiv_apply_inr, diagramRootPerm_one]
      simp

/-- The coordinate permutations of the pinned Geck module, as a homomorphism out of the symmetry
group of the Bourbaki-numbered Cartan matrix. This is what converts a relation satisfied by a node
permutation into the same relation for the coordinate permutation it induces; consumers use the
order statements below rather than the homomorphism itself. -/
private def geckDiagramIndexEquivHom : t.diagramSymmetry →* Equiv.Perm (t.GeckIndex ht) where
  toFun g := t.geckDiagramIndexEquiv ht g.2
  map_one' := geckDiagramIndexEquiv_one ht
  map_mul' g₁ g₂ := geckDiagramIndexEquiv_mul ht g₁.2 g₂.2

/-- **A node permutation of finite order induces a coordinate permutation of the pinned Geck
module satisfying the same relation.** -/
theorem geckDiagramIndexEquiv_pow_eq_one (hsigma : sigma ∈ t.diagramSymmetry) {m : ℕ}
    (hm : sigma ^ m = 1) : t.geckDiagramIndexEquiv ht hsigma ^ m = 1 := by
  have h : (⟨sigma, hsigma⟩ : t.diagramSymmetry) ^ m = 1 := Subtype.ext (by simpa using hm)
  calc t.geckDiagramIndexEquiv ht hsigma ^ m
      = geckDiagramIndexEquivHom ht (⟨sigma, hsigma⟩ ^ m) := by rw [map_pow]; rfl
    _ = 1 := by rw [h, map_one]

/-- **A node permutation of finite order induces a finite-ordinal coordinate permutation
satisfying the same relation.** This is the source of the order relation for the graph
automorphism on the algebra-valued points of the pinned Geck carrier. -/
theorem geckDiagramFinPerm_pow_eq_one (hsigma : sigma ∈ t.diagramSymmetry) {m : ℕ}
    (hm : sigma ^ m = 1) : t.geckDiagramFinPerm ht hsigma ^ m = 1 := by
  have hcongr : t.geckDiagramFinPerm ht hsigma =
      (Fintype.equivFin (t.GeckIndex ht)).permCongrHom (t.geckDiagramIndexEquiv ht hsigma) :=
    (congrFun (Equiv.permCongrHom_coe (Fintype.equivFin (t.GeckIndex ht))) _).symm
  rw [hcongr, ← map_pow, geckDiagramIndexEquiv_pow_eq_one ht hsigma hm, map_one]

/-! ## The permutation of the numbered generators -/

/-- The permutation of the simple raising and lowering indices induced by a diagram symmetry. The
same node permutation acts on both halves. -/
def diagramRootGeneratorPerm (sigma : Equiv.Perm (Fin t.rank)) :
    Equiv.Perm (Fin t.rank ⊕ Fin t.rank) :=
  Equiv.sumCongr sigma sigma

/-- The diagram permutation acts on a raising-generator index through `sigma`. -/
@[simp]
theorem diagramRootGeneratorPerm_apply_inl (i : Fin t.rank) :
    diagramRootGeneratorPerm sigma (Sum.inl i) = Sum.inl (sigma i) := by
  rw [diagramRootGeneratorPerm]
  rfl

/-- The diagram permutation acts on a lowering-generator index through `sigma`. -/
@[simp]
theorem diagramRootGeneratorPerm_apply_inr (i : Fin t.rank) :
    diagramRootGeneratorPerm sigma (Sum.inr i) = Sum.inr (sigma i) := by
  rw [diagramRootGeneratorPerm]
  rfl

/-- **A relation satisfied by a diagram symmetry is satisfied by the permutation it induces on the
numbered generator indices.** The induced permutation is the diagonal value of the bundled
homomorphism `Equiv.Perm.sumCongrHom`, so it inherits that homomorphism's power law. -/
theorem diagramRootGeneratorPerm_pow_eq_one {m : ℕ} (hm : sigma ^ m = 1) :
    diagramRootGeneratorPerm sigma ^ m = 1 := by
  have hsum : diagramRootGeneratorPerm sigma =
      Equiv.Perm.sumCongrHom (Fin t.rank) (Fin t.rank) (sigma, sigma) :=
    Equiv.ext fun i => by cases i <;> simp
  have hpair : ((sigma, sigma) : Equiv.Perm (Fin t.rank) × Equiv.Perm (Fin t.rank)) ^ m = 1 :=
    Prod.ext hm hm
  rw [hsum, ← map_pow, hpair, map_one]

/-- **The pinned Geck-module symmetry intertwines every represented simple root generator with
the generator carrying the permuted number.** This is exactly the additive pinning equation
required to construct the corresponding automorphism of the root-generated Kostant group scheme.
-/
@[simp]
theorem geckDiagramModuleEquiv_geckRepresentation_rootGenerator
    (hsigma : sigma ∈ t.diagramSymmetry) (i : Fin t.rank ⊕ Fin t.rank)
    (v : t.GeckIndex ht → ℚ) :
    t.geckDiagramModuleEquiv ht hsigma
        (t.geckRepresentation ht
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (t.lieAlgebra ht)
            (_root_.TensorAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))) v) =
      t.geckRepresentation ht
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ (t.lieAlgebra ht)
            (_root_.TensorAlgebra.ι ℚ
              ((t.lieBasis ht).rootGenerator (diagramRootGeneratorPerm sigma i))))
        (t.geckDiagramModuleEquiv ht hsigma v) := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply,
    ← _root_.UniversalEnvelopingAlgebra.ι_apply]
  cases i with
  | inl i =>
      simp only [LieAlgebra.Basis.rootGenerator_inl, diagramRootGeneratorPerm_apply_inl,
        geckRepresentation_ι_apply, coe_lieBasis_e]
      simpa only [geckDiagramModuleEquiv, geckDiagramBaseEquiv, Equiv.permCongr_apply,
        Equiv.symm_apply_apply] using
          geckModuleEquiv_mulVec_e (t.rationalDiagramAut ht hsigma)
            (t.geckDiagramBaseEquiv ht sigma)
            (coe_diagramBaseEquiv_eq_indexEquiv ht hsigma) (t.simpleSupportEquiv ht i) v
  | inr i =>
      simp only [LieAlgebra.Basis.rootGenerator_inr, diagramRootGeneratorPerm_apply_inr,
        geckRepresentation_ι_apply, coe_lieBasis_f]
      simpa only [geckDiagramModuleEquiv, geckDiagramBaseEquiv, Equiv.permCongr_apply,
        Equiv.symm_apply_apply] using
          geckModuleEquiv_mulVec_f (t.rationalDiagramAut ht hsigma)
            (t.geckDiagramBaseEquiv ht sigma)
            (coe_diagramBaseEquiv_eq_indexEquiv ht hsigma) (t.simpleSupportEquiv ht i) v

end

end TauCeti.DynkinType
