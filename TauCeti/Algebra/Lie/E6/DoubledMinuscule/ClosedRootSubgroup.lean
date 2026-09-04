/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RootInToral

/-!
# Closed root subgroups of the doubled type-E6 minuscule carrier

The twelve numbered raising and lowering maps into `TauCeti.E6DoubledMinuscule.groupScheme` are
closed copies of the additive group scheme. For every Bourbaki node one explicit edge of the
minuscule weight graph recovers the root-subgroup parameter as a matrix coordinate: the raising
operator carries the basis vector at the negative end of the edge to the basis vector at its
positive end with coefficient one, and the lowering operator traverses the same edge in reverse.

The edge is chosen inside the first of the two blocks. The doubled carrier is built from
`V(ϖ₁) ⊕ V(ϖ₆)`, and `TauCeti.E6DoubledMinuscule.summandSign` records that the structure
constants of the second block are the negatives of those of the first, so an edge there would
carry the coefficient `-1`. Both coefficients are units, so either block would do; taking the
first keeps the selected edge the one the `27`-dimensional carrier already uses in
`TauCeti/Algebra/Lie/E6/Minuscule/ClosedRootSubgroup.lean`, and the surjectivity a closed
immersion needs only asks for one unit-coefficient edge per node.

The generic Kostant root-subgroup construction turns that unit-coefficient basis step into a
surjection from the carrier's coordinate Hopf algebra onto the coordinate algebra of `𝔾ₐ`.
Consequently each numbered root-subgroup morphism is a closed immersion, and its
scheme-theoretic image is bundled below as a closed subgroup canonically isomorphic to `𝔾ₐ`.

Nothing here asserts reductivity, that the carrier's weight torus is maximal, that the carrier is
a pinned Chevalley--Demazure group scheme, or that the `E₆` diagram symmetry acts on it.

## Main declarations

* `TauCeti.E6DoubledMinuscule.rootSubgroupCoordinateMap_surjective`: every numbered
  root-subgroup coordinate map is surjective.
* `TauCeti.E6DoubledMinuscule.isClosedImmersion_rootSubgroup`: every numbered root-subgroup
  morphism is a closed immersion.
* `TauCeti.E6DoubledMinuscule.rootSubgroupClosedSubgroup`: its image as a closed subgroup scheme.
* `TauCeti.E6DoubledMinuscule.rootSubgroupClosedSubgroupIso`: the canonical isomorphism of that
  image with the additive group scheme.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 12.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
* The declaration order and proof organization follow
  `TauCeti/Algebra/Lie/E6/Minuscule/ClosedRootSubgroup.lean`, the same argument on the
  `27`-dimensional minuscule carrier.

## Roadmap

This supplies the closed-root-subgroup component of a pinning for the explicit full-weight
doubled type-`E₆` carrier, in the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. That carrier is the one the graph-twisted family
`²E₆(q)` of milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` needs, the `E₆` diagram
symmetry not acting on the `27`-dimensional one.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

/-! ## A unit-coefficient edge at every simple root -/

/-- A minuscule weight whose pairing with the given simple coroot is `-1`. The choice is internal
to the coordinate proof; no public declaration depends on which suitable weight is selected. -/
private noncomputable def negativeWeightIndex (i : Fin 6) : Fin 27 :=
  (exists_e6MinusculeWeight_apply_eq_neg_one i).choose

private theorem e6MinusculeWeight_negativeWeightIndex (i : Fin 6) :
    e6MinusculeWeight (negativeWeightIndex i) i = -1 :=
  (exists_e6MinusculeWeight_apply_eq_neg_one i).choose_spec

/-- The block coordinate at which the selected edge of a raising or lowering root generator
starts. It lies in the `V(ϖ₁)` block, where the structure constant is `1`. -/
private def blockSource : Fin 6 ⊕ Fin 6 → Fin 27 ⊕ Fin 27
  | .inl i => .inl (negativeWeightIndex i)
  | .inr i => .inl (e6MinusculeReflection i (negativeWeightIndex i))

/-- The block coordinate at which the selected edge of a raising or lowering root generator
ends. -/
private def blockTarget : Fin 6 ⊕ Fin 6 → Fin 27 ⊕ Fin 27
  | .inl i => .inl (e6MinusculeReflection i (negativeWeightIndex i))
  | .inr i => .inl (negativeWeightIndex i)

/-- The source matrix coordinate of the selected edge, in the fifty-four coordinates the carrier
is cut out in. -/
private def rootSource (k : Fin 6 ⊕ Fin 6) : Fin 54 := matrixIndexEquiv (blockSource k)

/-- The target matrix coordinate of the selected edge. -/
private def rootTarget (k : Fin 6 ⊕ Fin 6) : Fin 54 := matrixIndexEquiv (blockTarget k)

private theorem coe_matrixBasis_rootSource (k : Fin 6 ⊕ Fin 6) :
    ((matrixBasis (rootSource k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) =
      Pi.single (blockSource k) 1 := by
  rw [matrixBasis_apply, rootSource, Equiv.symm_apply_apply, coe_latticeBasis]

private theorem coe_matrixBasis_rootTarget (k : Fin 6 ⊕ Fin 6) :
    ((matrixBasis (rootTarget k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) =
      Pi.single (blockTarget k) 1 := by
  rw [matrixBasis_apply, rootTarget, Equiv.symm_apply_apply, coe_latticeBasis]

private theorem rep_serreRootGenerator_matrixBasis (k : Fin 6 ⊕ Fin 6) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))
        ((matrixBasis (rootSource k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) =
      (1 : ℤ) • ((matrixBasis (rootTarget k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [coe_matrixBasis_rootSource, coe_matrixBasis_rootTarget, one_smul]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rep_ι_apply, rationalSerreRepresentation_serreE,
        Matrix.mulVec_single_one]
      ext a
      simp [blockSource, blockTarget, raisingMatrixQ_apply, Pi.single_apply,
        e6MinusculeWeight_negativeWeightIndex]
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rep_ι_apply, rationalSerreRepresentation_serreF,
        Matrix.mulVec_single_one]
      ext a
      simp [blockSource, blockTarget, loweringMatrixQ_apply, Pi.single_apply,
        e6MinusculeWeight_negativeWeightIndex, e6MinusculeReflection_apply_apply]

private theorem rep_serreRootGenerator_sq_apply_matrixBasis (k : Fin 6 ⊕ Fin 6) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))
        ((matrixBasis (rootSource k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ)) = 0 := by
  have h := congrArg
    (fun f : Module.End ℚ ((Fin 27 ⊕ Fin 27) → ℚ) =>
      f ((matrixBasis (rootSource k) : lattice) : (Fin 27 ⊕ Fin 27) → ℚ))
    (rep_serreRootGenerator_sq k)
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

/-! ## Closed root-subgroup morphisms -/

/-- **The coordinate morphism of every numbered doubled type-`E₆` minuscule root subgroup is
surjective.** The selected minuscule-weight edge has coefficient one, so a single matrix
coordinate recovers the additive parameter. -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin 6 ⊕ Fin 6) :
    Function.Surjective
      (kostantRootSubgroupToralCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
        k).hom :=
  kostantRootSubgroupToralCoordinateMap_surjective
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice k isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    isUnit_one (rep_serreRootGenerator_matrixBasis k)
    (rep_serreRootGenerator_sq_apply_matrixBasis k)

/-- **Every numbered root-subgroup map into the doubled type-`E₆` minuscule carrier is a closed
immersion.** Its scheme-theoretic image is therefore a closed copy of `𝔾ₐ`, as a pinning requires
of its root subgroups. -/
instance isClosedImmersion_rootSubgroup (k : Fin 6 ⊕ Fin 6) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [rootSubgroup_def]
  exact isClosedImmersion_kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice k isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    isUnit_one (rep_serreRootGenerator_matrixBasis k)
    (rep_serreRootGenerator_sq_apply_matrixBasis k)

/-- Every numbered root-subgroup map into the doubled type-`E₆` minuscule carrier is a
monomorphism. -/
theorem mono_rootSubgroup (k : Fin 6 ⊕ Fin 6) : Mono (rootSubgroup k) :=
  mono_of_isClosedImmersion_underlying (rootSubgroup k)

/-- **A numbered doubled type-`E₆` minuscule root subgroup as a closed subgroup scheme of the
carrier.** -/
noncomputable def rootSubgroupClosedSubgroup (k : Fin 6 ⊕ Fin 6) :
    ClosedSubgroupScheme groupScheme :=
  ClosedSubgroupScheme.mk (rootSubgroup k)

/-- The bundled closed root subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (k : Fin 6 ⊕ Fin 6) :
    (rootSubgroupClosedSubgroup k).1 =
      letI := mono_rootSubgroup k
      Subobject.mk (rootSubgroup k) :=
  ClosedSubgroupScheme.coe_mk _

/-- The bundled numbered root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def rootSubgroupClosedSubgroupIso (k : Fin 6 ⊕ Fin 6) :
    ((rootSubgroupClosedSubgroup k).1 :
      Grp (Over (Spec (CommRingCat.of ℤ)))) ≅ AdditiveGroup.groupScheme ℤ :=
  ClosedSubgroupScheme.mkIso (rootSubgroup k)

/-- The canonical parametrization of the bundled closed subgroup followed by its inclusion is the
numbered doubled type-`E₆` root-subgroup map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (k : Fin 6 ⊕ Fin 6) :
    (rootSubgroupClosedSubgroupIso k).inv ≫ (rootSubgroupClosedSubgroup k).1.arrow =
      rootSubgroup k :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (rootSubgroup k)

end

end TauCeti.E6DoubledMinuscule
