/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RootInToral

/-!
# Closed root subgroups of the type-B spin carrier

For every Bourbaki node of type `Bₙ₊₁`, the raising and lowering root-subgroup maps into
`TauCeti.TypeBSpinCarrier.groupScheme n` are closed copies of the additive group scheme.

The spin representation makes the required unit matrix coefficient explicit. At a nonterminal
node, the raising and lowering operators move an exterior singleton between two adjacent
coordinates. At the terminal short node, they create or annihilate the final coordinate, with the
distinguished remainder vector acting by exterior parity. The generic Kostant root-subgroup
criterion then makes the coordinate-ring homomorphism surjective.

## Main declarations

* `TauCeti.TypeBSpinCarrier.rootSubgroupCoordinateMap_surjective`: every numbered root-subgroup
  coordinate-ring homomorphism is surjective.
* `TauCeti.TypeBSpinCarrier.isClosedImmersion_rootSubgroup`: every numbered root subgroup is a
  closed immersion.
* `TauCeti.TypeBSpinCarrier.rootSubgroupClosedSubgroup`: the corresponding closed subgroup scheme.
* `TauCeti.TypeBSpinCarrier.rootSubgroupClosedSubgroupIso`: its canonical isomorphism with the
  additive group scheme.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Linear Algebraic Groups*, Section 26.
* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.ClosedRootSubgroup`, for the corresponding
  type-`D` closed-root-subgroup construction.
-/

public section

open AlgebraicGeometry CategoryTheory CliffordAlgebra

namespace TauCeti.TypeBSpinCarrier

noncomputable section

variable (n : ℕ)

/-! ## Unit-coefficient exterior-basis steps -/

private noncomputable def basisIndex (s : Finset (Fin (n + 1))) : Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin (n + 1))) s

@[simp]
private theorem signSet_basisIndex (s : Finset (Fin (n + 1))) :
    signSet n (basisIndex n s) = s := by
  simp [basisIndex, signSet]

private def rootSourceSet :
    Fin (n + 1) ⊕ Fin (n + 1) → Finset (Fin (n + 1))
  | .inl i => Fin.lastCases ∅ (fun j => {j.succ}) i
  | .inr i => Fin.lastCases {Fin.last n} (fun j => {j.castSucc}) i

private def rootTargetSet :
    Fin (n + 1) ⊕ Fin (n + 1) → Finset (Fin (n + 1))
  | .inl i => Fin.lastCases {Fin.last n} (fun j => {j.castSucc}) i
  | .inr i => Fin.lastCases ∅ (fun j => {j.succ}) i

private theorem rep_rootGenerator_latticeBasis
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily k))
        ((latticeBasis n (basisIndex n (rootSourceSet n k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W) =
      (1 : ℤ) •
        ((latticeBasis n (basisIndex n (rootTargetSet n k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W) := by
  cases k with
  | inl i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [coe_latticeBasis, signSet_basisIndex, rootSourceSet,
          rootTargetSet, Fin.lastCases_last, one_zsmul] using
          (polarization n).typeBSpinRep_simpleRootGenerator_last_exteriorBasis_empty
            (polarizationBasis n) (remainderOne n)
            (TauCeti.splitOddForm_remainderOne ℚ (n + 1))
            (TauCeti.splitOddPolarization_lineCoordinate_remainderOne ℚ (n + 1))
      · simpa only [coe_latticeBasis, signSet_basisIndex, rootSourceSet,
          rootTargetSet, Fin.lastCases_castSucc, one_zsmul] using
          (polarization n).typeBSpinRep_simpleRootGenerator_castSucc_exteriorBasis_singleton
            (polarizationBasis n) (remainderOne n)
            (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) j
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [coe_latticeBasis, signSet_basisIndex, rootSourceSet,
          rootTargetSet, Fin.lastCases_last, one_zsmul] using
          (polarization n).typeBSpinRep_simpleNegativeRootGenerator_last_exteriorBasis_singleton
            (polarizationBasis n) (remainderOne n)
            (TauCeti.splitOddForm_remainderOne ℚ (n + 1))
            (TauCeti.splitOddPolarization_lineCoordinate_remainderOne ℚ (n + 1))
      · simpa only [coe_latticeBasis, signSet_basisIndex, rootSourceSet,
          rootTargetSet, Fin.lastCases_castSucc, one_zsmul] using
          (polarization n).typeBSpinRep_simpleNegativeRootGenerator_castSucc_exteriorBasis_singleton
            (polarizationBasis n) (remainderOne n)
            (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) j

private theorem rep_rootGenerator_sq_apply_latticeBasis
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily k))
      (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.typeBSimpleRootGeneratorFamily k))
        ((latticeBasis n (basisIndex n (rootSourceSet n k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W)) = 0 := by
  have h := congrArg
    (fun f : Module.End ℚ (ExteriorAlgebra ℚ (polarization n).W) =>
      f ((latticeBasis n (basisIndex n (rootSourceSet n k)) : lattice n) :
        ExteriorAlgebra ℚ (polarization n).W))
    ((polarization n).typeBSpinRep_simpleRootGenerator_sq
      (polarizationBasis n) (remainderOne n)
      (TauCeti.splitOddForm_remainderOne ℚ (n + 1)) k)
  simpa only [rep, pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

/-! ## Closed root-subgroup morphisms -/

/-- The coordinate-ring homomorphism of every numbered type-`Bₙ₊₁` spin root subgroup is
surjective. -/
theorem rootSubgroupCoordinateMap_surjective
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) (isNilpotent_rep_rootGenerator n)
        (latticeBasis n) (basisWeight n) k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) isUnit_one
    (rep_rootGenerator_latticeBasis n k)
    (rep_rootGenerator_sq_apply_latticeBasis n k)

/-- Every numbered root-subgroup map into the type-`Bₙ₊₁` spin carrier is a closed immersion. -/
instance isClosedImmersion_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsClosedImmersion (rootSubgroup n k).hom.hom.left := by
  have hroot :=
    TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) isUnit_one
    (rep_rootGenerator_latticeBasis n k)
    (rep_rootGenerator_sq_apply_latticeBasis n k)
  rw [← closedSubgroupMorphismProperty_iff
    (Spec (CommRingCat.of ℤ)) (rootSubgroup n k), rootSubgroup_def,
    (closedSubgroupMorphismProperty (Spec (CommRingCat.of ℤ))).cancel_right_of_respectsIso]
  exact (closedSubgroupMorphismProperty_iff _ _).2 hroot

/-- Every numbered root-subgroup map into the type-`Bₙ₊₁` spin carrier is a monomorphism. -/
theorem mono_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Mono (rootSubgroup n k) :=
  mono_of_isClosedImmersion_underlying (rootSubgroup n k)

/-- A numbered type-`Bₙ₊₁` spin root subgroup, bundled as a closed subgroup scheme. -/
noncomputable def rootSubgroupClosedSubgroup
    (k : Fin (n + 1) ⊕ Fin (n + 1)) : ClosedSubgroupScheme (groupScheme n) :=
  ClosedSubgroupScheme.mk (rootSubgroup n k)

/-- The bundled closed root subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootSubgroupClosedSubgroup n k).1 =
      letI := mono_rootSubgroup n k
      Subobject.mk (rootSubgroup n k) := by
  exact ClosedSubgroupScheme.coe_mk _

/-- The bundled numbered root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def rootSubgroupClosedSubgroupIso
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    ((rootSubgroupClosedSubgroup n k).1 :
      Grp (Over (Spec (CommRingCat.of ℤ)))) ≅ AdditiveGroup.groupScheme ℤ :=
  ClosedSubgroupScheme.mkIso (rootSubgroup n k)

/-- The canonical parametrization followed by inclusion is the numbered root-subgroup map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootSubgroupClosedSubgroupIso n k).inv ≫
        (rootSubgroupClosedSubgroup n k).1.arrow =
      rootSubgroup n k :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (rootSubgroup n k)

end

end TauCeti.TypeBSpinCarrier
