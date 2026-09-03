/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RootInToral

/-!
# Closed root subgroups of the type-D full-spin carrier

For every Bourbaki node of type `D_n`, the raising and lowering root-subgroup maps into
`TauCeti.TypeDSpinCarrier.groupScheme n hn` are closed copies of the additive group scheme.

The proof reads a unit coefficient directly from the exterior model of the full spin
representation. Along the chain, creation at one coordinate after annihilation at the next sends
one singleton exterior-basis vector to another. At the fork, the positive operator creates the
last two coordinates from the vacuum, while the negative operator annihilates them back to the
vacuum. The generic Kostant root-subgroup criterion then makes the coordinate map surjective.

## Main declarations

* `TauCeti.TypeDSpinCarrier.rootSubgroupCoordinateMap_surjective`: every numbered root-subgroup
  coordinate map is surjective.
* `TauCeti.TypeDSpinCarrier.isClosedImmersion_rootSubgroup`: every numbered root subgroup is a
  closed immersion.
* `TauCeti.TypeDSpinCarrier.rootSubgroupClosedSubgroup`: the corresponding closed subgroup scheme.
* `TauCeti.TypeDSpinCarrier.rootSubgroupClosedSubgroupIso`: its canonical isomorphism with the
  additive group scheme.

## References

* `TauCeti/Algebra/Lie/E6/Minuscule/ClosedRootSubgroup.lean`, the formal template for
  the declaration order and proof organization.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Linear Algebraic Groups*, Section 26.
* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.

This supplies the closed-root-subgroup component of the type-`D` pinning required by Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its downstream consumer is milestone L0 of the
CFSGStatement roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory CliffordAlgebra
open scoped Matrix

namespace TauCeti.TypeDSpinCarrier

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

private noncomputable def transportClosedSubgroup
    {G H : Grp (Over (Spec (CommRingCat.of ℤ)))} (h : G = H)
    (S : ClosedSubgroupScheme G) : ClosedSubgroupScheme H :=
  h ▸ S

private theorem coe_transportClosedSubgroup
    {G H : Grp (Over (Spec (CommRingCat.of ℤ)))} (h : G = H)
    (S : ClosedSubgroupScheme G) :
    (transportClosedSubgroup h S).1 = (Subobject.map (eqToHom h)).obj S.1 := by
  cases h
  exact (Subobject.map_id S.1).symm

private noncomputable def basisIndex (s : Finset (Fin n)) : Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin n)) s

@[simp]
private theorem signSet_basisIndex (s : Finset (Fin n)) :
    signSet n (basisIndex n s) = s := by
  simp [basisIndex, signSet]

private noncomputable def rootSourceSet : Fin n ⊕ Fin n → Finset (Fin n)
  | .inl i => if h : (i : ℕ) + 1 < n then {⟨(i : ℕ) + 1, h⟩} else ∅
  | .inr i => if (i : ℕ) + 1 < n then {i}
      else {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}

private noncomputable def rootTargetSet : Fin n ⊕ Fin n → Finset (Fin n)
  | .inl i => if (i : ℕ) + 1 < n then {i}
      else {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}
  | .inr i => if h : (i : ℕ) + 1 < n then {⟨(i : ℕ) + 1, h⟩} else ∅

private def rootCoefficient : Fin n ⊕ Fin n → ℤ
  | .inl i => if (i : ℕ) + 1 < n then 1 else
      TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 2, by omega⟩ : Fin n)
        {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}
  | .inr i => if (i : ℕ) + 1 < n then 1 else
      TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 2, by omega⟩ : Fin n)
          {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} *
        TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
          {⟨n - 1, by omega⟩}

private theorem isUnit_rootCoefficient (k : Fin n ⊕ Fin n) :
    IsUnit (rootCoefficient n hn k) := by
  cases k with
  | inl i =>
      by_cases hnext : (i : ℕ) + 1 < n
      · simp [rootCoefficient, hnext]
      · simp only [rootCoefficient, hnext, ↓reduceIte]
        exact (TauCeti.ExteriorAlgebra.basisEraseSign
          (⟨n - 2, by omega⟩ : Fin n)
          {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}).isUnit
  | inr i =>
      by_cases hnext : (i : ℕ) + 1 < n
      · simp [rootCoefficient, hnext]
      · simp only [rootCoefficient, hnext, ↓reduceIte]
        exact (TauCeti.ExteriorAlgebra.basisEraseSign
          (⟨n - 2, by omega⟩ : Fin n)
          {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} *
          TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
          {⟨n - 1, by omega⟩}).isUnit

private theorem rep_rootGenerator_latticeBasis (k : Fin n ⊕ Fin n) :
    rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))
        ((latticeBasis n (basisIndex n (rootSourceSet n hn k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W) =
      rootCoefficient n hn k •
        ((latticeBasis n (basisIndex n (rootTargetSet n hn k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W) := by
  cases k with
  | inl i =>
      by_cases hnext : (i : ℕ) + 1 < n
      · simp only [TauCeti.serreRootGenerator_inl, coe_latticeBasis, signSet_basisIndex,
          rootSourceSet, rootTargetSet, rootCoefficient, hnext, ↓reduceDIte, ↓reduceIte,
          one_zsmul]
        exact (polarization n).typeDSpinRep_serreE_exteriorBasis_singleton
          (polarizationBasis n) hn hnext
      · simp only [TauCeti.serreRootGenerator_inl, coe_latticeBasis, signSet_basisIndex,
          rootSourceSet, rootTargetSet, rootCoefficient, hnext, ↓reduceDIte, ↓reduceIte]
        exact (polarization n).typeDSpinRep_serreE_exteriorBasis_empty
          (polarizationBasis n) hn hnext
  | inr i =>
      by_cases hnext : (i : ℕ) + 1 < n
      · simp only [TauCeti.serreRootGenerator_inr, coe_latticeBasis, signSet_basisIndex,
          rootSourceSet, rootTargetSet, rootCoefficient, hnext, ↓reduceDIte, ↓reduceIte,
          one_zsmul]
        exact (polarization n).typeDSpinRep_serreF_exteriorBasis_singleton
          (polarizationBasis n) hn hnext
      · simp only [TauCeti.serreRootGenerator_inr, coe_latticeBasis, signSet_basisIndex,
          rootSourceSet, rootTargetSet, rootCoefficient, hnext, ↓reduceDIte, ↓reduceIte]
        exact (polarization n).typeDSpinRep_serreF_exteriorBasis_pair
          (polarizationBasis n) hn hnext

private theorem rep_rootGenerator_sq_apply_latticeBasis (k : Fin n ⊕ Fin n) :
    rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))
      (rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) k))
        ((latticeBasis n (basisIndex n (rootSourceSet n hn k)) : lattice n) :
          ExteriorAlgebra ℚ (polarization n).W)) = 0 := by
  have h := congrArg
    (fun f : Module.End ℚ (ExteriorAlgebra ℚ (polarization n).W) =>
      f ((latticeBasis n (basisIndex n (rootSourceSet n hn k)) : lattice n) :
        ExteriorAlgebra ℚ (polarization n).W))
    ((polarization n).typeDSpinRep_rootGenerator_sq (polarizationBasis n) hn k)
  simpa only [rep, pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

/-- The coordinate morphism of every numbered type-`D` full-spin root subgroup is surjective. -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin n ⊕ Fin n) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
        (latticeBasis n) (basisWeight n) k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isUnit_rootCoefficient n hn k)
    (rep_rootGenerator_latticeBasis n hn k)
    (rep_rootGenerator_sq_apply_latticeBasis n hn k)

/-- Every numbered root-subgroup map into the type-`D` full-spin carrier is a closed immersion. -/
instance isClosedImmersion_rootSubgroup (k : Fin n ⊕ Fin n) :
    IsClosedImmersion (rootSubgroup n hn k).hom.hom.left := by
  have hroot := TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isUnit_rootCoefficient n hn k)
    (rep_rootGenerator_latticeBasis n hn k)
    (rep_rootGenerator_sq_apply_latticeBasis n hn k)
  rw [← closedSubgroupMorphismProperty_iff
    (Spec (CommRingCat.of ℤ)) (rootSubgroup n hn k), rootSubgroup_def,
    (closedSubgroupMorphismProperty (Spec (CommRingCat.of ℤ))).cancel_right_of_respectsIso]
  exact (closedSubgroupMorphismProperty_iff _ _).2 hroot

/-- Every numbered root-subgroup map into the type-`D` full-spin carrier is a monomorphism. -/
theorem mono_rootSubgroup (k : Fin n ⊕ Fin n) : Mono (rootSubgroup n hn k) := by
  have hroot := TauCeti.UniversalEnvelopingAlgebra.mono_kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isUnit_rootCoefficient n hn k)
    (rep_rootGenerator_latticeBasis n hn k)
    (rep_rootGenerator_sq_apply_latticeBasis n hn k)
  rw [rootSubgroup_def]
  let _ := hroot
  infer_instance

/-- A numbered type-`D` full-spin root subgroup, bundled as a closed subgroup scheme. -/
noncomputable def rootSubgroupClosedSubgroup (k : Fin n ⊕ Fin n) :
    ClosedSubgroupScheme (groupScheme n hn) :=
  transportClosedSubgroup (groupScheme_eq_kostantToralGroupScheme n hn).symm
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupInToral
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn)
      (latticeBasis n) (basisWeight n) (isUnit_rootCoefficient n hn k)
      (rep_rootGenerator_latticeBasis n hn k)
      (rep_rootGenerator_sq_apply_latticeBasis n hn k))

/-- The bundled closed root subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (k : Fin n ⊕ Fin n) :
    (rootSubgroupClosedSubgroup n hn k).1 =
      letI := mono_rootSubgroup n hn k
      Subobject.mk (rootSubgroup n hn k) := by
  let _ := TauCeti.UniversalEnvelopingAlgebra.mono_kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isUnit_rootCoefficient n hn k)
    (rep_rootGenerator_latticeBasis n hn k)
    (rep_rootGenerator_sq_apply_latticeBasis n hn k)
  let _ := mono_rootSubgroup n hn k
  rw [rootSubgroupClosedSubgroup, coe_transportClosedSubgroup,
    TauCeti.UniversalEnvelopingAlgebra.coe_kostantRootSubgroupInToral,
    Subobject.map_mk]
  apply Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _)
  simpa only [Iso.refl_hom, Category.id_comp] using rootSubgroup_def n hn k

/-- The bundled numbered root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def rootSubgroupClosedSubgroupIso (k : Fin n ⊕ Fin n) :
    ((rootSubgroupClosedSubgroup n hn k).1 :
      Grp (Over (Spec (CommRingCat.of ℤ)))) ≅ AdditiveGroup.groupScheme ℤ :=
  eqToIso (congrArg (fun P : Subobject (groupScheme n hn) =>
      (P : Grp (Over (Spec (CommRingCat.of ℤ)))))
    (coe_rootSubgroupClosedSubgroup n hn k)) ≪≫
    Subobject.underlyingIso (rootSubgroup n hn k)

/-- The canonical parametrization followed by inclusion is the numbered root-subgroup map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (k : Fin n ⊕ Fin n) :
    (rootSubgroupClosedSubgroupIso n hn k).inv ≫
        (rootSubgroupClosedSubgroup n hn k).1.arrow =
      rootSubgroup n hn k :=
  by
    have harrow :
        (eqToIso (congrArg (fun P : Subobject (groupScheme n hn) =>
          (P : Grp (Over (Spec (CommRingCat.of ℤ)))))
          (coe_rootSubgroupClosedSubgroup n hn k))).inv ≫
            (rootSubgroupClosedSubgroup n hn k).1.arrow =
          (Subobject.mk (rootSubgroup n hn k)).arrow :=
      Subobject.arrow_congr (Subobject.mk (rootSubgroup n hn k))
        (rootSubgroupClosedSubgroup n hn k).1
        (coe_rootSubgroupClosedSubgroup n hn k).symm
    rw [rootSubgroupClosedSubgroupIso, Iso.trans_inv, Category.assoc, harrow,
      Subobject.underlyingIso_arrow]

end

end TauCeti.TypeDSpinCarrier
