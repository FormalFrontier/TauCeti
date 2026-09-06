/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
import TauCeti.CategoryTheory.Comma.Over

/-!
# Closed root subgroups of the Geck carrier

The numbered raising and lowering maps into the pinned Geck carrier are closed copies of the
additive group. The parameter is recovered from one explicit matrix coordinate: for a simple root
`i`, the raising divided-power exponential sends the coordinate vector at `-i` toward the Cartan
coordinate at `i`, while the lowering exponential does the same from `i`. In both cases that
coordinate is exactly the parameter, since its degree-one coefficient is `1` and every other
divided-power coefficient vanishes.

## Main declarations

* `TauCeti.DynkinType.geckRootSubgroupMatrix_apply`: a distinguished matrix entry recovers the
  parameter of a numbered root subgroup.
* `TauCeti.DynkinType.geckRootSubgroupPoints_injective`: every numbered root-subgroup map on
  points is injective.
* `TauCeti.DynkinType.geckRootSubgroupCoordinateMap_surjective`: the coordinate map of every
  numbered Geck root subgroup is surjective.
* `TauCeti.DynkinType.isClosedImmersion_geckRootSubgroup`: every numbered root-subgroup map
  `𝔾ₐ → G` is a closed immersion.
* `TauCeti.DynkinType.geckRootSubgroupClosedSubgroupIso`: the resulting closed subgroup is
  canonically isomorphic to `𝔾ₐ`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

This supplies the closed-root-subgroup condition in the pinning target of Layer 9 of the
ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.DynkinType

universe v

noncomputable section

attribute [local instance] TauCeti.moduleNNRat

variable (t : DynkinType) (ht : t.Valid)

/-- The finite coordinate row corresponding to a numbered simple root. -/
abbrev geckRootRow (i : Fin t.rank) : Fin (t.geckDim ht) :=
  Fintype.equivFin (t.GeckIndex ht) (.inl (t.simpleSupportEquiv ht i))

/-- The finite coordinate column that recovers a numbered root-subgroup parameter. -/
abbrev geckRootColumn (i : Fin t.rank ⊕ Fin t.rank) : Fin (t.geckDim ht) :=
  match i with
  | .inl i =>
      Fintype.equivFin (t.GeckIndex ht)
        (.inr ((t.rationalRootSystem ht).reflectionPerm
          (t.simpleSupportEquiv ht i) (t.simpleSupportEquiv ht i)))
  | .inr i => Fintype.equivFin (t.GeckIndex ht)
      (.inr (t.simpleSupportEquiv ht i : Fin t.numRoots))

private theorem geckRootSubgroup_dividedPower_repr
    (i : Fin t.rank ⊕ Fin t.rank) (n : ℕ) :
    (t.geckCoordinateBasisFin ht).repr
        (TauCeti.integralDividedPower
          (t.geckRepresentation ht
            (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
          (t.geckCoordinateLattice ht).toAddSubgroup n
          (fun _ hv =>
            TauCeti.UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem
            (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
            (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i n hv)
          (t.geckCoordinateBasisFin ht (t.geckRootColumn ht i)))
        (t.geckRootRow ht (Sum.elim id id i)) =
      if n = 1 then 1 else 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [t.intCast_geckCoordinateBasisFin_repr ht, TauCeti.coe_integralDividedPower_apply,
    ← TauCeti.Associative.map_dividedPower, Module.End.smul_def,
    t.geckRepresentation_dividedPower_ι_apply ht, t.coe_geckCoordinateBasisFin ht,
    Matrix.mulVec_single_one, Matrix.col_apply]
  cases i with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl, t.coe_lieBasis_e ht]
      simp only [geckRootRow, geckRootColumn, Equiv.symm_apply_apply, Sum.elim_inl]
      let _i := (t.rationalRootSystem ht).indexNeg
      simpa only [id_eq, RootPairing.indexNeg_neg, Int.cast_ite, Int.cast_one,
        Int.cast_zero] using
        RootPairing.GeckConstruction.dividedPower_e_apply_inl_inr_neg
          (t.simpleSupportEquiv ht i) n
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr, t.coe_lieBasis_f ht]
      simp only [geckRootRow, geckRootColumn, Equiv.symm_apply_apply, Sum.elim_inr]
      simpa only [id_eq, Int.cast_ite, Int.cast_one, Int.cast_zero] using
        RootPairing.GeckConstruction.dividedPower_f_apply_inl_inr
          (t.simpleSupportEquiv ht i) n

private theorem two_le_nilpotencyClass_geckRootOperator
    (i : Fin t.rank ⊕ Fin t.rank) :
    2 ≤ nilpotencyClass (t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))) := by
  have hrestricted : TauCeti.integralDividedPower
      (t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)))
      (t.geckCoordinateLattice ht).toAddSubgroup 1
      (fun _ hv =>
        TauCeti.UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i 1 hv)
      (t.geckCoordinateBasisFin ht (t.geckRootColumn ht i)) ≠ 0 := by
    intro hzero
    have hcoord := congrArg
      (fun v => (t.geckCoordinateBasisFin ht).repr v
        (t.geckRootRow ht (Sum.elim id id i))) hzero
    rw [t.geckRootSubgroup_dividedPower_repr ht, map_zero] at hcoord
    simp at hcoord
  have hx : t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)) ≠ 0 := by
    intro hzero
    apply hrestricted
    apply Subtype.ext
    rw [TauCeti.coe_integralDividedPower_apply, TauCeti.Associative.dividedPower_one,
      hzero, zero_smul]
    rfl
  by_contra hlt
  have hone : (t.geckRepresentation ht
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))) ^ 1 = 0 :=
    pow_eq_zero_of_le (by omega)
      (pow_nilpotencyClass (t.isNilpotent_geckRepresentation_rootGenerator ht i))
  rw [pow_one] at hone
  exact hx hone

/-- The distinguished root row and column of a represented numbered root subgroup recover its
additive parameter. -/
theorem geckRootSubgroupMatrix_apply (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A]
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    t.geckRootSubgroupMatrix ht i q
        (t.geckRootRow ht (Sum.elim id id i)) (t.geckRootColumn ht i) =
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply,
    TauCeti.UniversalEnvelopingAlgebra.repr_kostantRootSubgroupPoints_baseChange]
  simp_rw [t.geckRootSubgroup_dividedPower_repr ht]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n hn hne
    simp [hne]
  · intro hnot
    have htwo := t.two_le_nilpotencyClass_geckRootOperator ht i
    exact (hnot (Finset.mem_range.mpr htwo)).elim

/-- **Every parametrized numbered root subgroup in the Geck carrier points is injective.** -/
theorem geckRootSubgroupPoints_injective (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] : Function.Injective (t.geckRootSubgroupPoints ht i A) := by
  intro u u' huu'
  have hentry := congrArg
    (fun g : t.geckPoints ht A =>
      (((g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A)
          (t.geckRootRow ht (Sum.elim id id i)) (t.geckRootColumn ht i))) huu'
  apply Multiplicative.toAdd.injective
  simpa only [t.coe_geckRootSubgroupPoints ht, t.geckRootSubgroupMatrix_apply ht,
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply] using hentry

/-- The coordinate map of a numbered root subgroup before passage to the toral closure. -/
private abbrev geckRepresentedRootCoordinateMap (i : Fin t.rank ⊕ Fin t.rank) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
    (t.isNilpotent_geckRepresentation_rootGenerator ht i) (t.geckCoordinateBasisFin ht)

private theorem geckRepresentedRootCoordinateMap_X (i : Fin t.rank ⊕ Fin t.rank) :
    (t.geckRepresentedRootCoordinateMap ht i).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (t.geckDim ht)
          (GeneralLinear.coordinateRingMap ℤ (t.geckDim ht)
            (MvPolynomial.X
              (t.geckRootRow ht (Sum.elim id id i), t.geckRootColumn ht i)))) =
      SymmetricAlgebra.ι ℤ ℤ 1 := by
  have key :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap_apply
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
      (t.isNilpotent_geckRepresentation_rootGenerator ht i) (t.geckCoordinateBasisFin ht)
      (SymmetricAlgebra ℤ ℤ) (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ)))
      (t.geckRootRow ht (Sum.elim id id i)) (t.geckRootColumn ht i)
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply] at key
  calc
    _ = t.geckRootSubgroupMatrix ht i
        (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ)))
        (t.geckRootRow ht (Sum.elim id id i)) (t.geckRootColumn ht i) := by
          rw [TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply]
          exact key
    _ = Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv
        (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ)))) :=
      t.geckRootSubgroupMatrix_apply ht i _ _
    _ = _ := by
      rw [AdditiveGroup.toAdd_gaPointsMulEquiv, WithConv.ofConv_toConv]
      rfl

private theorem geckRepresentedRootCoordinateMap_surjective
    (i : Fin t.rank ⊕ Fin t.rank) :
    Function.Surjective (t.geckRepresentedRootCoordinateMap ht i).hom := by
  have hgen : SymmetricAlgebra.ι ℤ ℤ 1 ∈
      (t.geckRepresentedRootCoordinateMap ht i).hom.toAlgHom.range := by
    exact (AlgHom.mem_range _).2
      ⟨GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (t.geckDim ht)
        (GeneralLinear.coordinateRingMap ℤ (t.geckDim ht)
          (MvPolynomial.X
            (t.geckRootRow ht (Sum.elim id id i), t.geckRootColumn ht i))),
        t.geckRepresentedRootCoordinateMap_X ht i⟩
  intro y
  have hy : y ∈ (t.geckRepresentedRootCoordinateMap ht i).hom.toAlgHom.range := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap z => exact Subalgebra.algebraMap_mem _ z
    | ι z =>
        have hz : SymmetricAlgebra.ι ℤ ℤ z = z • SymmetricAlgebra.ι ℤ ℤ 1 := by
          rw [← map_zsmul]
          congr 1
          simp
        rw [hz]
        exact zsmul_mem hgen z
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨z, hz⟩

/-- The coordinate morphism of a numbered root subgroup after factorization through the Geck
carrier. -/
noncomputable abbrev geckRootSubgroupCoordinateMap (i : Fin t.rank ⊕ Fin t.rank) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i

/-- **The coordinate morphism of every numbered Geck root subgroup is surjective.** The explicit
Cartan/root matrix coordinate recovers the polynomial generator before and after factorization
through the common-kernel quotient defining the carrier. -/
theorem geckRootSubgroupCoordinateMap_surjective (i : Fin t.rank ⊕ Fin t.rank) :
    Function.Surjective (t.geckRootSubgroupCoordinateMap ht i).hom :=
  UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i
      (t.geckRepresentedRootCoordinateMap_surjective ht i)

/-- **Every numbered root-subgroup map into the Geck carrier is a closed immersion.** Thus its
scheme-theoretic image is a closed copy of `𝔾ₐ`, as required of the root subgroups in a pinning. -/
instance isClosedImmersion_geckRootSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    IsClosedImmersion (t.geckRootSubgroup ht i).hom.hom.left := by
  let e₂ := (eqToHom (t.geckGroupScheme_def ht).symm).hom.hom.left
  have hroot :=
    TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral_of_surjective
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i
      (t.geckRootSubgroupCoordinateMap_surjective ht i)
  have hcomp :=
    (MorphismProperty.cancel_right_of_respectsIso _
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i).hom.hom.left e₂).2 hroot
  rw [geckRootSubgroup_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact hcomp

/-- Every numbered root-subgroup map into the Geck carrier is a monomorphism. -/
theorem mono_geckRootSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    Mono (t.geckRootSubgroup ht i) :=
  mono_of_isClosedImmersion_underlying (t.geckRootSubgroup ht i)

/-- **A numbered Geck root subgroup as a closed subgroup scheme of the carrier.** -/
noncomputable def geckRootSubgroupClosedSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    ClosedSubgroupScheme (t.geckGroupScheme ht) :=
  ClosedSubgroupScheme.mk (t.geckRootSubgroup ht i)

/-- The bundled closed root subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_geckRootSubgroupClosedSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    (t.geckRootSubgroupClosedSubgroup ht i).1 =
      letI := t.mono_geckRootSubgroup ht i
      Subobject.mk (t.geckRootSubgroup ht i) := by
  exact ClosedSubgroupScheme.coe_mk _

/-- The bundled numbered root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def geckRootSubgroupClosedSubgroupIso (i : Fin t.rank ⊕ Fin t.rank) :
    ((t.geckRootSubgroupClosedSubgroup ht i).1 :
      Grp (Over (Spec (CommRingCat.of ℤ)))) ≅ AdditiveGroup.groupScheme ℤ :=
  ClosedSubgroupScheme.mkIso (t.geckRootSubgroup ht i)

/-- The canonical parametrization of the bundled closed subgroup followed by its inclusion is the
numbered Geck root-subgroup map. -/
@[simp]
theorem geckRootSubgroupClosedSubgroupIso_inv_comp_arrow (i : Fin t.rank ⊕ Fin t.rank) :
    (t.geckRootSubgroupClosedSubgroupIso ht i).inv ≫
        (t.geckRootSubgroupClosedSubgroup ht i).1.arrow =
      t.geckRootSubgroup ht i :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (t.geckRootSubgroup ht i)

end

end TauCeti.DynkinType
