/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.NormalInvariants
import TauCeti.Algebra.AlgebraicGroup.Unipotent.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Normal unipotent subgroups of linearly reductive affine groups

Let `H` be a reduced, finite-type coordinate Hopf algebra of an affine group over an
algebraically closed field `k`, and let `I` be a normal Hopf ideal cutting out a closed subgroup
`N` whose coordinate ring is reduced, of finite type, and has only unipotent points. If `H` is
linearly reductive then `N` is the identity subgroup, that is, `I` is the augmentation ideal.

The argument is the standard one. Fix a finite-dimensional representation `V` of the ambient
group. Its `N`-invariants are stable under the ambient group because `I` is normal, and geometric
point separation promotes that stable subspace to a subcomodule of `V`. Complete reducibility
supplies an ambient complement, which then contains no nonzero `N`-fixed vector; Kolchin's
theorem, already available for unipotent groups, forces such a complement to vanish. So `N` acts
trivially on every finite-dimensional representation of the ambient group. Applying this to the
finite-dimensional subcomodules of the regular representation, which exhaust `H`, shows that the
quotient morphism `H ⟶ H ⧸ I` sends `h` to `ε h • 1`, hence that `I` is the kernel of the counit.

The whole-group case — a linearly reductive unipotent group is trivial — is
`TauCeti.HopfAlgebra.counitBialgEquivOfIsLinearlyReductiveOfForallIsUnipotentPoint`, and it does
not suffice here: a closed subgroup of a linearly reductive group is not visibly linearly
reductive. Complete reducibility is therefore used on representations of the ambient group, and
normality is what makes the invariants of the subgroup an ambient subrepresentation.

For the object properties this gives one half of the Layer 6 comparison: a smooth, geometrically
connected finite-type affine group whose geometric fibre is linearly reductive is reductive. The
converse implication in characteristic zero is a separate development.

## Main declarations

* `mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible`:
  over an algebraically closed field, a normal unipotent closed subgroup of a reduced finite-type
  affine group acts trivially on every completely reducible finite-dimensional representation.
* `mkQuotient_eq_counit_smul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive`:
  under the same hypotheses, the quotient morphism of a linearly reductive group is
  `h ↦ ε h • 1`.
* `eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive`:
  **such a normal unipotent closed subgroup is trivial.**
* `quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive`:
  the same conclusion as a bialgebra equivalence between the subgroup's coordinate ring and the
  ground field.
* `of_smooth_of_geometricallyConnected_of_baseChange_linearlyReductive`:
  a smooth, geometrically connected finite-type affine group with linearly reductive geometric
  fibre is reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.45 and §22.42.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2 and §8.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This advances the Layer 6 milestone "Reductive and semisimple groups" of the ReductiveGroups
roadmap, whose instruction is to "provide both definitions and the char-0 equivalence so
downstream work can pick either": this is the implication from linear reductivity to reductivity,
and it holds in every characteristic.
-/

public section

open scoped TensorProduct

namespace TauCeti

open CategoryTheory WithConv

universe u v w

noncomputable section

namespace HopfIdeal

variable {k : Type u} {H : Type v}
variable [Field k] [CommRing H] [HopfAlgebra k H]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

section NormalUnipotent

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
variable {I : HopfIdeal k H}
variable [Algebra.FiniteType k (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)]
variable [IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)]
variable (hI : I.IsNormal)
variable (hu : ∀ g : WithConv
    (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k),
  HopfAlgebra.IsUnipotentPoint g)

section Comodule

variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]

include hI hu in
/-- Over an algebraically closed field, a normal closed subgroup whose coordinate ring is
reduced, of finite type and has only unipotent points acts trivially on every completely reducible
finite-dimensional representation of an ambient affine group with reduced, finite-type
coordinate ring.

Normality makes the subgroup's fixed subspace an ambient subcomodule, complete reducibility
supplies an ambient complement, and Kolchin's theorem finds a nonzero fixed vector inside a
nonzero complement. -/
theorem mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
    (hcr : Comodule.IsCompletelyReducible k H M) (m : M) :
    TensorProduct.map LinearMap.id
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
        (Comodule.coact (R := k) (C := H) m) =
      m ⊗ₜ[k] (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) := by
  let A := _root_.CommHopfAlgCat.of k H
  let Q := CommHopfAlgCat.quotient A I
  let q : H →ₐc[k] Q := (CommHopfAlgCat.mkQuotient A I).hom
  let _ : Comodule k Q M := Comodule.Corestrict q.toCoalgHom
  have hstable : ∀ (g : H →ₐ[k] k) {x : M}, x ∈ I.basePointFixedSubmodule M →
      Comodule.endOfPoint M g (1 ⊗ₜ[k] x) ∈ (I.basePointFixedSubmodule M).baseChange k := by
    intro g x hx
    simpa only [WithConv.ofConv_toConv] using
      hI.endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange (toConv g) hx
  let F : Subcomodule k H M :=
    Subcomodule.ofEndOfPointStable (K := k) (I.basePointFixedSubmodule M) hstable
  have hFsub : F.toSubmodule = I.basePointFixedSubmodule M :=
    Subcomodule.ofEndOfPointStable_toSubmodule _ hstable
  have hFtop : F = ⊤ := by
    obtain ⟨P, hP⟩ := hcr.exists_isCompl F
    have hPbot : P = ⊥ := by
      by_contra hne
      obtain ⟨w, hwP, hw0⟩ := Subcomodule.ne_bot_iff.mp hne
      have hne' : Subcomodule.corestrict q.toCoalgHom P ≠ ⊥ :=
        Subcomodule.ne_bot_iff.mpr
          ⟨w, (Subcomodule.mem_corestrict q.toCoalgHom P w).mpr hwP, hw0⟩
      obtain ⟨v, hvP, hv0, hvfix⟩ :=
        Comodule.exists_mem_ne_zero_coact_eq_tmul_one_of_forall_isUnipotentPoint
          (H := Q) hu (Subcomodule.corestrict q.toCoalgHom P) hne'
      have hvF : v ∈ I.basePointFixedSubmodule M :=
        mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one I v
          (by simpa only [Comodule.corestrict_coact_apply] using hvfix)
      have hmem : v ∈ F.toSubmodule ⊓ P.toSubmodule :=
        ⟨hFsub ▸ hvF, (Subcomodule.mem_corestrict q.toCoalgHom P v).mp hvP⟩
      rw [hP.inf_eq_bot, Submodule.mem_bot] at hmem
      exact hv0 hmem
    have hsup := hP.sup_eq_top
    rw [hPbot, Subcomodule.bot_toSubmodule, sup_bot_eq] at hsup
    exact Subcomodule.toSubmodule_eq_top.mp hsup
  have hm : m ∈ I.basePointFixedSubmodule M := by
    rw [← hFsub, hFtop, Subcomodule.top_toSubmodule]
    exact Submodule.mem_top
  exact (mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one I m).mp hm

end Comodule

variable (hlr : Coalgebra.IsLinearlyReductive.{u, v, u} k H)

include hI hu hlr in
/-- Over an algebraically closed field, the regular representation of a linearly reductive,
reduced finite-type affine group is fixed by a normal unipotent closed subgroup: comultiplication
followed by the quotient morphism in the second factor sends `h` to `h ⊗ 1`.

Every element lies in a finite-dimensional subcoalgebra, hence in a finite-dimensional
subcomodule of the regular comodule, where the previous theorem applies. -/
theorem mkQuotient_comul_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
    (h : H) :
    TensorProduct.map LinearMap.id
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
        (Coalgebra.comul (R := k) h) =
      h ⊗ₜ[k] (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) := by
  obtain ⟨D, hDfin, hD⟩ := Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem (k := k) h
  set N : Subcomodule k H H := D.toRegularSubcomodule with hNdef
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have hNfin : FiniteDimensional k N.toSubmodule := by
    rw [hNdef, Subcoalgebra.toRegularSubcomodule_toSubmodule]
    exact hDfin
  -- `↥N` and `↥N.toSubmodule` subtype the same carrier, so finite-dimensionality transfers.
  have _ : FiniteDimensional k N := hNfin
  have hmem : h ∈ N := Subcoalgebra.mem_toRegularSubcomodule.mpr hD
  have hfix :=
    mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
      (M := N) hI hu hlr.isCompletelyReducible ⟨h, hmem⟩
  have hpush := Subcomodule.map_id_coact_coe_eq_tmul_one
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom.toCoalgHom N hfix
  rwa [Comodule.instSelf_coact] at hpush

include hI hu hlr in
/-- Over an algebraically closed field, the quotient morphism of a linearly reductive, reduced
finite-type affine group by a normal unipotent closed subgroup is `h ↦ ε h • 1`.

Contracting the previous identity against the counit in the first factor removes
comultiplication. -/
theorem mkQuotient_eq_counit_smul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
    (h : H) :
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom h =
      Coalgebra.counit (R := k) h •
        (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) := by
  have hcomul :=
    mkQuotient_comul_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
      hI hu hlr h
  have hcounit :
      ((TensorProduct.lid k
          (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)).toLinearMap ∘ₗ
        TensorProduct.map (Coalgebra.counit (R := k) (A := H))
          (CommHopfAlgCat.mkQuotient
            (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap) ∘ₗ
        Coalgebra.comul (R := k) (A := H) =
      (CommHopfAlgCat.mkQuotient
        (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap := by
    rw [LinearMap.comp_assoc, CoassocSimps.map_counit_comp_comul_left,
      ← LinearMap.comp_assoc, CoassocSimps.lid_comp_map]
    ext x
    simp
  have hcounit_h := LinearMap.congr_fun hcounit h
  simp only [LinearMap.comp_apply] at hcounit_h
  have hfactor :
      LinearMap.rTensor (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)
          (Coalgebra.counit (R := k) (A := H))
          (TensorProduct.map LinearMap.id
            (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
            (Coalgebra.comul (R := k) h)) =
        TensorProduct.map (Coalgebra.counit (R := k) (A := H))
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
          (Coalgebra.comul (R := k) h) := by
    rw [LinearMap.rTensor_def, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id]
  calc
    _ = TensorProduct.lid k
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)
        (TensorProduct.map (Coalgebra.counit (R := k) (A := H))
          (CommHopfAlgCat.mkQuotient
            (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
          (Coalgebra.comul (R := k) h)) := hcounit_h.symm
    _ = TensorProduct.lid k
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)
        (LinearMap.rTensor _ (Coalgebra.counit (R := k) (A := H))
          (TensorProduct.map LinearMap.id
            (CommHopfAlgCat.mkQuotient
              (_root_.CommHopfAlgCat.of k H) I).hom.toLinearMap
            (Coalgebra.comul (R := k) h))) := congrArg _ hfactor.symm
    _ = TensorProduct.lid k
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)
        (LinearMap.rTensor _ (Coalgebra.counit (R := k) (A := H)) (h ⊗ₜ[k] 1)) :=
      congrArg (fun t : H ⊗[k]
        CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I ↦
          TensorProduct.lid k
            (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)
            (LinearMap.rTensor _ (Coalgebra.counit (R := k) (A := H)) t)) hcomul
    _ = _ := by simp

include hI hu hlr in
/-- **Over an algebraically closed field, a linearly reductive affine group with reduced,
finite-type coordinate ring has no nontrivial normal unipotent closed subgroup.**

A normal Hopf ideal whose quotient coordinate ring is reduced, of finite type and has only
unipotent points is the augmentation ideal; contravariantly, the closed subgroup it cuts out is
the identity subgroup. Connectedness of the subgroup is not needed. -/
theorem eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive :
    I = augmentation k H := by
  refine HopfIdeal.ext fun x ↦ ?_
  rw [mem_augmentation]
  refine ⟨fun hx ↦ I.counit_eq_zero hx, fun hx ↦ ?_⟩
  have hq :=
    mkQuotient_eq_counit_smul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
      hI hu hlr x
  rw [hx, zero_smul] at hq
  exact mem_toIdeal.mp
    ((CommHopfAlgCat.mkQuotient_eq_zero_iff (_root_.CommHopfAlgCat.of k H) I x).mp hq)

include hI hu hlr in
/-- Over an algebraically closed field, the coordinate Hopf algebra of a normal unipotent closed
subgroup of a linearly reductive affine group with reduced, finite-type coordinate ring has zero
augmentation ideal. -/
theorem quotient_augmentation_eq_bot_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive :
    augmentation k (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) = ⊥ := by
  refine HopfIdeal.ext fun y ↦ ?_
  rw [mem_augmentation, mem_bot]
  refine ⟨fun hy ↦ ?_, fun hy ↦ by rw [hy, map_zero]⟩
  obtain ⟨x, rfl⟩ :=
    CommHopfAlgCat.mkQuotient_surjective (_root_.CommHopfAlgCat.of k H) I y
  rw [CoalgHomClass.counit_comp_apply] at hy
  rw [mkQuotient_eq_counit_smul_one_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
    hI hu hlr x, hy, zero_smul]

include hI hu hlr in
/-- **Over an algebraically closed field, a normal unipotent closed subgroup of a linearly
reductive affine group with reduced, finite-type coordinate ring is trivial**: its coordinate
Hopf algebra is bialgebra-equivalent to the ground field via the counit. -/
def quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive :
    CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I ≃ₐc[k] k :=
  counitBialgEquivOfAugmentationEqBot
    (quotient_augmentation_eq_bot_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
      hI hu hlr)

include hI hu hlr in
/-- The triviality equivalence of a normal unipotent closed subgroup is its counit. -/
@[simp]
theorem quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive_apply
    (y : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) :
    quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive hI hu hlr y =
      Bialgebra.counitBialgHom k
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) y := by
  rw [quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive]
  exact counitBialgEquivOfAugmentationEqBot_apply _ _

include hI hu hlr in
/-- The inverse of the triviality equivalence is the structure map. -/
@[simp]
theorem quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive_symm_apply
    (r : k) :
    (quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive hI hu hlr).symm
        r =
      algebraMap k (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I) r := by
  rw [quotientCounitBialgEquivOfIsNormalOfForallIsUnipotentPointOfIsLinearlyReductive]
  exact counitBialgEquivOfAugmentationEqBot_symm_apply _ _

end NormalUnipotent

end HopfIdeal

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A smooth, geometrically connected finite-type affine group whose geometric fibre is
linearly reductive is reductive.**

This is the implication from linear reductivity to reductivity in Layer 6 of the ReductiveGroups
roadmap. Linear reductivity is asked of the geometric fibre because reductivity is defined after
extension to an algebraic closure. -/
theorem of_smooth_of_geometricallyConnected_of_baseChange_linearlyReductive
    (hsm : Algebra.Smooth k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H.obj)
    (hlr : linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj) :
    reductiveCommHopfAlgProperty k H := by
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨hsm, hconn, ?_⟩
  intro I hnormal _ hunipotent
  rw [smoothUnipotentCommHopfAlgProperty_iff] at hunipotent
  let _ : Algebra.Smooth (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
    @Algebra.Smooth.baseChange k _ H (AlgebraicClosure k) _ _ _ _ hsm
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
    isReduced_of_smooth_of_field (AlgebraicClosure k) _
  let _ := hunipotent.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) :=
    isReduced_of_smooth_of_field (AlgebraicClosure k) _
  exact HopfIdeal.eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
    hnormal
    (geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mpr hunipotent.2))
    ((linearlyReductiveCommHopfAlgProperty_iff _ _).mp hlr)

end reductiveCommHopfAlgProperty

end

end TauCeti
