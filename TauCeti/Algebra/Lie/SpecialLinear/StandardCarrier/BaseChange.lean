/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange

/-!
# Base change of the full-weight type A carrier

The full-weight type `A_r` carrier is constructed over `ℤ` by closing its numbered root
subgroups and weight torus inside `GL_{r+1}`. This file specializes the general base-change
presentation of a toral Kostant closure to that carrier.

For every commutative ring `A`, `TauCeti.SlStd.baseChangeDefiningIdeal` is the transported
integral defining ideal inside `O(GL_{r+1}/A)`. Its quotient is canonically the scalar extension
of the integral carrier coordinate ring. The numbered root-subgroup and weight-torus coordinate
maps base-change with the carrier and factor through that quotient, so the pinning is transported
rather than chosen again after changing the base.

This file does not identify the carrier with `SL_{r+1}` or assert reductivity or maximality of
its torus.

## Main declarations

* `TauCeti.SlStd.baseChangeDefiningIdeal`: the transported defining ideal in
  `O(GL_{r+1}/A)`.
* `TauCeti.SlStd.baseChangeCoordinateIso`: its quotient is the scalar extension of the integral
  carrier coordinate Hopf algebra.
* `TauCeti.SlStd.rootSubgroupToBaseChangeCoordinateMap`: the transported numbered root subgroup
  factored through the base-changed carrier.
* `TauCeti.SlStd.weightTorusToBaseChangeCoordinateMap`: the transported weight torus factored
  through the base-changed carrier.
* `TauCeti.SlStd.baseChangeDefiningIdeal_le_commonKernel`: the transported ideal lies in the
  common kernel of the numbered root-subgroup and weight-torus maps.
## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances the base-change and pinning targets in Layer 9 of the ReductiveGroups roadmap. The
specialized type `A` carrier is consumed by milestone L0, "pinned ambient groups", of the
CFSGStatement roadmap.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.SlStd

universe v

noncomputable section

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (r : ℕ) (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GL_{r+1}/A)` obtained by transporting the defining ideal of the integral
full-weight type `A_r` carrier along `ℤ → A`. -/
noncomputable def baseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (r + 1)) :=
  kostantToralBaseChangePresentationIdeal
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The specialized defining ideal is the general toral Kostant base-change ideal for the
standard type `A_r` representation. -/
@[simp]
theorem baseChangeDefiningIdeal_def :
    baseChangeDefiningIdeal r A =
      kostantToralBaseChangePresentationIdeal
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A := by
  unfold baseChangeDefiningIdeal
  rfl

/-- The coordinate Hopf algebra cut out by the transported type `A_r` defining ideal is
canonically the scalar extension of the integral carrier coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
        (baseChangeDefiningIdeal r A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (kostantToralDefiningIdeal
            (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
            (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
            (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r))) :=
  kostantToralBaseChangePresentationIso
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The type `A_r` base-change coordinate isomorphism is compatible with the quotient
presentation inside `GL_{r+1}`. -/
@[simp]
theorem mkQuotient_comp_baseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
          (baseChangeDefiningIdeal r A) ≫
        (baseChangeCoordinateIso r A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (r + 1)).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
            (kostantToralDefiningIdeal
              (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
              (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
              (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r))) := by
  exact mkQuotient_comp_kostantToralBaseChangePresentationIso_hom
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The base change to `A` of the integral root-subgroup coordinate map at the numbered root
`i`, transported to the coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def rootSubgroupBaseChangeCoordinateMap (i : Fin r ⊕ Fin r) :
    GeneralLinear.coordinateHopfAlgebra A (r + 1) ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupBaseChangePresentationCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) A i

/-- The ambient base-changed root-subgroup map is the specialization of the general transported
Kostant root-subgroup map. -/
theorem rootSubgroupBaseChangeCoordinateMap_def (i : Fin r ⊕ Fin r) :
    rootSubgroupBaseChangeCoordinateMap r A i =
      kostantRootSubgroupBaseChangePresentationCoordinateMap
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) A i := by
  unfold rootSubgroupBaseChangeCoordinateMap
  rfl

/-- The base-changed numbered root-subgroup coordinate map factored through the transported
type `A_r` carrier. -/
noncomputable def rootSubgroupToBaseChangeCoordinateMap (i : Fin r ⊕ Fin r) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
        (baseChangeDefiningIdeal r A) ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A i

/-- The factored type `A_r` root-subgroup map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap (i : Fin r ⊕ Fin r) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
          (baseChangeDefiningIdeal r A) ≫
        rootSubgroupToBaseChangeCoordinateMap r A i =
      rootSubgroupBaseChangeCoordinateMap r A i := by
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A i

/-- The base change to `A` of the integral type `A_r` weight-torus coordinate map, transported to
the coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def weightTorusBaseChangeCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra A (r + 1) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin r))).obj :=
  GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (weight r)

/-- The ambient base-changed weight-torus map is the scalar extension of the integral weight
torus, transported into the coordinate Hopf algebras constructed directly over `A`. -/
theorem weightTorusBaseChangeCoordinateMap_def :
    weightTorusBaseChangeCoordinateMap r A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (weight r) := by
  unfold weightTorusBaseChangeCoordinateMap
  rfl

/-- The underlying bialgebra morphism of the transported type `A_r` weight torus is the direct
diagonal representation over `A` with the standard-module weights. -/
theorem hom_weightTorusBaseChangeCoordinateMap :
    (weightTorusBaseChangeCoordinateMap r A).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := A) (weight r) := by
  rw [weightTorusBaseChangeCoordinateMap_def]
  exact GeneralLinear.hom_weightTorusBaseChangeCoordinateMap ℤ A (weight r)

/-- The base-changed type `A_r` weight-torus coordinate map factored through the transported
carrier. -/
noncomputable def weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
        (baseChangeDefiningIdeal r A) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin r))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The factored type `A_r` weight-torus map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (r + 1))
          (baseChangeDefiningIdeal r A) ≫
        weightTorusToBaseChangeCoordinateMap r A =
      weightTorusBaseChangeCoordinateMap r A := by
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The transported defining ideal lies in the common kernel of the numbered root-subgroup and
weight-torus maps over `A`. -/
theorem baseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin r ⊕ Fin r) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup (Fin r))).obj
    baseChangeDefiningIdeal r A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl i => rootSubgroupBaseChangeCoordinateMap r A i
          | .inr _ => weightTorusBaseChangeCoordinateMap r A) := by
  have h := kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A
  dsimp only at h ⊢
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff] at h ⊢
  rintro (i | _)
  · simpa only [baseChangeDefiningIdeal_def, rootSubgroupBaseChangeCoordinateMap_def] using
      h (.inl i)
  · simpa only [baseChangeDefiningIdeal_def, weightTorusBaseChangeCoordinateMap_def] using
      h (.inr ())

end

end TauCeti.SlStd
