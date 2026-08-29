/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity

/-!
# The pinned graph automorphism of the type-A standard carrier

The signed reverse-inverse-transpose automorphism of `GL_{r+1}` preserves the full-weight
type-`A_r` Chevalley carrier. This file descends it to an automorphism of
`TauCeti.SlStd.groupScheme r`. On the chosen pinning it reverses the Bourbaki numbering without
changing root-subgroup parameters, and on the split torus it reverses the coordinates.

The proof first recovers the ambient coordinate Hopf-algebra automorphism from its natural action
on matrix points. The root subgroups are permuted among themselves and the weight torus is carried
to itself up to relabelling, so the largest Hopf ideal killed by all those coordinate maps is
invariant. The automorphism therefore descends to the quotient.

## Main declarations

* `TauCeti.SlStd.graphRootPerm`: reversal on the positive and negative simple-root indices.
* `TauCeti.SlStd.graphAutomorphism`: the pinned graph automorphism of the standard carrier.
* `TauCeti.SlStd.graphAutomorphismPoints`: its induced automorphism on algebra-valued matrix
  points.
* `TauCeti.SlStd.generalLinearSchemePointsMulEquiv_graphAutomorphism_comp_carrierι`: its signed
  reverse-inverse-transpose formula on arbitrary carrier points.
* `TauCeti.SlStd.graphAutomorphism_hom_comp_self`: its involutivity.
* `TauCeti.SlStd.rootSubgroup_comp_graphAutomorphism_hom`: its action on root subgroups.
* `TauCeti.SlStd.weightTorus_comp_graphAutomorphism_hom`: its action on the split torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.

This advances the Pinnings and Chevalley--Demazure construction targets in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. It supplies the graph part of the Steinberg map needed
by milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md` for the twisted family `²A_r(q)`.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.SlStd

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable (r : ℕ)

/-- Reversal of the Bourbaki node on both the positive and negative simple-root indices. -/
def graphRootPerm : Equiv.Perm (Fin r ⊕ Fin r) :=
  Equiv.sumCongr Fin.revPerm Fin.revPerm

@[simp] theorem graphRootPerm_inl (i : Fin r) : graphRootPerm r (.inl i) = .inl i.rev := by
  simp [graphRootPerm]

@[simp] theorem graphRootPerm_inr (i : Fin r) : graphRootPerm r (.inr i) = .inr i.rev := by
  simp [graphRootPerm]

@[simp] theorem graphRootPerm_graphRootPerm (k : Fin r ⊕ Fin r) :
    graphRootPerm r (graphRootPerm r k) = k := by
  cases k <;> simp [graphRootPerm]

private theorem weight_rev_rev (k : Fin (r + 1)) (i : Fin r) :
    weight r k.rev i.rev = -weight r k i := by
  rw [weight_def, weight_def]
  simp only [← Fin.rev_succ, ← Fin.rev_castSucc, Fin.rev_injective.eq_iff]
  ring

private theorem torusCharacter_weight_rev_reindex {A : Type*} [CommRing A]
    (s : Fin r → Aˣ) (k : Fin (r + 1)) :
    (TauCeti.torusCharacter s (weight r k.rev))⁻¹ =
      TauCeti.torusCharacter s (weight r k ∘ Fin.revPerm) := by
  rw [← TauCeti.torusCharacter_neg]
  congr 1
  funext i
  simpa using (weight_rev_rev r k.rev i).symm

private theorem typeAGraphAutomorphism_kostantRootSubgroupMatrix
    {A : Type*} [CommRing A] (k : Fin r ⊕ Fin r)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    TauCeti.typeAGraphAutomorphism r A
        (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
          (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
          (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
        (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r) q := by
  have hk :=
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_transvectionUnit_of_action
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
      (isNilpotent_rep_rootGenerator r k) (latticeBasis r) (rootSource r k)
      (rootTarget r k) (rootTarget_ne_rootSource r k)
      (nilpotencyClass_rep_rootGenerator r k) (rep_rootGenerator_latticeBasis_apply r k) q
  have hgraph :=
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_transvectionUnit_of_action
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
      (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
      (rootSource r (graphRootPerm r k)) (rootTarget r (graphRootPerm r k))
      (rootTarget_ne_rootSource r (graphRootPerm r k))
      (nilpotencyClass_rep_rootGenerator r (graphRootPerm r k))
      (rep_rootGenerator_latticeBasis_apply r (graphRootPerm r k)) q
  rw [hk, hgraph]
  cases k with
  | inl i =>
      simpa only [graphRootPerm_inl, rootTarget_inl, rootSource_inl] using
        TauCeti.typeAGraphAutomorphism_transvectionUnit r i
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q))
  | inr i =>
      simpa only [graphRootPerm_inr, rootTarget_inr, rootSource_inr] using
        TauCeti.typeAGraphAutomorphism_transvectionUnit_lower r i
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q))

/-- Two coordinate Hopf maps are equal if they agree on the universal point of their target. -/
private theorem hom_eq_of_universalPoint_eq
    {H K : _root_.CommHopfAlgCat.{0} ℤ} (f g : H ⟶ K)
    (h : toConv ((AlgHom.id ℤ K).comp f.hom.toAlgHom) =
      toConv ((AlgHom.id ℤ K).comp g.hom.toAlgHom)) : f = g := by
  apply _root_.CommHopfAlgCat.hom_ext
  ext z
  have hz := congrArg (fun p => p.ofConv z) h
  simp only [AlgHom.id_apply, AlgHom.comp_apply] at hz
  exact hz

/-- Precomposing the universal point agrees with composing its represented coordinate map. -/
private theorem universalPoint_comp
    {H K : _root_.CommHopfAlgCat.{0} ℤ} (c : H ⟶ H) (x : H ⟶ K) :
    toConv ((AlgHom.id ℤ K).comp (c ≫ x).hom.toAlgHom) =
      toConv ((toConv ((AlgHom.id ℤ K).comp x.hom.toAlgHom)).ofConv.comp
        c.hom.toAlgHom) := by
  apply WithConv.ofConv_injective
  ext z
  rfl

/-- Recover an ambient coordinate-map identity from its matrix equality on the universal point. -/
private theorem typeAGraphCoordinateIso_hom_comp_eq_of_universalPoint
    {K : _root_.CommHopfAlgCat.{0} ℤ}
    (x y : GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) ⟶ K)
    (h : TauCeti.typeAGraphAutomorphism r (CommAlgCat.of ℤ K)
        (GeneralLinear.pointToGeneralLinear (r + 1)
          (toConv ((AlgHom.id ℤ K).comp x.hom.toAlgHom))) =
      GeneralLinear.pointToGeneralLinear (r + 1)
        (toConv ((AlgHom.id ℤ K).comp y.hom.toAlgHom))) :
    (GeneralLinear.typeAGraphCoordinateIso r).hom ≫ x = y := by
  apply hom_eq_of_universalPoint_eq
  rw [universalPoint_comp]
  apply (GeneralLinear.pointsMulEquiv
    (R := ℤ) (A := CommAlgCat.of ℤ K) (r + 1)).injective
  rw [GeneralLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso,
    GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointsMulEquiv_apply]
  exact h

private theorem ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap
    (k : Fin r ⊕ Fin r) :
    (GeneralLinear.typeAGraphCoordinateIso r).hom ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
          (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
          (isNilpotent_rep_rootGenerator r k) (latticeBasis r) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
        (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r) := by
  let x := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
  let y := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
    (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
  apply typeAGraphCoordinateIso_hom_comp_eq_of_universalPoint
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  have hx : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (q.ofConv.comp x.hom.toAlgHom)) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
      (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
      (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hy : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (q.ofConv.comp y.hom.toAlgHom)) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
        (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r) q :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
      (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
      (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  rw [hx, hy]
  exact typeAGraphAutomorphism_kostantRootSubgroupMatrix
    (A := CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) r k q

private theorem ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap :
    (GeneralLinear.typeAGraphCoordinateIso r).hom ≫
        GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) =
      GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm := by
  let c := (GeneralLinear.typeAGraphCoordinateIso r).hom
  let x := GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r)
  let y := GeneralLinear.weightTorusCoordinateMap (R := ℤ)
    (fun i => weight r i ∘ Fin.revPerm)
  have hxy : c ≫ x = y := by
    apply typeAGraphCoordinateIso_hom_comp_eq_of_universalPoint
    let T := MonoidAlgebra ℤ (SplitTorus.characterGroup (Fin r))
    let q : WithConv (T →ₐ[ℤ] T) := toConv (AlgHom.id ℤ T)
    have hx : GeneralLinear.pointsMulEquiv (r + 1)
        (toConv (q.ofConv.comp x.hom.toAlgHom)) =
        diagGL fun i => TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q) (weight r i) := by
      calc
        _ = GeneralLinear.pointsMulEquiv (r + 1)
            ((CommHopfAlgCat.mapPointsFunctor x).app (CommAlgCat.of ℤ T) q) := by
          rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
        _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
          (weight r) (CommAlgCat.of ℤ T) q
    have hy : GeneralLinear.pointsMulEquiv (r + 1)
        (toConv (q.ofConv.comp y.hom.toAlgHom)) =
        diagGL fun i => TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q)
          (weight r i ∘ Fin.revPerm) := by
      calc
        _ = GeneralLinear.pointsMulEquiv (r + 1)
            ((CommHopfAlgCat.mapPointsFunctor y).app (CommAlgCat.of ℤ T) q) := by
          rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
        _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
          (fun i => weight r i ∘ Fin.revPerm) (CommAlgCat.of ℤ T) q
    rw [← GeneralLinear.pointsMulEquiv_apply, ← GeneralLinear.pointsMulEquiv_apply,
      hx, hy, TauCeti.typeAGraphAutomorphism_diagGL]
    congr 1
    funext i
    exact torusCharacter_weight_rev_reindex r (SplitTorus.pointsMulEquiv q) i
  calc
    (GeneralLinear.typeAGraphCoordinateIso r).hom ≫
        GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) = y := hxy
    _ = GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm := by
      -- Reindexing the weights is definitionally composition with `Fin.revPerm`; spelling that
      -- family explicitly lets the public coordinate-map reindexing theorem apply.
      change GeneralLinear.weightTorusCoordinateMap (R := ℤ)
          (fun i => weight r i ∘ Fin.revPerm) = _
      have h := GeneralLinear.weightTorusCoordinateMap_reindex
        (R := ℤ) (Fin.revPerm : Equiv.Perm (Fin r)) (weight r)
      have hrev : (Fin.revPerm : Equiv.Perm (Fin r))⁻¹ = Fin.revPerm :=
        Fin.revPerm_symm
      rw [hrev] at h
      exact h

/-! ## Descent to the standard carrier -/

/-- The defining Hopf ideal of the full-weight standard carrier. -/
private noncomputable abbrev definingIdeal :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

/-- The quotient coordinate Hopf algebra underlying the standard carrier. -/
private noncomputable abbrev carrierCoordinateHopfAlgebra :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)

private theorem definingIdeal_comap_ambientGraphCoordinateIso_hom_le :
    (definingIdeal r).comapOfSurjective (GeneralLinear.typeAGraphCoordinateIso r).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.typeAGraphCoordinateIso r).hom).2 ≤
      definingIdeal r := by
  refine kostantToralDefiningIdeal_comapOfSurjective_le_of_comp_eq
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
      (GeneralLinear.typeAGraphCoordinateIso r).hom _ (graphRootPerm r)
      (SplitTorus.relabelCoordinateMap ℤ Fin.revPerm)
      (SplitTorus.relabelCoordinateMap_injective ℤ Fin.revPerm) (fun k => ?_) ?_
  · rw [ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap,
      graphRootPerm_graphRootPerm]
  · exact ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap r

private theorem definingIdeal_comap_ambientGraphCoordinateIso_inv_le :
    (definingIdeal r).comapOfSurjective (GeneralLinear.typeAGraphCoordinateIso r).inv.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.typeAGraphCoordinateIso r).inv).2 ≤
      definingIdeal r := by
  let c := GeneralLinear.typeAGraphCoordinateIso r
  refine kostantToralDefiningIdeal_comapOfSurjective_le_of_comp_eq
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
      c.inv _ (graphRootPerm r) (SplitTorus.relabelCoordinateMap ℤ Fin.revPerm)
      (SplitTorus.relabelCoordinateMap_injective ℤ Fin.revPerm) (fun k => ?_) ?_
  · rw [← ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap r k,
      Iso.inv_hom_id_assoc]
  · rw [← cancel_epi c.hom]
    simp only [← Category.assoc, c.hom_inv_id, Category.id_comp]
    rw [ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap, Category.assoc,
      SplitTorus.relabelCoordinateMap_comp]
    have hrev : (Fin.revPerm : Equiv.Perm (Fin r)) * Fin.revPerm = 1 := by
      ext i
      simp
    rw [hrev, SplitTorus.relabelCoordinateMap_one, Category.comp_id]

private theorem definingIdeal_comap_ambientGraphCoordinateIso :
    (definingIdeal r).comapOfSurjective (GeneralLinear.typeAGraphCoordinateIso r).hom.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.typeAGraphCoordinateIso r).hom).2 =
      definingIdeal r := by
  exact HopfIdeal.comapOfSurjective_eq_of_hom_le_of_inv_le
    (GeneralLinear.typeAGraphCoordinateIso r) (definingIdeal r)
    (definingIdeal_comap_ambientGraphCoordinateIso_hom_le r)
    (definingIdeal_comap_ambientGraphCoordinateIso_inv_le r)

/-- The graph automorphism induced on the standard carrier's quotient coordinate algebra. -/
private noncomputable def graphCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r) ≅
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r) :=
  CommHopfAlgCat.quotientIsoOfComapEq (GeneralLinear.typeAGraphCoordinateIso r) (definingIdeal r)
    (definingIdeal_comap_ambientGraphCoordinateIso r)

private theorem mkQuotient_comp_graphCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r) ≫
        (graphCoordinateIso r).hom =
      (GeneralLinear.typeAGraphCoordinateIso r).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r) := by
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom
    (GeneralLinear.typeAGraphCoordinateIso r) (definingIdeal r)
    (definingIdeal_comap_ambientGraphCoordinateIso r)

private theorem graphCoordinateIso_hom_comp_rootMap (k : Fin r ⊕ Fin r) :
    (graphCoordinateIso r).hom ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
          (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (graphRootPerm r k) := by
  let J := definingIdeal r
  let y := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
    (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
  have hy : J.toIdeal ≤ RingHom.ker y.hom.toAlgHom.toRingHom :=
    TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_toIdeal_le_root_ker
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (graphRootPerm r k)
  have hleft := CommHopfAlgCat.liftQuotient_unique J y hy
    ((graphCoordinateIso r).hom ≫
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) k) (by
      rw [← Category.assoc, mkQuotient_comp_graphCoordinateIso_hom, Category.assoc,
        TauCeti.UniversalEnvelopingAlgebra.mkQuotient_comp_kostantRootSubgroupToralCoordinateMap,
        ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap])
  have hright := CommHopfAlgCat.liftQuotient_unique J y hy
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (graphRootPerm r k))
    (TauCeti.UniversalEnvelopingAlgebra.mkQuotient_comp_kostantRootSubgroupToralCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (graphRootPerm r k))
  exact hleft.trans hright.symm

private theorem graphCoordinateIso_hom_comp_torusMap :
    (graphCoordinateIso r).hom ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToralCoordinateMap
          (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToralCoordinateMap
          (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm := by
  let J := definingIdeal r
  let y := GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
    SplitTorus.relabelCoordinateMap ℤ Fin.revPerm
  have hy : J.toIdeal ≤ RingHom.ker y.hom.toAlgHom.toRingHom := by
    intro z hz
    have hzero : (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r)).hom z = 0 := by
      simpa using RingHom.mem_ker.mp
        (TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_toIdeal_le_torus_ker
          (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) hz)
    rw [RingHom.mem_ker]
    -- The composite Hopf morphism acts by the underlying composed bialgebra homomorphism.
    change (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
      SplitTorus.relabelCoordinateMap ℤ Fin.revPerm).hom z = 0
    rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, hzero, map_zero]
  have hleft := CommHopfAlgCat.liftQuotient_unique J y hy
    ((graphCoordinateIso r).hom ≫
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToralCoordinateMap
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)) (by
      rw [← Category.assoc, mkQuotient_comp_graphCoordinateIso_hom, Category.assoc,
        TauCeti.UniversalEnvelopingAlgebra.mkQuotient_comp_kostantWeightTorusToralCoordinateMap,
        ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap])
  have hright := CommHopfAlgCat.liftQuotient_unique J y hy
    (TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToralCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm) (by
      rw [← Category.assoc,
        TauCeti.UniversalEnvelopingAlgebra.mkQuotient_comp_kostantWeightTorusToralCoordinateMap])
  exact hleft.trans hright.symm

/-- **The pinned graph automorphism of the full-weight type-`A_r` standard carrier.** -/
noncomputable def graphAutomorphism : Aut (groupScheme r) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).mapIso (graphCoordinateIso r).op

/-- The standard carrier is represented by its quotient coordinate Hopf algebra. -/
private theorem groupScheme_eq_hopfSpec :
    groupScheme r =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
        (Opposite.op (carrierCoordinateHopfAlgebra r)) := rfl

/-- Algebra-valued points of the carrier, transported to scheme-valued points. -/
private noncomputable def groupSchemePointMulEquiv (A : Type) [CommRing A] :
    WithConv (carrierCoordinateHopfAlgebra r →ₐ[ℤ] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ (groupScheme r).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation (carrierCoordinateHopfAlgebra r) A
    (groupScheme_eq_hopfSpec r)

private theorem groupSchemePointMulEquiv_apply_left {A : Type} [CommRing A]
    (q : WithConv (carrierCoordinateHopfAlgebra r →ₐ[ℤ] A)) :
    (groupSchemePointMulEquiv r A q).left =
      Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
        eqToHom (congrArg
          (fun K : Grp (Over (Spec (CommRingCat.of ℤ))) => K.X.left)
          (groupScheme_eq_hopfSpec r)).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (carrierCoordinateHopfAlgebra r) A (groupScheme_eq_hopfSpec r)
      (congrArg (fun K : Grp (Over (Spec (CommRingCat.of ℤ))) => K.X.left)
        (groupScheme_eq_hopfSpec r)) q

private theorem groupSchemePointMulEquiv_comp_graphAutomorphism
    {A : Type} [CommRing A]
    (q : WithConv (carrierCoordinateHopfAlgebra r →ₐ[ℤ] A)) :
    groupSchemePointMulEquiv r A q ≫ (graphAutomorphism r).hom.hom.hom =
      groupSchemePointMulEquiv r A
        ((CommHopfAlgCat.mapPointsFunctor (graphCoordinateIso r).hom).app
          (CommAlgCat.of ℤ A) q) := by
  rw [graphAutomorphism, Functor.mapIso_hom, Iso.op_hom]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ℤ) A (groupScheme_eq_hopfSpec r) (groupScheme_eq_hopfSpec r)
      (groupSchemePointMulEquiv r A) (groupSchemePointMulEquiv r A)
      (groupSchemePointMulEquiv_apply_left r) (groupSchemePointMulEquiv_apply_left r)
      (graphCoordinateIso r).hom q

private theorem groupSchemePointMulEquiv_comp_carrierι
    {A : Type} [CommRing A]
    (q : WithConv (carrierCoordinateHopfAlgebra r →ₐ[ℤ] A)) :
    groupSchemePointMulEquiv r A q ≫ (carrierι r).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv (r + 1) A
        ((CommHopfAlgCat.mapPointsFunctor
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
            (definingIdeal r))).app (CommAlgCat.of ℤ A) q) := by
  rw [carrierι_def, kostantToralGroupSchemeι_def, CommHopfAlgCat.quotientSpecι_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ℤ) A (GeneralLinear.groupScheme_def ℤ (r + 1)) rfl
      (GeneralLinear.groupSchemePointMulEquiv (r + 1) A) (groupSchemePointMulEquiv r A)
      (GeneralLinear.groupSchemePointMulEquiv_apply_left (r + 1) A)
      (groupSchemePointMulEquiv_apply_left r)
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r)) q

/-- On every algebra-valued carrier point, the graph automorphism is signed
reverse-inverse-transpose after the canonical inclusion into `GL_{r+1}`. -/
theorem generalLinearSchemePointsMulEquiv_graphAutomorphism_comp_carrierι
    {A : Type} [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ (groupScheme r).X) :
    GeneralLinear.schemePointsMulEquiv (r + 1) A
        (p ≫ (graphAutomorphism r).hom.hom.hom ≫ (carrierι r).hom.hom) =
      TauCeti.typeAGraphAutomorphism r A
        (GeneralLinear.schemePointsMulEquiv (r + 1) A (p ≫ (carrierι r).hom.hom)) := by
  obtain ⟨q, rfl⟩ := (groupSchemePointMulEquiv r A).surjective p
  have hgraph := groupSchemePointMulEquiv_comp_graphAutomorphism r q
  have hinclusion := groupSchemePointMulEquiv_comp_carrierι r q
  have hgraphCarrier := congrArg (fun f => f ≫ (carrierι r).hom.hom) hgraph
  have hinclusionGraph := groupSchemePointMulEquiv_comp_carrierι (A := A) r
    ((CommHopfAlgCat.mapPointsFunctor (graphCoordinateIso r).hom).app (CommAlgCat.of ℤ A) q)
  rw [← Category.assoc, hgraphCarrier, hinclusionGraph,
    CommHopfAlgCat.mapPointsFunctor_app_apply, CommHopfAlgCat.mapPointsFunctor_app_apply,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    hinclusion, CommHopfAlgCat.mapPointsFunctor_app_apply,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    WithConv.ofConv_toConv]
  let qambient : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (CommAlgCat.of ℤ A) :=
    toConv (q.ofConv.comp
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r)).hom.toAlgHom)
  have hpoint :
      toConv ((q.ofConv.comp (graphCoordinateIso r).hom.hom.toAlgHom).comp
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r)).hom.toAlgHom) =
        toConv (qambient.ofConv.comp
          (GeneralLinear.typeAGraphCoordinateIso r).hom.hom.toAlgHom) := by
    apply WithConv.ofConv_injective
    ext z
    have hz := congrArg (fun f => q.ofConv (f.hom z))
      (mkQuotient_comp_graphCoordinateIso_hom r)
    exact hz
  rw [hpoint]
  exact GeneralLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso r
    (CommAlgCat.of ℤ A) qambient

/-- Signed reverse-inverse-transpose preserves the matrix points of the standard carrier. -/
theorem typeAGraphAutomorphism_mem_points {A : Type} [CommRing A]
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) (hg : g ∈ points r A) :
    TauCeti.typeAGraphAutomorphism r A g ∈ points r A := by
  rw [mem_points_iff] at hg ⊢
  intro x hx
  let q : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (CommAlgCat.of ℤ A) :=
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := CommAlgCat.of ℤ A) (r + 1)).symm g
  have hpoint :
      (GeneralLinear.pointsMulEquiv (R := ℤ) (A := CommAlgCat.of ℤ A) (r + 1)).symm
          (TauCeti.typeAGraphAutomorphism r A g) =
        toConv (q.ofConv.comp
          (GeneralLinear.typeAGraphCoordinateIso r).hom.hom.toAlgHom) := by
    apply (GeneralLinear.pointsMulEquiv
      (R := ℤ) (A := CommAlgCat.of ℤ A) (r + 1)).injective
    rw [MulEquiv.apply_symm_apply,
      GeneralLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso]
    exact congrArg (TauCeti.typeAGraphAutomorphism r A)
      ((GeneralLinear.pointsMulEquiv
        (R := ℤ) (A := CommAlgCat.of ℤ A) (r + 1)).apply_symm_apply g).symm
  rw [hpoint]
  -- `mem_points_iff` evaluates the represented point as an algebra hom, whereas `hpoint`
  -- retains the `WithConv` and bialgebra-hom wrappers around that same evaluation.
  change q.ofConv ((GeneralLinear.typeAGraphCoordinateIso r).hom.hom x) = 0
  apply hg
  apply HopfIdeal.mem_comapOfSurjective.mp
  rw [definingIdeal_comap_ambientGraphCoordinateIso]
  exact hx

/-- **The pinned graph automorphism on algebra-valued points of the standard carrier.** -/
noncomputable def graphAutomorphismPoints (A : Type) [CommRing A] :
    points r A ≃* points r A where
  toFun g := ⟨TauCeti.typeAGraphAutomorphism r A
      (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A),
    typeAGraphAutomorphism_mem_points (A := A) r
      (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) g.property⟩
  invFun g := ⟨TauCeti.typeAGraphAutomorphism r A
      (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A),
    typeAGraphAutomorphism_mem_points (A := A) r
      (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) g.property⟩
  left_inv g := Subtype.ext (TauCeti.typeAGraphAutomorphism_typeAGraphAutomorphism r
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A))
  right_inv g := Subtype.ext (TauCeti.typeAGraphAutomorphism_typeAGraphAutomorphism r
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A))
  map_mul' g h := Subtype.ext (map_mul (TauCeti.typeAGraphAutomorphism r A)
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A)
    (h : Matrix.GeneralLinearGroup (Fin (r + 1)) A))

/-- The point-group graph automorphism is signed reverse-inverse-transpose on matrices. -/
@[simp]
theorem coe_graphAutomorphismPoints {A : Type} [CommRing A] (g : points r A) :
    (graphAutomorphismPoints r A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      TauCeti.typeAGraphAutomorphism r A g := by
  unfold graphAutomorphismPoints
  rfl

/-- The point-group graph automorphism reverses the numbered root subgroups. -/
@[simp]
theorem graphAutomorphismPoints_rootSubgroupPoints {A : Type} [CommRing A]
    (i : Fin r ⊕ Fin r) (u : Multiplicative A) :
    graphAutomorphismPoints r A (rootSubgroupPoints r i A u) =
      rootSubgroupPoints r (graphRootPerm r i) A u := by
  apply Subtype.ext
  rw [coe_graphAutomorphismPoints, coe_rootSubgroupPoints, coe_rootSubgroupPoints]
  exact typeAGraphAutomorphism_kostantRootSubgroupMatrix r i
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

/-- The point-group graph automorphism reverses the coordinates of the split weight torus. -/
@[simp]
theorem graphAutomorphismPoints_weightTorusPoints {A : Type} [CommRing A]
    (s : Fin r → Aˣ) :
    graphAutomorphismPoints r A (weightTorusPoints r A s) =
      weightTorusPoints r A (fun i => s i.rev) := by
  apply Subtype.ext
  rw [coe_graphAutomorphismPoints, coe_weightTorusPoints, coe_weightTorusPoints,
    TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    TauCeti.typeAGraphAutomorphism_diagGL]
  congr 1
  funext i
  rw [torusCharacter_weight_rev_reindex]
  have hs : (MulEquiv.arrowCongr Fin.revPerm (MulEquiv.refl Aˣ)) s =
      (fun j => s j.rev) := by
    funext j
    simp only [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, Fin.revPerm_symm,
      Fin.revPerm_apply]
  rw [← hs]
  exact (TauCeti.torusCharacter_mulEquivArrowCongr
    (Fin.revPerm : Equiv.Perm (Fin r)) s (weight r i)).symm

/-- The graph automorphism reverses the Bourbaki numbering of every positive and negative simple
root subgroup, without changing its additive parameter. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_graphAutomorphism_hom (k : Fin r ⊕ Fin r) :
    rootSubgroup r k ≫ (graphAutomorphism r).hom =
      rootSubgroup r (graphRootPerm r k) := by
  rw [rootSubgroup_def, kostantRootSubgroupToToral_def, graphAutomorphism,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    ← Functor.map_comp, ← op_comp, graphCoordinateIso_hom_comp_rootMap]
  rw [rootSubgroup_def]
  exact (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_def
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
    (graphRootPerm r k)).symm

/-- The graph automorphism normalizes the split torus and reverses its Bourbaki-numbered
coordinates. -/
@[reassoc (attr := simp)]
theorem weightTorus_comp_graphAutomorphism_hom :
    weightTorus r ≫ (graphAutomorphism r).hom =
      SplitTorus.relabel ℤ Fin.revPerm ≫ weightTorus r := by
  rw [weightTorus_def, kostantWeightTorusToToral_def, graphAutomorphism,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    ← Functor.map_comp, ← op_comp, graphCoordinateIso_hom_comp_torusMap, op_comp,
    Functor.map_comp, SplitTorus.relabel_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Applying the graph automorphism twice is the identity on the standard carrier. -/
@[reassoc (attr := simp)]
theorem graphAutomorphism_hom_comp_self :
    (graphAutomorphism r).hom ≫ (graphAutomorphism r).hom = 𝟙 (groupScheme r) := by
  apply TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
  · intro k
    rw [← rootSubgroup_def]
    have h₁ := rootSubgroup_comp_graphAutomorphism_hom r k
    have h₂ := rootSubgroup_comp_graphAutomorphism_hom r (graphRootPerm r k)
    calc
      rootSubgroup r k ≫ ((graphAutomorphism r).hom ≫ (graphAutomorphism r).hom) =
          (rootSubgroup r k ≫ (graphAutomorphism r).hom) ≫
            (graphAutomorphism r).hom := (Category.assoc _ _ _).symm
      _ = rootSubgroup r (graphRootPerm r k) ≫ (graphAutomorphism r).hom := by rw [h₁]
      _ = rootSubgroup r (graphRootPerm r (graphRootPerm r k)) := h₂
      _ = rootSubgroup r k := by rw [graphRootPerm_graphRootPerm]
      _ = rootSubgroup r k ≫ 𝟙 (groupScheme r) := (Category.comp_id _).symm
  · rw [← weightTorus_def]
    have htorus := weightTorus_comp_graphAutomorphism_hom r
    calc
      weightTorus r ≫ ((graphAutomorphism r).hom ≫ (graphAutomorphism r).hom) =
          (weightTorus r ≫ (graphAutomorphism r).hom) ≫
            (graphAutomorphism r).hom := (Category.assoc _ _ _).symm
      _ = (SplitTorus.relabel ℤ Fin.revPerm ≫ weightTorus r) ≫
          (graphAutomorphism r).hom := by rw [htorus]
      _ = SplitTorus.relabel ℤ Fin.revPerm ≫
          (weightTorus r ≫ (graphAutomorphism r).hom) := Category.assoc _ _ _
      _ = SplitTorus.relabel ℤ Fin.revPerm ≫
          (SplitTorus.relabel ℤ Fin.revPerm ≫ weightTorus r) := by rw [htorus]
      _ = (SplitTorus.relabel ℤ Fin.revPerm ≫ SplitTorus.relabel ℤ Fin.revPerm) ≫
          weightTorus r := (Category.assoc _ _ _).symm
      _ = SplitTorus.relabel ℤ
            ((Fin.revPerm : Equiv.Perm (Fin r)) * Fin.revPerm) ≫ weightTorus r := by
        rw [SplitTorus.relabel_comp]
      _ = weightTorus r := by
        have hrev : (Fin.revPerm : Equiv.Perm (Fin r)) * Fin.revPerm = 1 := by
          ext i
          simp
        rw [hrev, SplitTorus.relabel_one, Category.id_comp]
      _ = weightTorus r ≫ 𝟙 (groupScheme r) := (Category.comp_id _).symm

/-- The inverse leg of the graph automorphism is its forward leg. -/
@[simp]
theorem graphAutomorphism_inv : (graphAutomorphism r).inv = (graphAutomorphism r).hom := by
  calc
    (graphAutomorphism r).inv = 𝟙 (groupScheme r) ≫ (graphAutomorphism r).inv :=
      (Category.id_comp _).symm
    _ = ((graphAutomorphism r).hom ≫ (graphAutomorphism r).hom) ≫
        (graphAutomorphism r).inv := by rw [graphAutomorphism_hom_comp_self]
    _ = (graphAutomorphism r).hom ≫
        ((graphAutomorphism r).hom ≫ (graphAutomorphism r).inv) := Category.assoc _ _ _
    _ = (graphAutomorphism r).hom := by
      rw [(graphAutomorphism r).hom_inv_id, Category.comp_id]

end TauCeti.SlStd
