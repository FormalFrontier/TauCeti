/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

/-!
# The pinned graph automorphism of the type-A standard carrier

The signed reverse-inverse-transpose automorphism of `GL_{r+1}` preserves the full-weight
type-`A_r` Chevalley carrier. This file descends it to an automorphism of
`TauCeti.SlStd.groupScheme r`. On the chosen pinning it reverses the Bourbaki numbering without
changing root-subgroup parameters, and on the split torus it reverses the coordinates.

The proof first recovers the ambient coordinate Hopf-algebra automorphism from its natural action
on matrix points. The positive and negative transvection formulas and the diagonal formula then
show that it preserves every generator of the carrier's defining ideal. Passing to the quotient
gives the desired group-scheme automorphism.

## Main declarations

* `TauCeti.SlStd.graphRootPerm`: reversal on the positive and negative simple-root indices.
* `TauCeti.SlStd.graphAutomorphism`: the pinned graph automorphism of the standard carrier.
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

@[simp] theorem graphRootPerm_apply_apply (k : Fin r ⊕ Fin r) :
    graphRootPerm r (graphRootPerm r k) = k := by
  cases k <;> simp [graphRootPerm]

private theorem weight_rev_rev (k : Fin (r + 1)) (i : Fin r) :
    weight r k.rev i.rev = -weight r k i := by
  rw [weight_apply, weight_apply]
  simp only [← Fin.rev_succ, ← Fin.rev_castSucc, Fin.rev_injective.eq_iff]
  ring

private theorem torusCharacter_weight_rev {A : Type*} [CommRing A]
    (s : Fin r → Aˣ) (k : Fin (r + 1)) :
    (TauCeti.torusCharacter s (weight r k.rev))⁻¹ =
      TauCeti.torusCharacter (fun i => s i.rev) (weight r k) := by
  rw [← TauCeti.torusCharacter_neg]
  calc
    TauCeti.torusCharacter s (-weight r k.rev) =
        TauCeti.torusCharacter s (weight r k ∘ Fin.revPerm) := by
      congr 1
      funext i
      simpa using (weight_rev_rev r k.rev i).symm
    _ = TauCeti.torusCharacter (fun i => s i.rev) (weight r k) := by
      have h := (TauCeti.torusCharacter_mulEquivArrowCongr
        (Fin.revPerm : Equiv.Perm (Fin r)) s (weight r k)).symm
      change TauCeti.torusCharacter s (weight r k ∘ Fin.revPerm) =
        TauCeti.torusCharacter
          ((MulEquiv.arrowCongr Fin.revPerm (MulEquiv.refl Aˣ)) s) (weight r k) at h
      change TauCeti.torusCharacter s (weight r k ∘ Fin.revPerm) =
        TauCeti.torusCharacter
          ((MulEquiv.arrowCongr Fin.revPerm (MulEquiv.refl Aˣ)) s) (weight r k)
      exact h

private theorem torusCharacter_weight_rev_reindex {A : Type*} [CommRing A]
    (s : Fin r → Aˣ) (k : Fin (r + 1)) :
    (TauCeti.torusCharacter s (weight r k.rev))⁻¹ =
      TauCeti.torusCharacter s (weight r k ∘ Fin.revPerm) := by
  rw [torusCharacter_weight_rev]
  exact TauCeti.torusCharacter_mulEquivArrowCongr
    (Fin.revPerm : Equiv.Perm (Fin r)) s (weight r k)

/-! ## The ambient coordinate automorphism -/

/-- Signed reverse-inverse-transpose transported to general-linear coordinate-algebra points. -/
private noncomputable def generalLinearPointsGraphMulEquiv (A : CommAlgCat.{0} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A ≃*
      HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A :=
  ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) (r + 1)).trans
    (TauCeti.typeAGraphAutomorphism r A)).trans
      (GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) (r + 1)).symm

private theorem pointsMulEquiv_generalLinearPointsGraphMulEquiv
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A) :
    GeneralLinear.pointsMulEquiv (r + 1) (generalLinearPointsGraphMulEquiv r A f) =
      TauCeti.typeAGraphAutomorphism r A (GeneralLinear.pointsMulEquiv (r + 1) f) := by
  rw [generalLinearPointsGraphMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact (GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) (r + 1)).apply_symm_apply _

/-- The pointwise graph automorphism in the object presentation used by the points functor. -/
private noncomputable def generalLinearPointsGraphIsoApp (A : CommAlgCat.{0} ℤ) :
    (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))).obj A ≅
      (HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))).obj A :=
  eqToIso (HopfAlgebra.pointsFunctor_obj
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A) ≪≫
    (generalLinearPointsGraphMulEquiv r A).toGrpIso ≪≫
      eqToIso (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A).symm

/-- The natural automorphism of the general-linear functor of points induced by the matrix graph
automorphism. -/
private noncomputable def generalLinearPointsGraphNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) ≅
      HopfAlgebra.pointsFunctor
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) :=
  NatIso.ofComponents
    (fun A ↦ generalLinearPointsGraphIsoApp r A)
    (fun {A B} φ ↦ by
      apply (cancel_epi (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A).symm)).1
      apply (cancel_mono (eqToHom (HopfAlgebra.pointsFunctor_obj
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) B))).1
      rw [generalLinearPointsGraphIsoApp, generalLinearPointsGraphIsoApp]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, eqToHom_trans, Category.comp_id]
      simp only [← Category.assoc]
      rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 2 3 => rw [HopfAlgebra.pointsFunctor_map_eqToHom]
      slice_rhs 3 4 => simp
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      rw [GrpCat.comp_apply, GrpCat.comp_apply]
      change generalLinearPointsGraphMulEquiv r B (HopfAlgebra.mapPoints φ f) =
        HopfAlgebra.mapPoints φ (generalLinearPointsGraphMulEquiv r A f)
      apply (GeneralLinear.pointsMulEquiv (R := ℤ) (A := B) (r + 1)).injective
      simp only [HopfAlgebra.mapPoints]
      rw [pointsMulEquiv_generalLinearPointsGraphMulEquiv]
      change TauCeti.typeAGraphAutomorphism r B
          (GeneralLinear.pointsMulEquiv (r + 1) (AlgHom.mapValue φ.hom f)) =
        GeneralLinear.pointsMulEquiv (r + 1)
          (AlgHom.mapValue φ.hom (generalLinearPointsGraphMulEquiv r A f))
      rw [GeneralLinear.pointsMulEquiv_mapValue,
        GeneralLinear.pointsMulEquiv_mapValue,
        pointsMulEquiv_generalLinearPointsGraphMulEquiv,
        TauCeti.map_typeAGraphAutomorphism])

/-- The coordinate Hopf-algebra automorphism corresponding to signed reverse-inverse-transpose
on general-linear points. -/
private noncomputable def ambientGraphCoordinateIso :
    GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) ≅
      GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) :=
  ((CommHopfAlgCat.pointsFunctor (R := ℤ)).preimageIso
    (generalLinearPointsGraphNatIso r)).unop

private theorem pointsMulEquiv_mapPointsFunctor_ambientGraphCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A) :
    GeneralLinear.pointsMulEquiv (r + 1)
        ((CommHopfAlgCat.mapPointsFunctor (ambientGraphCoordinateIso r).hom).app A f) =
      TauCeti.typeAGraphAutomorphism r A (GeneralLinear.pointsMulEquiv (r + 1) f) := by
  have hmap := (CommHopfAlgCat.pointsFunctor (R := ℤ)).map_preimage
    (generalLinearPointsGraphNatIso r).hom
  have happ := congrArg (fun α => α.app A f) hmap
  have hcoordinate : (ambientGraphCoordinateIso r).hom.op =
      (CommHopfAlgCat.pointsFunctor (R := ℤ)).preimage
        (generalLinearPointsGraphNatIso r).hom := rfl
  change GeneralLinear.pointsMulEquiv (r + 1)
      (((CommHopfAlgCat.pointsFunctor (R := ℤ)).map
        (ambientGraphCoordinateIso r).hom.op).app A f) = _
  rw [hcoordinate, happ]
  change GeneralLinear.pointsMulEquiv (r + 1) (generalLinearPointsGraphMulEquiv r A f) = _
  exact pointsMulEquiv_generalLinearPointsGraphMulEquiv r A f

private theorem pointsMulEquiv_comp_ambientGraphCoordinateIso
    (A : CommAlgCat.{0} ℤ)
    (f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) A) :
    GeneralLinear.pointsMulEquiv (r + 1)
        (toConv (f.ofConv.comp ((ambientGraphCoordinateIso r).hom.hom :
          GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) →ₐ[ℤ]
            GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)))) =
      TauCeti.typeAGraphAutomorphism r A (GeneralLinear.pointsMulEquiv (r + 1) f) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
  exact pointsMulEquiv_mapPointsFunctor_ambientGraphCoordinateIso r A f

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
  rw [kostantRootSubgroupMatrix_eq_transvection, kostantRootSubgroupMatrix_eq_transvection]
  cases k with
  | inl i =>
      simpa only [graphRootPerm_inl, rootTarget_inl, rootSource_inl] using
        TauCeti.typeAGraphAutomorphism_transvectionUnit r i
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q))
  | inr i =>
      simpa only [graphRootPerm_inr, rootTarget_inr, rootSource_inr] using
        TauCeti.typeAGraphAutomorphism_transvectionUnit_lower r i
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q))

private theorem ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap
    (k : Fin r ⊕ Fin r) :
    (ambientGraphCoordinateIso r).hom ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
          (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
          (isNilpotent_rep_rootGenerator r k) (latticeBasis r) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
        (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r) := by
  let c := (ambientGraphCoordinateIso r).hom
  let x := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
  let y := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
    (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
  apply _root_.CommHopfAlgCat.hom_ext
  ext z
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  let f : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) :=
    toConv (q.ofConv.comp x.hom.toAlgHom)
  let g : HopfAlgebra.points
      (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) :=
    toConv (q.ofConv.comp y.hom.toAlgHom)
  have hx : GeneralLinear.pointToGeneralLinear (r + 1) f =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
      (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
      (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hy : GeneralLinear.pointToGeneralLinear (r + 1) g =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
        (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r) q :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (graphRootPerm r k)
      (isNilpotent_rep_rootGenerator r (graphRootPerm r k)) (latticeBasis r)
      (A := AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hp : toConv (f.ofConv.comp c.hom.toAlgHom) = g := by
    apply (GeneralLinear.pointsMulEquiv
      (R := ℤ) (A := CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
        (r + 1)).injective
    rw [pointsMulEquiv_comp_ambientGraphCoordinateIso,
      GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointsMulEquiv_apply]
    have hleft := congrArg (TauCeti.typeAGraphAutomorphism r
      (CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))) hx
    exact hleft.trans ((typeAGraphAutomorphism_kostantRootSubgroupMatrix
      (A := CommAlgCat.of ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) r k q).trans hy.symm)
  have hz := congrArg (fun p => p.ofConv z) hp
  simp only [f, g, q, AlgHom.id_apply, AlgHom.comp_apply] at hz
  rw [_root_.CommHopfAlgCat.comp_apply]
  exact hz

private theorem ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap :
    (ambientGraphCoordinateIso r).hom ≫
        GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) =
      GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm := by
  let c := (ambientGraphCoordinateIso r).hom
  let x := GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r)
  let y := GeneralLinear.weightTorusCoordinateMap (R := ℤ)
    (fun i => weight r i ∘ Fin.revPerm)
  have hxy : c ≫ x = y := by
    apply _root_.CommHopfAlgCat.hom_ext
    refine DFunLike.ext _ _ fun z => ?_
    let T := MonoidAlgebra ℤ (SplitTorus.characterGroup (Fin r))
    let q : WithConv (T →ₐ[ℤ] T) := toConv (AlgHom.id ℤ T)
    let f : HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (CommAlgCat.of ℤ T) :=
      toConv (q.ofConv.comp x.hom.toAlgHom)
    let g : HopfAlgebra.points
        (R := ℤ) (H := GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (CommAlgCat.of ℤ T) :=
      toConv (q.ofConv.comp y.hom.toAlgHom)
    have hx : GeneralLinear.pointsMulEquiv (r + 1) f =
        diagGL fun i => TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q) (weight r i) := by
      calc
        _ = GeneralLinear.pointsMulEquiv (r + 1)
            ((CommHopfAlgCat.mapPointsFunctor x).app (CommAlgCat.of ℤ T) q) := by
          rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
        _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
          (weight r) (CommAlgCat.of ℤ T) q
    have hy : GeneralLinear.pointsMulEquiv (r + 1) g =
        diagGL fun i => TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q)
          (weight r i ∘ Fin.revPerm) := by
      calc
        _ = GeneralLinear.pointsMulEquiv (r + 1)
            ((CommHopfAlgCat.mapPointsFunctor y).app (CommAlgCat.of ℤ T) q) := by
          rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
        _ = _ := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
          (fun i => weight r i ∘ Fin.revPerm) (CommAlgCat.of ℤ T) q
    have hp : toConv (f.ofConv.comp c.hom.toAlgHom) = g := by
      apply (GeneralLinear.pointsMulEquiv (R := ℤ) (A := CommAlgCat.of ℤ T)
        (r + 1)).injective
      rw [pointsMulEquiv_comp_ambientGraphCoordinateIso, hx, hy,
        TauCeti.typeAGraphAutomorphism_diagGL]
      congr 1
      funext i
      exact torusCharacter_weight_rev_reindex r (SplitTorus.pointsMulEquiv q) i
    have hz := congrArg (fun p => p.ofConv z) hp
    simp only [f, g, q, AlgHom.id_apply, AlgHom.comp_apply] at hz
    rw [_root_.CommHopfAlgCat.comp_apply]
    exact hz
  calc
    (ambientGraphCoordinateIso r).hom ≫
        GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) = y := hxy
    _ = GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r) ≫
        SplitTorus.relabelCoordinateMap ℤ Fin.revPerm := by
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

private theorem definingIdeal_comap_ambientGraphCoordinateIso_hom_le :
    (definingIdeal r).comapOfSurjective (ambientGraphCoordinateIso r).hom.hom
        (ConcreteCategory.bijective_of_isIso (ambientGraphCoordinateIso r).hom).2 ≤
      definingIdeal r := by
  refine kostantToralDefiningIdeal_comapOfSurjective_le_of_comp_eq
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)
      (ambientGraphCoordinateIso r).hom _ (graphRootPerm r)
      (SplitTorus.relabelCoordinateMap ℤ Fin.revPerm)
      (SplitTorus.relabelCoordinateMap_injective ℤ Fin.revPerm) (fun k => ?_) ?_
  · rw [ambientGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap,
      graphRootPerm_apply_apply]
  · exact ambientGraphCoordinateIso_hom_comp_weightTorusCoordinateMap r

private theorem definingIdeal_comap_ambientGraphCoordinateIso_inv_le :
    (definingIdeal r).comapOfSurjective (ambientGraphCoordinateIso r).inv.hom
        (ConcreteCategory.bijective_of_isIso (ambientGraphCoordinateIso r).inv).2 ≤
      definingIdeal r := by
  let c := ambientGraphCoordinateIso r
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
    (definingIdeal r).comapOfSurjective (ambientGraphCoordinateIso r).hom.hom
        (ConcreteCategory.bijective_of_isIso (ambientGraphCoordinateIso r).hom).2 =
      definingIdeal r := by
  exact HopfIdeal.comapOfSurjective_eq_of_hom_le_of_inv_le
    (ambientGraphCoordinateIso r) (definingIdeal r)
    (definingIdeal_comap_ambientGraphCoordinateIso_hom_le r)
    (definingIdeal_comap_ambientGraphCoordinateIso_inv_le r)

/-- The graph automorphism induced on the standard carrier's quotient coordinate algebra. -/
private noncomputable def graphCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r) ≅
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
        (definingIdeal r) :=
  CommHopfAlgCat.quotientIsoOfComapEq (ambientGraphCoordinateIso r) (definingIdeal r)
    (definingIdeal_comap_ambientGraphCoordinateIso r)

private theorem mkQuotient_comp_graphCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r) ≫
        (graphCoordinateIso r).hom =
      (ambientGraphCoordinateIso r).hom ≫
        CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r) := by
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom
    (ambientGraphCoordinateIso r) (definingIdeal r)
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

/-- The graph automorphism reverses the Bourbaki numbering of every positive and negative simple
root subgroup, without changing its additive parameter. -/
@[simp]
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
@[simp]
theorem weightTorus_comp_graphAutomorphism_hom :
    weightTorus r ≫ (graphAutomorphism r).hom =
      SplitTorus.relabel ℤ Fin.revPerm ≫ weightTorus r := by
  rw [weightTorus_def, kostantWeightTorusToToral_def, graphAutomorphism,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    ← Functor.map_comp, ← op_comp, graphCoordinateIso_hom_comp_torusMap, op_comp,
    Functor.map_comp, SplitTorus.relabel_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end TauCeti.SlStd
