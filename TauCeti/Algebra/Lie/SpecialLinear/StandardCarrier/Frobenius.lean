/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# Frobenius on the full-weight type-A carrier

`TauCeti.SlStd.groupScheme r` is the explicit full-weight Chevalley carrier of type `A_r` built
from the standard representation of `sl_{r+1}` and its coordinate integral lattice. For a
commutative value ring `A` of exponential characteristic `p`, this file equips its point group
`TauCeti.SlStd.points r A` with the `p ^ k`-power Frobenius endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F(x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring.

The construction specializes the generic Frobenius of a Kostant toral closure; it does not reprove
entrywise Frobenius stability. Nothing here asserts that the carrier is reductive, or that any
fixed-point group is finite or simple.

## Main definitions

* `TauCeti.SlStd.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`A_r` point group.

## Main results

* `TauCeti.SlStd.coe_frobenius` and `TauCeti.SlStd.coe_frobenius_apply`: the endomorphism acts by
  entrywise Frobenius.
* `TauCeti.SlStd.frobenius_rootSubgroupPoints` and `TauCeti.SlStd.frobenius_weightTorusPoints`: the
  equations on the pinned generating root subgroups and split torus.
* `TauCeti.SlStd.frobenius_zero` and `TauCeti.SlStd.frobenius_add`: the iteration laws.
* `TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq`: the Frobenius-fixed points are the points
  over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the "points over an algebraically closed field" and "Chevalley--Demazure
construction" targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`: this is the Frobenius component intended
for a future construction of the `A_r(p ^ k)` Steinberg map over an algebraic closure of `ZMod p`.
-/

public section

open WithConv

namespace TauCeti.SlStd

universe v

noncomputable section

variable (r p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

private theorem points_eq_kostantToralPointsSubgroup :
    points r A =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A := by
  ext g
  rw [mem_points_iff,
    TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff]

private def pointsEquivKostantToralPoints :
    points r A ≃*
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A :=
  MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup r A)

@[simp]
private theorem coe_pointsEquivKostantToralPoints (g : points r A) :
    (pointsEquivKostantToralPoints r A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) = g :=
  rfl

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`A_r` carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `A_r(p ^ k)` Steinberg map. -/
def frobenius : points r A →* points r A :=
  (pointsEquivKostantToralPoints r A).symm.toMonoidHom.comp
    ((TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius (rootGenerator r)
      (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A).comp
        (pointsEquivKostantToralPoints r A).toMonoidHom)

private theorem pointsEquivKostantToralPoints_frobenius (g : points r A) :
    pointsEquivKostantToralPoints r A (frobenius r p k A g) =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A
        (pointsEquivKostantToralPoints r A g) := by
  simp only [frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

/-- The Frobenius endomorphism of the type-`A_r` carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points r A) :
    (frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  have h := congrArg Subtype.val (pointsEquivKostantToralPoints_frobenius r p k A g)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its
`p ^ k`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : points r A) (i j : Fin (r + 1)) :
    ((frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j =
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ^ p ^ k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius_apply
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A
      (pointsEquivKostantToralPoints r A g) i j
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- **Frobenius raises the parameter of a numbered type-`A_r` root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin r ⊕ Fin r) (u : Multiplicative A) :
    frobenius r p k A (rootSubgroupPoints r i A u) =
      rootSubgroupPoints r i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply (pointsEquivKostantToralPoints r A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantRootSubgroupMatrix
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A i u)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  exact h

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin r → Aˣ) :
    frobenius r p k A (weightTorusPoints r A s) = weightTorusPoints r A (s ^ p ^ k) := by
  apply (pointsEquivKostantToralPoints r A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantTorusMatrix
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A s)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using h

/-- The zeroth Frobenius iterate is the identity on the type-`A_r` point group. -/
@[simp]
theorem frobenius_zero : frobenius r p 0 A = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints r A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.id_apply]
  have h := DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_zero
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p A)
    (pointsEquivKostantToralPoints r A g)
  simpa only [MonoidHom.id_apply] using h

/-- Frobenius iterates add under composition on the type-`A_r` point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius r p (k + m) A = (frobenius r p k A).comp (frobenius r p m A) := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints r A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.comp_apply,
    pointsEquivKostantToralPoints_frobenius, pointsEquivKostantToralPoints_frobenius]
  exact DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_add
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A m)
    (pointsEquivKostantToralPoints r A g)

/-- A type-`A_r` carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points r A) :
    frobenius r p k A g = g ↔
      ∀ i j, ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ∈ frobeniusFixedSubring A p k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_eq_self_iff
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A
      (pointsEquivKostantToralPoints r A g)
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simp only [coe_pointsEquivKostantToralPoints] at h
  constructor
  · intro hg
    exact h.mp (congrArg (pointsEquivKostantToralPoints r A) hg)
  · intro hg
    apply (pointsEquivKostantToralPoints r A).injective
    exact h.mpr hg

/-- **The Frobenius-fixed points of the full-weight type-`A_r` carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius r p k A)).map (points r A).subtype =
      (points r ↥(frobeniusFixedSubring A p k)).map
        (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius r p k A) _
    (coe_frobenius r p k A)]
  rw [points_eq_kostantToralPointsSubgroup,
    points_eq_kostantToralPointsSubgroup]
  rw [← TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius]
  exact
    TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius_eq
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A

end

end TauCeti.SlStd
