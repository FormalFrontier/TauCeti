/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# Frobenius on the full-weight type-C carrier

`TauCeti.SpStd.groupScheme n` is the explicit full-weight Chevalley carrier of type `C_(n+1)`,
built from the standard representation of `sp_(2n+2)` and its coordinate integral lattice. For a
commutative value ring `A` of exponential characteristic `p`, this file equips its point group
`TauCeti.SpStd.points n A` with the `p ^ k`-power Frobenius endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F(x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring.

The construction specializes the generic Frobenius of a Kostant toral closure, and every equation
below is read off the corresponding generic statement; nothing about the symplectic Lie algebra or
its lattice is used again here. Nothing asserts that the carrier is reductive, that it is the
symplectic group scheme, or that any fixed-point group is finite or simple.

## Main definitions

* `TauCeti.SpStd.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`C_(n+1)` point
  group.

## Main results

* `TauCeti.SpStd.coe_frobenius` and `TauCeti.SpStd.coe_frobenius_apply`: the endomorphism acts by
  entrywise Frobenius.
* `TauCeti.SpStd.frobenius_rootSubgroupPoints` and `TauCeti.SpStd.frobenius_weightTorusPoints`: the
  equations on the pinned generating root subgroups and split torus.
* `TauCeti.SpStd.frobenius_zero` and `TauCeti.SpStd.frobenius_add`: the iteration laws.
* `TauCeti.SpStd.map_subtype_fixedSubgroup_frobenius_eq`: the Frobenius-fixed points are the points
  over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the "points over an algebraically closed field" and "Chevalley--Demazure
construction" targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose first named
case is the `q`-power Frobenius. Its consumer is milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose Steinberg map for the untwisted family `C_n(q)` is
`Frob_q` on the points of the pinned type-`C` ambient group over an algebraic closure of `ZMod p`.
The type-`A` counterpart is
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/Frobenius.lean`.
-/

public section

open WithConv

namespace TauCeti.SpStd

universe v

noncomputable section

variable (n p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

private theorem points_eq_kostantToralPointsSubgroup :
    points n A =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A := by
  ext g
  rw [mem_points_iff, definingIdeal_def,
    TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff]

private def pointsEquivKostantToralPoints :
    points n A ≃*
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A :=
  MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup n A)

@[simp]
private theorem coe_pointsEquivKostantToralPoints (g : points n A) :
    (pointsEquivKostantToralPoints n A g :
      _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) = g :=
  rfl

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`C_(n+1)` carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `C_(n+1)(p ^ k)` Steinberg map. -/
def frobenius : points n A →* points n A :=
  (pointsEquivKostantToralPoints n A).symm.toMonoidHom.comp
    ((TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius (rootGenerator n)
      (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A).comp
        (pointsEquivKostantToralPoints n A).toMonoidHom)

private theorem pointsEquivKostantToralPoints_frobenius (g : points n A) :
    pointsEquivKostantToralPoints n A (frobenius n p k A g) =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A
        (pointsEquivKostantToralPoints n A g) := by
  simp only [frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

/-- The Frobenius endomorphism of the type-`C_(n+1)` carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points n A) :
    (frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  have h := congrArg Subtype.val (pointsEquivKostantToralPoints_frobenius n p k A g)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its
`p ^ k`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : points n A) (i j : Fin ((n + 1) + (n + 1))) :
    ((frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j ^ p ^ k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius_apply
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A
      (pointsEquivKostantToralPoints n A g) i j
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- **Frobenius raises the parameter of a numbered type-`C_(n+1)` root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    frobenius n p k A (rootSubgroupPoints n i A u) =
      rootSubgroupPoints n i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply (pointsEquivKostantToralPoints n A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantRootSubgroupMatrix
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A i u)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  exact h

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin (n + 1) → Aˣ) :
    frobenius n p k A (weightTorusPoints n A s) = weightTorusPoints n A (s ^ p ^ k) := by
  apply (pointsEquivKostantToralPoints n A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantTorusMatrix
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A s)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using h

/-- The zeroth Frobenius iterate is the identity on the type-`C_(n+1)` point group. -/
@[simp]
theorem frobenius_zero : frobenius n p 0 A = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints n A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.id_apply]
  have h := DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_zero
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p A)
    (pointsEquivKostantToralPoints n A g)
  simpa only [MonoidHom.id_apply] using h

/-- Frobenius iterates add under composition on the type-`C_(n+1)` point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius n p (k + m) A = (frobenius n p k A).comp (frobenius n p m A) := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints n A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.comp_apply,
    pointsEquivKostantToralPoints_frobenius, pointsEquivKostantToralPoints_frobenius]
  exact DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_add
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A m)
    (pointsEquivKostantToralPoints n A g)

/-- A type-`C_(n+1)` carrier point is fixed by Frobenius exactly when all of its matrix entries lie
in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points n A) :
    frobenius n p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
          _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j ∈
        frobeniusFixedSubring A p k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_eq_self_iff
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A
      (pointsEquivKostantToralPoints n A g)
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simp only [coe_pointsEquivKostantToralPoints] at h
  constructor
  · intro hg
    exact h.mp (congrArg (pointsEquivKostantToralPoints n A) hg)
  · intro hg
    exact (pointsEquivKostantToralPoints n A).injective (h.mpr hg)

/-- **The Frobenius-fixed points of the full-weight type-`C_(n+1)` carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius n p k A)).map (points n A).subtype =
      (points n ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius n p k A) _
    (coe_frobenius n p k A)]
  rw [points_eq_kostantToralPointsSubgroup, points_eq_kostantToralPointsSubgroup]
  rw [← TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius]
  exact
    TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius_eq
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) p k A

end

end TauCeti.SpStd
