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
* `TauCeti.SlStd.frobenius_rootSubgroupPoint` and `TauCeti.SlStd.frobenius_weightTorusPoint`: the
  equations on the pinned generating root subgroups and split torus.
* `TauCeti.SlStd.frobenius_zero` and `TauCeti.SlStd.frobenius_add`: the iteration laws.
* `TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq`: the Frobenius-fixed points are the points
  over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the "points over an algebraically closed field" and "Chevalley--Demazure
construction" targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`: on an algebraic closure of `ZMod p`, the
ordinary `A_r(q)` Steinberg map is this Frobenius with `q = p ^ k`.
-/

public section

open WithConv

namespace TauCeti.SlStd

universe v

noncomputable section

variable (r p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`A_r` carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the untwisted Steinberg
endomorphism used to construct `A_r(p ^ k)`. -/
def frobenius : points r A →* points r A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A

/-- The Frobenius endomorphism of the type-`A_r` carrier acts by entrywise Frobenius. -/
@[simp]
theorem coe_frobenius (g : points r A) :
    (frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius]
  exact TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv ↦ rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) p k A g

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its
`p ^ k`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : points r A) (i j : Fin (r + 1)) :
    ((frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j =
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ^ p ^ k := by
  rw [coe_frobenius, Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`A_r` root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoint (i : Fin r ⊕ Fin r) (u : Multiplicative A) :
    frobenius r p k A (rootSubgroupPoint r i A u) =
      rootSubgroupPoint r i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) :=
  Subtype.ext (by
    rw [coe_frobenius, coe_rootSubgroupPoint, coe_rootSubgroupPoint]
    apply TauCeti.UniversalEnvelopingAlgebra.map_iterateFrobenius_kostantRootSubgroupMatrix)

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoint (s : Fin r → Aˣ) :
    frobenius r p k A (weightTorusPoint r A s) = weightTorusPoint r A (s ^ p ^ k) :=
  Subtype.ext (by
    rw [coe_frobenius, coe_weightTorusPoint, coe_weightTorusPoint]
    simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
      TauCeti.UniversalEnvelopingAlgebra.map_iterateFrobenius_kostantTorusMatrix
        (M := (lattice r).toAddSubgroup) (b := latticeBasis r) (wt := weight r)
        (p := p) (k := k) s)

/-- The zeroth Frobenius iterate is the identity on the type-`A_r` point group. -/
@[simp]
theorem frobenius_zero : frobenius r p 0 A = MonoidHom.id _ := by
  refine MonoidHom.ext fun g ↦ Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j ↦ ?_)
  rw [coe_frobenius_apply, MonoidHom.id_apply, pow_zero, pow_one]

/-- Frobenius iterates add under composition on the type-`A_r` point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius r p (k + m) A = (frobenius r p k A).comp (frobenius r p m A) := by
  refine MonoidHom.ext fun g ↦ Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j ↦ ?_)
  rw [coe_frobenius_apply, MonoidHom.comp_apply, coe_frobenius_apply,
    coe_frobenius_apply, ← pow_mul, ← pow_add, Nat.add_comm k m]

/-- A type-`A_r` carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points r A) :
    frobenius r p k A g = g ↔
      ∀ i j, ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`A_r` carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius r p k A)).map (points r A).subtype =
      (points r ↥(frobeniusFixedSubring A p k)).map
        (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius r p k A) _
      (coe_frobenius r p k A)]
  unfold points
  rw [TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def,
    TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def,
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.SlStd
