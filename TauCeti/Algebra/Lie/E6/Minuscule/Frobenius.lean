/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear

/-!
# The Frobenius of the full-weight type-E6 minuscule carrier

The type-`E₆` minuscule carrier is the explicit Kostant toral closure over `ℤ` built from the
27-dimensional minuscule representation and its admissible full-weight lattice. Over a commutative
ring `A` of exponential characteristic `p`, entrywise `p ^ k`-th powers preserve its defining Hopf
ideal and therefore give a group endomorphism of its `A`-valued points.

This file names that endomorphism `TauCeti.E6Minuscule.frobenius` and records its characteristic
equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity and exponents add under composition. The fixed points are the
points of the same carrier over the Frobenius-fixed subring. No reductivity, finiteness, or
simplicity statement is involved.

## Main declarations

* `TauCeti.E6Minuscule.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.E6Minuscule.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise actions.
* `TauCeti.E6Minuscule.frobenius_rootSubgroupPoints`: its action on every numbered simple-root
  subgroup.
* `TauCeti.E6Minuscule.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.E6Minuscule.frobenius_zero` and `frobenius_add`: its iteration laws.
* `TauCeti.E6Minuscule.map_subtype_fixedSubgroup_frobenius_eq`: the identification of its fixed
  points with points over the fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The formal organization follows the carrier specializations
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius` and
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius` and uses the carrier's functorial
  points API.

This advances the Layer 9 target "points over an algebraically closed field as a group,
functorially in the field" of `TauCetiRoadmap/ReductiveGroups/README.md`, which names the
`q`-power Frobenius as its first consumer-facing case. Milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md` will consume this carrier Frobenius and its root-subgroup
equation in a future construction of the ordinary `E₆(q)` Steinberg map. The identification of
this carrier with the required pinned simply connected reductive group remains pending.
-/

public section

open WithConv
open scoped Matrix

namespace TauCeti.E6Minuscule

universe v

noncomputable section

open TauCeti.DynkinType

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`E₆` minuscule carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the carrier Frobenius
intended for a future construction of the ordinary `E₆(p ^ k)` Steinberg map. -/
def frobenius : points A →* points A :=
  pointsMap (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the minuscule carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 27) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of every numbered type-`E₆` simple-root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 6 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) := by
  have hs : (fun j => Units.map (iterateFrobenius A p k : A →* A) (s j)) = s ^ p ^ k := by
    funext j
    exact Units.ext (by
      rw [Units.coe_map, MonoidHom.coe_coe, iterateFrobenius_def, Pi.pow_apply,
        Units.val_pow_eq_pow_val])
  rw [frobenius, pointsMap_weightTorusPoints, hs]

/-- The zeroth Frobenius iterate is the identity on the minuscule carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the minuscule carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- A minuscule-carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight minuscule carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
      (coe_frobenius p k A), points_def A, points_def ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end


end TauCeti.E6Minuscule
