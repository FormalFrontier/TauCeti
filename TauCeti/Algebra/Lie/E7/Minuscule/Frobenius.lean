/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor
-- The endomorphism power law and the toral-closure Frobenius are used only inside the proofs of
-- `frobenius_pow` and `frobenius_weightTorusPoints`, so they are imported privately rather than
-- re-exported to consumers of this module.
import TauCeti.Algebra.Group.Hom.End
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# The Frobenius of the full-weight type-E7 minuscule carrier

`TauCeti.E7Minuscule.groupScheme` is the explicit full-weight type-`E₇` Chevalley carrier over
`ℤ`, the Kostant toral closure built from the `56`-dimensional minuscule representation and its
admissible lattice, and `TauCeti.E7Minuscule.points A` realizes its `A`-valued points as a
subgroup of `GL₅₆(A)`. Over a commutative ring `A` of exponential characteristic `p`, entrywise
`p ^ k`-th powers are a homomorphism of value rings, so the carrier's functoriality turns them
into a group endomorphism of its points.

This file names that endomorphism `TauCeti.E7Minuscule.frobenius` and records its characteristic
equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity, exponents add under composition and multiply under taking
powers in the endomorphism monoid, and the fixed points are the points of the same carrier over
the Frobenius-fixed subring of `A`.

The `E₇` diagram has no nontrivial symmetry, so a Steinberg endomorphism built on this carrier
is a field Frobenius alone, with no graph automorphism to compose with. Nothing here asserts
reductivity, maximality of the weight torus, an identification of the carrier's root datum, or
any finiteness or simplicity statement.

## Main declarations

* `TauCeti.E7Minuscule.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.E7Minuscule.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise actions.
* `TauCeti.E7Minuscule.frobenius_rootSubgroupPoints`: its action on every numbered simple-root
  subgroup.
* `TauCeti.E7Minuscule.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.E7Minuscule.frobenius_zero`, `frobenius_add` and `frobenius_pow`: its iteration laws.
* `TauCeti.E7Minuscule.frobenius_eq_self_iff` and
  `TauCeti.E7Minuscule.map_subtype_fixedSubgroup_frobenius_eq`: which points it fixes, and the
  identification of the fixed subgroup with the points over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The formal organization follows the carrier specializations
  `TauCeti.Algebra.Lie.E6.Minuscule.Frobenius`,
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius`,
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius` and
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius`.
-/

public section

namespace TauCeti.E7Minuscule

universe v

noncomputable section

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`E₇` minuscule carrier**,
the functorial map on points induced by the iterated Frobenius endomorphism of the value ring.

For `p` prime, `0 < k` and `A` an algebraic closure of `ZMod p`, this is the `q`-power Frobenius
of the carrier's points for `q = p ^ k`. -/
def frobenius : points A →* points A :=
  pointsMap (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the type-`E₇` minuscule carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 56) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 56) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 56) A) :
        _root_.Matrix (Fin 56) (Fin 56) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 56) A) :
        _root_.Matrix (Fin 56) (Fin 56) A) i j ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of every numbered type-`E₇` simple-root subgroup to its
`p ^ k`-th power**, on both the raising and the lowering generators. -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 7 ⊕ Fin 7) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 7 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) :=
  Subtype.ext (by
    rw [coe_frobenius, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.map_iterateFrobenius_kostantTorusMatrix, coe_weightTorusPoints])

/-- The zeroth Frobenius iterate is the identity on the type-`E₇` minuscule carrier's point
group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the type-`E₇` minuscule carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `p ^ k`-power
Frobenius of the type-`E₇` minuscule carrier, in the endomorphism monoid of its points, is its
`p ^ (k * m)`-power Frobenius. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated. `frobenius_zero` and `frobenius_add` are exactly the
-- hypotheses of the carrier-independent law `TauCeti.pow_eq_of_id_of_comp`.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from frobenius p k A) ^ m = frobenius p (k * m) A :=
  pow_eq_of_id_of_comp (fun i => frobenius p i A) (frobenius_zero p A)
    (fun i j => frobenius_add p i A j) k m

/-- A type-`E₇` minuscule carrier point is fixed by Frobenius exactly when all of its matrix
entries lie in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 56) A) :
        _root_.Matrix (Fin 56) (Fin 56) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`E₇` minuscule carrier are its points
over the Frobenius-fixed subring.** No finiteness of either side is asserted. -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
      (coe_frobenius p k A), points_def A, points_def ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.E7Minuscule
