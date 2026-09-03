/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor
-- The toral-closure Frobenius is used only inside the proof of `frobenius_weightTorusPoints`, so
-- it is imported privately rather than re-exported to consumers of this module.
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# The Frobenius of the doubled type-E6 minuscule carrier

`TauCeti.E6DoubledMinuscule.groupScheme` is the explicit full-weight type-`E₆` carrier over `ℤ`
built from `V(ϖ₁) ⊕ V(ϖ₆)`, and `TauCeti.E6DoubledMinuscule.points A` realizes its `A`-valued
points as a subgroup of `GL₅₄(A)`. Over a commutative ring `A` of exponential characteristic `p`,
entrywise `p ^ k`-th powers are a homomorphism of value rings, so the carrier's functoriality
turns them into a group endomorphism of its points.

This file names that endomorphism `TauCeti.E6DoubledMinuscule.frobenius` and records its
characteristic equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity, exponents add under composition and multiply under taking
powers in the endomorphism monoid, and the fixed points are the points of the same carrier over
the Frobenius-fixed subring.

The `27`-dimensional carrier already carries a Frobenius, `TauCeti.E6Minuscule.frobenius`, and it
is the one the untwisted family `E₆(q)` is built from. What the doubled carrier adds is the index
set on which the `E₆` diagram symmetry acts, by
`TauCeti.DynkinType.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm`, whereas that symmetry
moves every minuscule weight off the twenty-seven-element table by
`TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range`. A Steinberg map composing a
graph automorphism with a field Frobenius therefore needs the Frobenius of *this* carrier, which
is what is built here. The graph automorphism itself is not built here, and no declaration below
mentions the diagram symmetry.

Nothing here asserts reductivity, maximality of the weight torus, an identification of the
carrier's root datum, or any finiteness or simplicity statement.

## Main declarations

* `TauCeti.E6DoubledMinuscule.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.E6DoubledMinuscule.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise
  actions.
* `TauCeti.E6DoubledMinuscule.frobenius_rootSubgroupPoints`: its action on every numbered
  simple-root subgroup.
* `TauCeti.E6DoubledMinuscule.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.E6DoubledMinuscule.frobenius_zero`, `frobenius_add` and `frobenius_pow`: its iteration
  laws.
* `TauCeti.E6DoubledMinuscule.frobenius_eq_self_iff` and
  `TauCeti.E6DoubledMinuscule.map_subtype_fixedSubgroup_frobenius_eq`: which points it fixes, and
  the identification of the fixed subgroup with the points over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the doubled minuscule realization on
  which the twisted family `²E₆(q)` is built.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The formal organization follows the carrier specializations
  `TauCeti.Algebra.Lie.E6.Minuscule.Frobenius`,
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius` and
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius`, and the power law follows
  `TauCeti.DynkinType.geckFrobenius_pow` in
  `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius`. Every
  general fact used about entrywise Frobenius is consumed rather than reproved: the facts about
  the points cut out by a Hopf ideal from
  `TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear`, and the entrywise Frobenius of a
  weight-torus matrix from
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius`.

## Roadmap

This advances the target "points over an algebraically closed field as a group, functorially in
the field, so that a field endomorphism induces a group endomorphism of the points", whose "the
`q`-power Frobenius is the case a consumer asks for first", in Layer 9, "pinned
Chevalley--Demazure group schemes over `ℤ`", of `TauCetiRoadmap/ReductiveGroups/README.md`. Its
consumer is milestone L1, "ordinary and graph Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose Steinberg map for the twisted family `²E₆(q)` is
`γ₂ ∘ Frob_q` on the points of a carrier for the `E₆` diagram over an algebraic closure of
`ZMod p`; the identification of this carrier with the pinned simply connected Chevalley--Demazure
group that milestone requires remains pending, as does the graph automorphism `γ₂`.
-/

public section

namespace TauCeti.E6DoubledMinuscule

universe v

noncomputable section

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight doubled type-`E₆` minuscule
carrier**, the functorial map on points induced by the iterated Frobenius endomorphism of the
value ring.

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius factor of
the Steinberg map that a future construction of the twisted family `²E₆(p ^ k)` composes with the
`E₆` graph automorphism. -/
def frobenius : points A →* points A :=
  pointsMap (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the doubled minuscule carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 54) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
        _root_.Matrix (Fin 54) (Fin 54) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
        _root_.Matrix (Fin 54) (Fin 54) A) i j ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of every numbered doubled type-`E₆` simple-root subgroup to
its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 6 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) :=
  Subtype.ext (by
    rw [coe_frobenius, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.map_iterateFrobenius_kostantTorusMatrix, coe_weightTorusPoints])

/-- The zeroth Frobenius iterate is the identity on the doubled minuscule carrier's point
group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the doubled minuscule carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `p ^ k`-power
Frobenius of the doubled minuscule carrier, in the endomorphism monoid of its points, is its
`p ^ (k * m)`-power Frobenius. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from frobenius p k A) ^ m = frobenius p (k * m) A := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, frobenius_zero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, frobenius_add p (k * m) A k]; rfl

/-- A doubled minuscule carrier point is fixed by Frobenius exactly when all of its matrix entries
lie in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 54) A) :
        _root_.Matrix (Fin 54) (Fin 54) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight doubled minuscule carrier are its points over
the Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
      (coe_frobenius p k A), points_def A, points_def ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.E6DoubledMinuscule
