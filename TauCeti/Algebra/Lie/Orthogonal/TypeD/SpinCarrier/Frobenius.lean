/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.PointsFunctor
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# Frobenius on the full-weight type-D spin carrier

`TauCeti.TypeDSpinCarrier.groupScheme n hn` is the explicit full-weight Chevalley carrier of type
`Dₙ`, cut out inside `GL_(2^n)` over `ℤ` by the split spin representation and its exterior
coordinate lattice. For a commutative value ring `A` of exponential characteristic `p`, this file
equips its point group `TauCeti.TypeDSpinCarrier.points n hn A` with the `p ^ k`-power Frobenius
endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F (x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split spin weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring of `A`.

The construction specializes the generic Frobenius of a Kostant toral closure, and every equation
below is read off the corresponding generic statement; nothing about the spin representation or its
exterior lattice is used again here. Nothing asserts that the carrier is reductive, that it is the
spin group scheme, or that any fixed-point group is finite or simple.

## Main definitions

* `TauCeti.TypeDSpinCarrier.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`Dₙ`
  spin carrier's point group.

## Main results

* `TauCeti.TypeDSpinCarrier.coe_frobenius` and `TauCeti.TypeDSpinCarrier.coe_frobenius_apply`: the
  endomorphism acts by entrywise Frobenius.
* `TauCeti.TypeDSpinCarrier.frobenius_eq_pointsMap`: it is the functorial point map induced by the
  iterated Frobenius endomorphism of the value ring.
* `TauCeti.TypeDSpinCarrier.frobenius_rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.frobenius_weightTorusPoints`: the equations on the pinned generating
  root subgroups and split spin weight torus.
* `TauCeti.TypeDSpinCarrier.frobenius_zero` and `TauCeti.TypeDSpinCarrier.frobenius_add`: the
  iteration laws.
* `TauCeti.TypeDSpinCarrier.frobenius_eq_self_iff` and
  `TauCeti.TypeDSpinCarrier.map_subtype_fixedSubgroup_frobenius_eq`: a point is fixed exactly when
  its entries lie in the Frobenius-fixed subring, so the fixed points are the points of the same
  carrier over that subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the "points over an algebraically closed field" target in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, whose first named case is the `q`-power Frobenius, for
the type-`D` carrier that Layer 9's Chevalley--Demazure construction assembles. Its consumer is
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`, whose table prescribes `Frob_q` as the
Steinberg map of the untwisted family `Dₙ(q)` and `γ ∘ Frob_q` for the twisted families `²Dₙ(q)`
and `³D₄(q)`, all three built on this diagram. The type-`A`, type-`C` and type-`E₆` counterparts
are `TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/Frobenius.lean`,
`TauCeti/Algebra/Lie/Symplectic/StandardCarrier/Frobenius.lean` and
`TauCeti/Algebra/Lie/E6/Minuscule/Frobenius.lean`, and this file follows their formal template.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

/-- The presentation of the named type-`Dₙ` spin carrier points as the generic Kostant
toral-closure points of its represented data. Private: it is the internal bridge along which the
generic Frobenius API is read, while `TauCeti.TypeDSpinCarrier.points_def` is the presentation a
consumer sees. -/
private theorem points_eq_kostantToralPointsSubgroup (n : ℕ) (hn : 4 ≤ n) (B : Type v)
    [CommRing B] :
    points n hn B =
      kostantToralPointsSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) B := by
  ext g
  rw [mem_points_iff, definingIdeal_def, mem_kostantToralPointsSubgroup_iff]

variable (n : ℕ) (hn : 4 ≤ n) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- The presentation of `TauCeti.TypeDSpinCarrier.points` as generic toral-closure points, as a
group isomorphism. Private, for the same reason as
`TauCeti.TypeDSpinCarrier.points_eq_kostantToralPointsSubgroup`. -/
private def pointsEquivKostantToralPoints :
    points n hn A ≃*
      kostantToralPointsSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A :=
  MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup n hn A)

@[simp]
private theorem coe_pointsEquivKostantToralPoints (g : points n hn A) :
    (pointsEquivKostantToralPoints n hn A g :
      _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) = g :=
  (rfl)

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`Dₙ` spin carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `Dₙ(p ^ k)`, `²Dₙ(p ^ k)` and `³D₄(p ^ k)` Steinberg
maps. -/
def frobenius : points n hn A →* points n hn A :=
  (pointsEquivKostantToralPoints n hn A).symm.toMonoidHom.comp
    ((kostantToralFrobenius
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) p k A).comp
      (pointsEquivKostantToralPoints n hn A).toMonoidHom)

/-- Along the presentation as generic toral-closure points, the carrier Frobenius is the generic
Kostant toral Frobenius. Private: it is the transport equation through which the public equations
below read the generic API, so they do not depend on how the presentation is implemented. -/
private theorem pointsEquivKostantToralPoints_frobenius (g : points n hn A) :
    pointsEquivKostantToralPoints n hn A (frobenius n hn p k A g) =
      kostantToralFrobenius
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) p k A
        (pointsEquivKostantToralPoints n hn A g) := by
  simp only [frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

/-- The Frobenius endomorphism of the type-`Dₙ` spin carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level normal
form. -/
theorem coe_frobenius (g : points n hn A) :
    (frobenius n hn p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  have h := congrArg Subtype.val (pointsEquivKostantToralPoints_frobenius n hn p k A g)
  rw [coe_kostantToralFrobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- **The carrier Frobenius is the functorial map on points** induced by the iterated Frobenius
endomorphism of the value ring, so it is an instance of `TauCeti.TypeDSpinCarrier.pointsMap` rather
than a separate endomorphism. -/
theorem frobenius_eq_pointsMap :
    frobenius n hn p k A = pointsMap n hn (iterateFrobenius A p k) :=
  MonoidHom.ext fun g => Subtype.ext (by rw [coe_frobenius, coe_pointsMap])

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points n hn A) (r c : Fin (dimension n)) :
    ((frobenius n hn p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`Dₙ` root subgroup to its `p ^ k`-th
power**, that is, `F (x_i(u)) = x_i(u ^ (p ^ k))` on both the raising and the lowering
generators. -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin n ⊕ Fin n) (u : Multiplicative A) :
    frobenius n hn p k A (rootSubgroupPoints n hn i A u) =
      rootSubgroupPoints n hn i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply Subtype.ext
  rw [coe_frobenius, coe_rootSubgroupPoints, coe_rootSubgroupPoints]
  exact map_iterateFrobenius_kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) p k i u

/-- **Frobenius raises every coordinate of the pinned split spin weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin n → Aˣ) :
    frobenius n hn p k A (weightTorusPoints n hn A s) =
      weightTorusPoints n hn A (s ^ p ^ k) := by
  apply Subtype.ext
  rw [coe_frobenius, coe_weightTorusPoints, coe_weightTorusPoints]
  exact map_iterateFrobenius_kostantTorusMatrix (M := (lattice n).toAddSubgroup)
    (b := latticeBasis n) (wt := basisWeight n) (p := p) (k := k) s

/-- The zeroth Frobenius iterate is the identity on the type-`Dₙ` spin carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius n hn p 0 A = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => (pointsEquivKostantToralPoints n hn A).injective ?_
  rw [pointsEquivKostantToralPoints_frobenius]
  have h := DFunLike.congr_fun
    (kostantToralFrobenius_zero
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) p A)
    (pointsEquivKostantToralPoints n hn A g)
  simpa only [MonoidHom.id_apply] using h

/-- Frobenius iterates add under composition on the type-`Dₙ` spin carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius n hn p (k + m) A = (frobenius n hn p k A).comp (frobenius n hn p m A) := by
  refine MonoidHom.ext fun g => (pointsEquivKostantToralPoints n hn A).injective ?_
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.comp_apply,
    pointsEquivKostantToralPoints_frobenius, pointsEquivKostantToralPoints_frobenius]
  exact DFunLike.congr_fun
    (kostantToralFrobenius_add
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) p k A m)
    (pointsEquivKostantToralPoints n hn A g)

/-- A type-`Dₙ` spin carrier point is fixed by Frobenius exactly when all of its matrix entries lie
in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points n hn A) :
    frobenius n hn p k A g = g ↔
      ∀ r c, ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
          _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ∈
        frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`Dₙ` spin carrier are its points over the
Frobenius-fixed subring.** For `p` prime, `0 < k`, `A` an algebraic closure of `ZMod p` and
`q = p ^ k` this reads the fixed group of the untwisted `Dₙ(q)` Steinberg map as the carrier's
`𝔽_q`-points; no finiteness of either side is asserted. -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius n hn p k A)).map (points n hn A).subtype =
      (points n hn ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius n hn p k A) _
      (coe_frobenius n hn p k A),
    points_eq_kostantToralPointsSubgroup, points_eq_kostantToralPointsSubgroup,
    ← map_subtype_fixedSubgroup_kostantToralFrobenius]
  exact map_subtype_fixedSubgroup_kostantToralFrobenius_eq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) p k A

end

end TauCeti.TypeDSpinCarrier
