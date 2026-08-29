/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.GraphAutomorphism

/-!
# The graph-twisted Frobenius of the full-weight type-A carrier

`TauCeti.SlStd.groupScheme r` is the explicit full-weight Chevalley carrier of type `A_r`, and its
point group over a commutative ring `A` of exponential characteristic `p` carries two pinned
endomorphisms: the `p ^ k`-power Frobenius `TauCeti.SlStd.frobenius`, which raises every matrix
entry to its `p ^ k`-th power, and the graph automorphism
`TauCeti.SlStd.graphAutomorphismPoints`, which is signed reverse inverse transpose. This file
composes them into

```text
twistedFrobenius = γ ∘ Frob_q,      q = p ^ k,
```

and proves the three relations that make the composite behave like the Frobenius it twists: the two
factors commute, `γ` is an involution, and consequently

```text
twistedFrobenius ∘ twistedFrobenius = Frob_(q ^ 2).
```

The commutation is not a computation about the carrier: signed reverse inverse transpose is defined
by matrices with entries `0` and `±1`, so it is natural in the coefficient ring, and the Frobenius
is the entrywise action of a ring endomorphism of that same coefficient ring.

The square relation has an arithmetic reading. Every point fixed by the twisted map is fixed by
`Frob_(q ^ 2)`, so its matrix entries lie in the subring of `A` fixed by the `q ^ 2`-power
Frobenius. That subring is a field of `q ^ 2` elements only under hypotheses none of the statements
below assume: `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`. Under those hypotheses,
and for `2 ≤ r`, it is the usual statement that the twisted family of type `A` at parameter `q` has
a matrix realization over `𝔽_{q ^ 2}` while its Frobenius parameter is `q`. At the other permitted
parameters the reading fails; at `k = 0` the exponent `q ^ 2` is `1` and the fixed subring is all
of `A`. Only the containment is proved; no reverse containment is claimed, and nothing here
asserts that either fixed group is finite, is perfect, or is simple.

The value ring is taken in `Type`, matching `TauCeti.SlStd.graphAutomorphismPoints`. That is
inherited rather than chosen here: the coordinate automorphism the graph automorphism descends from
is recovered through the full faithfulness of the points functor on `CommAlgCat.{0} ℤ`, so
`TauCeti.GeneralLinear.pointsMulEquiv_comp_typeAGraphCoordinateIso` and every point-level
consequence of it are stated at universe `0`. `TauCeti.SlStd.frobenius`, which is
universe-polymorphic, is specialized to that universe here.

## Main definitions

* `TauCeti.SlStd.twistedFrobenius`: the composite `γ ∘ Frob_q` on the type-`A_r` point group.

## Main results

* `TauCeti.SlStd.graphAutomorphismPoints_frobenius` and
  `TauCeti.SlStd.graphAutomorphismPoints_comp_frobenius`: the graph automorphism commutes with
  Frobenius.
* `TauCeti.SlStd.twistedFrobenius_rootSubgroupPoints` and
  `TauCeti.SlStd.twistedFrobenius_weightTorusPoints`: the equations on the pinned generating root
  subgroups and split torus, which reverse the Bourbaki numbering and raise the parameter to its
  `p ^ k`-th power.
* `TauCeti.SlStd.twistedFrobenius_twistedFrobenius` and
  `TauCeti.SlStd.twistedFrobenius_comp_self`: the square of the twisted map is the
  `p ^ (2 * k)`-power Frobenius, pointwise and as an identity of endomorphisms.
* `TauCeti.SlStd.fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius` and
  `TauCeti.SlStd.map_subtype_fixedSubgroup_twistedFrobenius_le`: its fixed points lie among the
  points over the `p ^ (2 * k)`-power Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, §11.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*, for the
  small-field convention that indexes the twisted type-`A` family by `q` rather than by `q ^ 2`.

This advances the "Pinnings" and "points over an algebraically closed field" targets in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which sets the `²A` Steinberg map to `γ₂ ∘ Frob_q` and
requires exactly `γ₂ ^ 2 = 1` together with the commutation of `γ₂` with `Frob_q`.
-/

public section

namespace TauCeti.SlStd

noncomputable section

variable (r p k : ℕ) (A : Type) [CommRing A] [ExpChar A p]

/-! ## The graph automorphism commutes with Frobenius -/

/-- **The pinned type-`A_r` graph automorphism commutes with the Frobenius endomorphism of the
carrier points.** Both act on matrices: the former by conjugated inverse transpose over the signed
reversal matrix, the latter entrywise through a ring endomorphism of the coefficients. -/
theorem graphAutomorphismPoints_frobenius (g : points r A) :
    graphAutomorphismPoints r A (frobenius r p k A g) =
      frobenius r p k A (graphAutomorphismPoints r A g) := by
  apply Subtype.ext
  simp only [coe_graphAutomorphismPoints, coe_frobenius, TauCeti.map_typeAGraphAutomorphism]

/-- The graph automorphism commutes with Frobenius, as an identity of endomorphisms. -/
theorem graphAutomorphismPoints_comp_frobenius :
    (graphAutomorphismPoints r A).toMonoidHom.comp (frobenius r p k A) =
      (frobenius r p k A).comp (graphAutomorphismPoints r A).toMonoidHom :=
  MonoidHom.ext (graphAutomorphismPoints_frobenius r p k A)

/-! ## The twisted Frobenius -/

/-- **The graph-twisted `p ^ k`-power Frobenius of the full-weight type-`A_r` carrier**, the
composite `γ ∘ Frob_q` of the pinned graph automorphism with the Frobenius endomorphism.

For `2 ≤ r`, `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Steinberg
map intended for a future construction of the twisted family `²A_r(p ^ k)`; at `r ≤ 1` the type-`A`
diagram has no nontrivial symmetry and there is no such family. None of those hypotheses are
assumed here, and nothing here asserts that the fixed group is finite or simple. -/
def twistedFrobenius : points r A →* points r A :=
  (graphAutomorphismPoints r A).toMonoidHom.comp (frobenius r p k A)

/-- The twisted Frobenius applies the Frobenius first and then the graph automorphism. -/
theorem twistedFrobenius_apply (g : points r A) :
    twistedFrobenius r p k A g = graphAutomorphismPoints r A (frobenius r p k A g) := (rfl)

/-- On matrices, the twisted Frobenius is signed reverse inverse transpose applied to the entrywise
`p ^ k`-power Frobenius. -/
theorem coe_twistedFrobenius (g : points r A) :
    (twistedFrobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      TauCeti.typeAGraphAutomorphism r A
        (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g) := by
  rw [twistedFrobenius_apply, coe_graphAutomorphismPoints, coe_frobenius]

/-! ## The pinned equations -/

/-- **The twisted Frobenius reverses the Bourbaki numbering of a numbered root subgroup and raises
its parameter to the `p ^ k`-th power.** This is the pinned equation
`γ ∘ Frob_q (x_α(t)) = x_{γ α}(t ^ q)` on the simple root subgroups. -/
@[simp]
theorem twistedFrobenius_rootSubgroupPoints (i : Fin r ⊕ Fin r) (u : Multiplicative A) :
    twistedFrobenius r p k A (rootSubgroupPoints r i A u) =
      rootSubgroupPoints r (graphRootPerm r i) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [twistedFrobenius_apply, frobenius_rootSubgroupPoints,
    graphAutomorphismPoints_rootSubgroupPoints]

/-- **The twisted Frobenius reverses the coordinates of the pinned split torus and raises each of
them to the `p ^ k`-th power.** -/
@[simp]
theorem twistedFrobenius_weightTorusPoints (s : Fin r → Aˣ) :
    twistedFrobenius r p k A (weightTorusPoints r A s) =
      weightTorusPoints r A (fun i => s i.rev ^ p ^ k) := by
  rw [twistedFrobenius_apply, frobenius_weightTorusPoints,
    graphAutomorphismPoints_weightTorusPoints]
  rfl

/-! ## The square relation -/

/-- **Applying the twisted Frobenius twice raises every matrix entry to its `p ^ (2 * k)`-th
power.** This is the relation a Steinberg map of the twisted family is required to satisfy, that a
power of it is a Frobenius; no such structure is asserted here. -/
@[simp]
theorem twistedFrobenius_twistedFrobenius (g : points r A) :
    twistedFrobenius r p k A (twistedFrobenius r p k A g) = frobenius r p (2 * k) A g := by
  rw [twistedFrobenius_apply, twistedFrobenius_apply, ← graphAutomorphismPoints_frobenius,
    graphAutomorphismPoints_graphAutomorphismPoints, two_mul, frobenius_add, MonoidHom.comp_apply]

/-- The square of the twisted Frobenius is the `p ^ (2 * k)`-power Frobenius, as an identity of
endomorphisms. -/
theorem twistedFrobenius_comp_self :
    (twistedFrobenius r p k A).comp (twistedFrobenius r p k A) = frobenius r p (2 * k) A :=
  MonoidHom.ext (twistedFrobenius_twistedFrobenius r p k A)

/-- A point fixed by the twisted Frobenius is fixed by the `p ^ (2 * k)`-power Frobenius. No
reverse containment is claimed. -/
theorem fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius :
    fixedSubgroup (twistedFrobenius r p k A) ≤ fixedSubgroup (frobenius r p (2 * k) A) := by
  have hsq : (show Monoid.End _ from twistedFrobenius r p k A) ^ 2 =
      frobenius r p (2 * k) A :=
    (pow_two (show Monoid.End _ from twistedFrobenius r p k A)).trans
      (twistedFrobenius_comp_self r p k A)
  rw [← hsq]
  exact TauCeti.fixedSubgroup_le_fixedSubgroup_pow _ 2

/-- **Every matrix entry of a point fixed by the twisted Frobenius lies in the subring fixed by the
`p ^ (2 * k)`-power Frobenius.** For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`
that subring is the field of `p ^ (2 * k)` elements; if moreover `2 ≤ r`, so that the type-`A`
diagram has a nontrivial symmetry and a twisted family exists, this is the statement that the
twisted family at Frobenius parameter `q = p ^ k` is realized by matrices over `𝔽_{q ^ 2}`. Without
those hypotheses the subring need not be a finite field; at `k = 0` it is all of `A`. -/
theorem mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self {g : points r A}
    (hg : twistedFrobenius r p k A g = g) (i j : Fin (r + 1)) :
    ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ∈ frobeniusFixedSubring A p (2 * k) := by
  refine (frobenius_eq_self_iff r p (2 * k) A g).mp ?_ i j
  exact fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius r p k A
    (mem_fixedSubgroup.mpr hg)

/-- **The points fixed by the twisted Frobenius lie among the points of the same carrier over the
`p ^ (2 * k)`-power Frobenius-fixed subring.** The corresponding statement for the Frobenius itself,
`TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq`, is an equality; here only the containment
holds. -/
theorem map_subtype_fixedSubgroup_twistedFrobenius_le :
    (fixedSubgroup (twistedFrobenius r p k A)).map (points r A).subtype ≤
      (points r ↥(frobeniusFixedSubring A p (2 * k))).map
        (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p (2 * k)).subtype) := by
  rw [← map_subtype_fixedSubgroup_frobenius_eq r p (2 * k) A]
  exact Subgroup.map_mono (fixedSubgroup_twistedFrobenius_le_fixedSubgroup_frobenius r p k A)

end

end TauCeti.SlStd
