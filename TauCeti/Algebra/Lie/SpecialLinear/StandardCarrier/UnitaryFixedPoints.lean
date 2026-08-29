/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius

/-!
# The points of the type-A carrier fixed by the graph-twisted Frobenius

`TauCeti.SlStd.twistedFrobenius r p k A` is the composite `γ ∘ Frob_q` of the pinned type-`A_r`
graph automorphism with the entrywise `q`-power Frobenius, `q = p ^ k`. This file identifies the
points it fixes by a single matrix equation. Writing `Q` for the signed reversal matrix
`TauCeti.typeAGraphConjugator r A` and `g^{(q)}` for the entrywise `q`-th power of `g`, a carrier
point is fixed exactly when

```text
g * Q * (g^{(q)})ᵀ = Q,      equivalently      (g^{(q)})ᵀ * Q * g = Q,
```

the second being the classical unitarity condition `g* Q g = Q` for the `q`-power-sesquilinear
form of Gram matrix `Q`, with `g* = (g^{(q)})ᵀ`. So the fixed group is the group of `Q`-unitary
carrier points, and `TauCeti.SlStd.mem_map_subtype_fixedSubgroup_twistedFrobenius_iff` states that
description as a membership criterion inside `GL_{r+1}(A)`.

For `p` prime, `0 < k`, `2 ≤ r`, and `A` an algebraic closure of `ZMod p`, that is the usual
matrix realization of the twisted family `²A_r(q)`: the already available
`TauCeti.SlStd.mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self` puts the entries of a fixed
point in the field of `q ^ 2` elements, and the equation here is unitarity with respect to the
`q`-power involution of that field. None of those hypotheses are assumed below, and nothing here
asserts that the fixed group is finite, is perfect, or is simple, nor that it agrees with any other
construction of a unitary group.

Mathlib's `Matrix.unitaryGroup` is not the object described here and is not available for it: it is
the unitary group of the conjugate-transpose involution supplied by a `StarRing` structure on the
coefficients, whereas the involution here is the `q`-power ring endomorphism of a ring of
exponential characteristic `p`, which carries no such structure, and the Gram matrix is the pinned
`Q` rather than the identity.

The last two results record that the pinned generators of the carrier lie in the fixed group under
the expected numerical conditions, so the group is not described vacuously: a torus point is fixed
when its coordinates are exchanged by the `q`-power map along the reversal of the Bourbaki
numbering, and a root-subgroup point is fixed when it sits at a node fixed by that reversal and its
parameter is fixed by the `q`-power map.

## Main results

* `TauCeti.SlStd.twistedFrobenius_eq_self_iff` and
  `TauCeti.SlStd.twistedFrobenius_eq_self_iff_transpose`: a carrier point is fixed by the
  graph-twisted Frobenius exactly when it is unitary for the pinned `q`-power-sesquilinear form.
* `TauCeti.SlStd.mem_map_subtype_fixedSubgroup_twistedFrobenius_iff`: the same description of the
  fixed group as a subgroup of the ambient general linear group.
* `TauCeti.SlStd.twistedFrobenius_weightTorusPoints_eq_self` and
  `TauCeti.SlStd.twistedFrobenius_rootSubgroupPoints_eq_self`: pinned points of the fixed group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 14, for the unitary description of the fixed
  points of a graph-twisted Steinberg map in type `A`.
* R. Steinberg, *Lectures on Chevalley Groups*, §11.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*, for the
  small-field convention that indexes the twisted type-`A` family by `q` rather than by `q ^ 2`.

This advances the "points over an algebraically closed field" target of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, by describing the group of points fixed by the induced
endomorphism the previous file constructed. Its consumer is milestone L3 of
`TauCetiRoadmap/CFSGStatement/README.md`, which sets `H_d = fixedSubgroup d.steinberg` with
`d.steinberg` the map `γ₂ ∘ Frob_q` of milestone L1 on the `²A` branch; the equation proved here is
what lets a reader of that branch see which matrices `H_d` contains.
-/

public section

namespace TauCeti.SlStd

noncomputable section

variable (r p k : ℕ) (A : Type) [CommRing A] [ExpChar A p]

/-! ## The unitary description of the fixed points -/

-- The point-level Frobenius is entrywise exponentiation; this is the form the invariance equation
-- of `TauCeti.typeAGraphAutomorphism_eq_iff` is stated in.
private theorem coe_map_iterateFrobenius (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    ((Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g :
          Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k) := (rfl)

/-- **A type-`A_r` carrier point is fixed by the graph-twisted Frobenius exactly when it preserves
the pinned `q`-power-sesquilinear form**, `q = p ^ k`, whose Gram matrix is the signed reversal
matrix `TauCeti.typeAGraphConjugator`.

`TauCeti.SlStd.map_subtype_fixedSubgroup_twistedFrobenius_le` places a fixed point among the
points over the `q ^ 2`-power Frobenius-fixed subring and claims no reverse containment; the
equation here says exactly which carrier points are fixed. -/
@[simp]
theorem twistedFrobenius_eq_self_iff (g : points r A) :
    twistedFrobenius r p k A g = g ↔
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
                Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k)).transpose =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [Subtype.ext_iff, coe_twistedFrobenius, typeAGraphAutomorphism_eq_iff,
    coe_map_iterateFrobenius]

/-- **A type-`A_r` carrier point is fixed by the graph-twisted Frobenius exactly when it is
unitary for the pinned `q`-power-sesquilinear form**, `q = p ^ k`: writing `g*` for the transpose
of the entrywise `q`-th power of `g`, the condition is `g* * Q * g = Q`.

This is the classical form of the condition; `TauCeti.SlStd.twistedFrobenius_eq_self_iff` is the
same condition with the two outer factors exchanged, which is the form the graph automorphism
produces directly. -/
theorem twistedFrobenius_eq_self_iff_transpose (g : points r A) :
    twistedFrobenius r p k A g = g ↔
      (((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
                Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k)).transpose *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [Subtype.ext_iff, coe_twistedFrobenius, typeAGraphAutomorphism_eq_iff_transpose,
    coe_map_iterateFrobenius]

/-- **The graph-twisted Frobenius-fixed points of the full-weight type-`A_r` carrier are the
`Q`-unitary carrier points.** Read inside the ambient general linear group, membership in the fixed
group is carrier membership together with the invariance equation of
`TauCeti.SlStd.twistedFrobenius_eq_self_iff`. -/
theorem mem_map_subtype_fixedSubgroup_twistedFrobenius_iff
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ (fixedSubgroup (twistedFrobenius r p k A)).map (points r A).subtype ↔
      g ∈ points r A ∧
        (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
              (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
              ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k)).transpose =
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (twistedFrobenius_eq_self_iff r p k A x).mp (mem_fixedSubgroup.mp hx)⟩
  · rintro ⟨hmem, heq⟩
    exact ⟨⟨g, hmem⟩,
      mem_fixedSubgroup.mpr ((twistedFrobenius_eq_self_iff r p k A ⟨g, hmem⟩).mpr heq), rfl⟩

/-! ## Pinned points of the fixed group -/

/-- **A pinned torus point is fixed by the graph-twisted Frobenius when the `q`-power map exchanges
its coordinates along the reversal of the Bourbaki numbering.** -/
theorem twistedFrobenius_weightTorusPoints_eq_self {s : Fin r → Aˣ}
    (hs : ∀ i, s i.rev ^ p ^ k = s i) :
    twistedFrobenius r p k A (weightTorusPoints r A s) = weightTorusPoints r A s := by
  rw [twistedFrobenius_weightTorusPoints]
  exact congrArg (weightTorusPoints r A) (funext hs)

/-- **A pinned root-subgroup point is fixed by the graph-twisted Frobenius when its node is fixed
by the reversal of the Bourbaki numbering and its parameter is fixed by the `q`-power map.** For
`0 < r` such a node exists exactly when `r` is odd, the middle node of the diagram. -/
theorem twistedFrobenius_rootSubgroupPoints_eq_self {i : Fin r ⊕ Fin r} {u : Multiplicative A}
    (hi : graphRootPerm r i = i)
    (hu : Multiplicative.toAdd u ^ p ^ k = Multiplicative.toAdd u) :
    twistedFrobenius r p k A (rootSubgroupPoints r i A u) = rootSubgroupPoints r i A u := by
  rw [twistedFrobenius_rootSubgroupPoints, hi, hu]
  rfl

end

end TauCeti.SlStd
