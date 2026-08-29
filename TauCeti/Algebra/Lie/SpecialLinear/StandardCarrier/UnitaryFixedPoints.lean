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

the second saying that `g` is an isometry of the `q`-power-semilinear form of Gram matrix `Q`,
written `g* Q g = Q` with `g* = (g^{(q)})ᵀ`. That is the shape of the classical unitarity
condition, but two things are needed before it may be called that condition, and the generality
assumed here supplies neither.

First, the `q`-power map is only a ring endomorphism: the Frobenius of a ring of exponential
characteristic `p` need not square to the identity, and on `(ZMod p)[X]` it does not. It is an
involution on the subring fixed by the `q ^ 2`-power Frobenius, and every entry of a fixed point
lies in that subring by `TauCeti.SlStd.mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self`.

Second, the pinned Gram matrix has a parity. `Q` is the reversal matrix with alternating signs, so
transposing it reverses the sign pattern: `Qᵀ = (-1) ^ r • Q`, equivalently `Qᵀ = Q⁻¹` together
with `Q * Q = (-1) ^ r`, which is `TauCeti.typeAGraphConjugator_mul_self`. Where the `q`-power map
is an involution the form is therefore Hermitian for even `r` and skew-Hermitian for odd `r`, the
latter being Hermitian too exactly where `-1 = 1`, as in characteristic two; and
where the `q`-power map is the identity, as on `ZMod p` with `q = p`, the form is bilinear,
symmetric for even `r` and alternating for odd `r`, so that the equation is then the symplectic
condition (for `r = 3`, `A = ZMod 3` and `q = 3` it is exactly `gᵀ * Q * g = Q` for a
nondegenerate alternating form). So involutivity alone does not make the equation a unitary one.

To read the fixed group inside `GL_{r+1}(A)`, rewrite with
`TauCeti.map_subtype_fixedSubgroup_of_coe_eq` and `TauCeti.SlStd.coe_twistedFrobenius` and then
with either equivalence below.

For `p` prime, `0 < k`, `2 ≤ r`, and `A` an algebraic closure of `ZMod p`, that subring is the
field `F` of `q ^ 2` elements, on which the `q`-power map is the involution fixing the field of
`q` elements, and the equation here is the isometry equation over `F` of the Hermitian form `Q`
for even `r` and of the skew-Hermitian form `Q` for odd `r`. In the odd case the isometries are
still those of a Hermitian form: choosing `c` in `F` with `c ^ q = -c` (take `c = 1` when `q` is
even) makes `c • Q` Hermitian, and rescaling the invertible Gram matrix by a unit does not change
which matrices satisfy the equation. That is the usual unitary equation of the twisted family
`²A_r(q)`. Identifying the fixed group with that family is not done here and does not follow from
what is proved: it would need the carrier identified with `SL_{r+1}` and the derived subgroup and
central quotient taken. None of those hypotheses are assumed below, and nothing here asserts that
the fixed group is finite, is perfect, or is simple, nor that it agrees with any other
construction of a unitary group.

Mathlib's `Matrix.unitaryGroup` is not the object described here: it is the unitary group of the
conjugate-transpose involution supplied by a `StarRing` structure on the coefficients, whereas the
map here is the `q`-power ring endomorphism of a ring of exponential characteristic `p`, no
compatible `StarRing` structure on `A` is assumed, and the Gram matrix is the pinned `Q` rather
than the identity.

## Main results

* `TauCeti.SlStd.twistedFrobenius_eq_self_iff_mul_conjugator_mul_transpose_eq` and
  `TauCeti.SlStd.twistedFrobenius_eq_self_iff_transpose_mul_conjugator_mul_eq`: a carrier point is
  fixed by the graph-twisted Frobenius exactly when it is an isometry of the pinned
  `q`-power-semilinear form.

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

/-! ## The fixed points as isometries of the pinned semilinear form -/

-- The point-level Frobenius is entrywise exponentiation; this is the form the invariance equation
-- of `TauCeti.typeAGraphAutomorphism_eq_iff_mul_conjugator_mul_transpose_eq` is stated in.
private theorem coe_map_iterateFrobenius (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    ((Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g :
          Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, iterateFrobenius_def]

/-- **A type-`A_r` carrier point is fixed by the graph-twisted Frobenius exactly when it preserves
the pinned `q`-power-semilinear form**, `q = p ^ k`, whose Gram matrix is the signed reversal
matrix `TauCeti.typeAGraphConjugator`.

`TauCeti.SlStd.map_subtype_fixedSubgroup_twistedFrobenius_le` places a fixed point among the
points over the `q ^ 2`-power Frobenius-fixed subring and claims no reverse containment; the
equation here says exactly which carrier points are fixed. -/
@[simp]
theorem twistedFrobenius_eq_self_iff_mul_conjugator_mul_transpose_eq (g : points r A) :
    twistedFrobenius r p k A g = g ↔
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
                Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k)).transpose =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [Subtype.ext_iff, coe_twistedFrobenius,
    typeAGraphAutomorphism_eq_iff_mul_conjugator_mul_transpose_eq, coe_map_iterateFrobenius]

/-- **A type-`A_r` carrier point is fixed by the graph-twisted Frobenius exactly when it is an
isometry of the pinned `q`-power-semilinear form**, `q = p ^ k`: writing `g*` for the transpose of
the entrywise `q`-th power of `g`, the condition is `g* * Q * g = Q`.

This is the shape in which the classical unitarity condition is written, `g ↦ g*` being an
adjoint where the `q`-power map is an involution; since `Qᵀ = (-1) ^ r • Q`, the form there is
Hermitian for even `r` and skew-Hermitian for odd `r`, the latter being Hermitian too where
`-1 = 1`, as the module documentation records.
`TauCeti.SlStd.twistedFrobenius_eq_self_iff_mul_conjugator_mul_transpose_eq` is the same condition
with the two outer factors exchanged, which is the form the graph automorphism produces
directly. -/
theorem twistedFrobenius_eq_self_iff_transpose_mul_conjugator_mul_eq (g : points r A) :
    twistedFrobenius r p k A g = g ↔
      (((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
                Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k)).transpose *
            (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
              Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [Subtype.ext_iff, coe_twistedFrobenius,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq, coe_map_iterateFrobenius]

end

end TauCeti.SlStd
