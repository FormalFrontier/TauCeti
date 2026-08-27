/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import TauCeti.LinearAlgebra.RootSystem.Positive

public section

/-!
# The Weyl denominator

The **Weyl denominator** of a base of a root pairing is the element `Δ = ∏_{α > 0} (1 - e^{-α})`
of the integral group algebra `ℤ[M]` of the weight space. It is one of the two universal elements
that the Weyl character formula compares, the other being the Weyl numerator
`TauCeti.weylNumerator`; the formula is the identity `ch L(λ) · Δ = N(λ)` in `ℤ[M]`.

This normalization is the one all of whose exponents lie in the weight lattice `M`. The symmetric
form `∏_{α>0} (e^{α/2} - e^{-α/2})` is `e^{ρ}` times this one and needs the half-roots `α/2`,
which need not belong to `M` — nothing in the hypotheses below makes a root divisible by two.

Only the positive roots of the base enter, so the denominator asks for far less than the numerator
does: neither the crystallographic nor the reduced hypothesis, nor an invertible `2`, only what
`TauCeti.posRootsFinset` needs. That is why it lives in this file rather than beside the numerator,
whose Weyl-group combinatorics is a much later dependency.

## Main definitions

* `TauCeti.weylDenominator`: `Δ = ∏_{α > 0} (1 - e^{-α})`, an element of `ℤ[M]`.

## Main results

* `TauCeti.weylDenominator_eq_sum_powerset`: expanding the product, `Δ` is the signed sum
  `∑_{T ⊆ Φ⁺} (-1)^{|T|} e^{-∑_{α ∈ T} α}` over the subsets of the positive roots; hence
* `TauCeti.coeff_weylDenominator_eq_zero`: `Δ` is supported on the negatives of the sums of sets of
  positive roots, which is the statement that it lives in the negative cone.

## References

This builds the `weylDenominator` target of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 6 ("the character,
dimension, and Kostant formulas"), whose `Suggested.lean` pins it on `Module.Dual K H` for the root
system of a Cartan subalgebra. As with `TauCeti.weylVector`, the combinatorics lives at the level
of an abstract root pairing, so the Lie-algebra target is a specialization rather than a rebuild.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

/-- **The Weyl denominator** `Δ = ∏_{α > 0} (1 - e^{-α})` of a base, an element of the integral
group algebra of the weight space.

This is the normalization all of whose exponents lie in the weight lattice; the symmetric form
`∏_{α>0} (e^{α/2} - e^{-α/2})` is `e^{ρ}` times this one and needs the half-roots `α/2`, which
need not lie in `M`. -/
noncomputable def weylDenominator : AddMonoidAlgebra ℤ M :=
  ∏ i ∈ posRootsFinset P b, (1 - AddMonoidAlgebra.single (-P.root i) 1)

/-- `Δ` is the product of `1 - e^{-α}` over the positive roots, by definition. -/
lemma weylDenominator_def : weylDenominator P b =
    ∏ i ∈ posRootsFinset P b, (1 - AddMonoidAlgebra.single (-P.root i) 1) := by
  rw [weylDenominator]

/-- **The Weyl denominator, expanded.** Multiplying out `∏_{α>0} (1 - e^{-α})` indexes the terms by
the subsets `T` of the positive roots, the term of `T` being `(-1)^{|T|} e^{-∑_{α ∈ T} α}`.

Every exponent occurring is therefore minus a sum of positive roots, which is the statement that
`Δ` lives in the negative cone; `TauCeti.coeff_weylDenominator_eq_zero` reads that off. -/
theorem weylDenominator_eq_sum_powerset :
    weylDenominator P b =
      ∑ T ∈ (posRootsFinset P b).powerset,
        AddMonoidAlgebra.single (-∑ i ∈ T, P.root i) ((-1) ^ T.card) := by
  classical
  rw [weylDenominator_def, Finset.prod_sub]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  have hpow : (-1 : AddMonoidAlgebra ℤ M) ^ T.card
      = AddMonoidAlgebra.single 0 ((-1) ^ T.card) := by
    rw [AddMonoidAlgebra.one_def, ← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.single_pow,
      smul_zero]
  simp [hpow, AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single]

/-- **The Weyl denominator is supported on the negative cone**: a coefficient of `Δ` at a weight
that is not minus the sum of a set of positive roots vanishes. -/
theorem coeff_weylDenominator_eq_zero {x : M}
    (hx : ∀ T ⊆ posRootsFinset P b, x ≠ -∑ i ∈ T, P.root i) :
    (weylDenominator P b).coeff x = 0 := by
  simp only [weylDenominator_eq_sum_powerset, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single]
  exact Finset.sum_eq_zero fun T hT ↦ Finsupp.single_apply_eq_zero.mpr fun h ↦
    absurd h (hx T (Finset.mem_powerset.mp hT))

end TauCeti
