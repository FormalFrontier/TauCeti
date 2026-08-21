/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight.Basic

/-!
# Conjugation symmetry of the plumbing-lattice weight function

The spin^c structures of a plumbed three-manifold are encoded by characteristic covectors of the
plumbing lattice, and spin^c **conjugation** acts by negating the covector. The involution itself,
`PlumbingGraph.conjugate`, lives at the characteristic-covector layer in `Characteristic.lean`;
this file proves its compatibility with the characteristic weight function `χ_k(x)` from
`Weight.lean`: conjugating the covector while negating the lattice point leaves the weight
unchanged,

`χ_{-k}(-x) = χ_k(x)`,

the symmetry that descends to the conjugation involution on Némethi's lattice homology. Together
with the linear relation `χ_{-k}(x) + χ_k(x) = -(x · x)` it pins down how the conjugate weight is
obtained from the original.

The underlying identities are purely about the numerator `⟨k, x⟩ + x · x`: negating both
arguments fixes it, while negating only the covector reflects it through `2 (x · x)`. These hold
for arbitrary covectors and are stated first; the weight statements then follow from the doubling
equation `two_mul_characteristicWeight`, with no integer division to discharge.

## Main results

* `TauCeti.PlumbingGraph.characteristicWeightNumerator_neg_neg`: negating both arguments fixes the
  weight numerator.
* `TauCeti.PlumbingGraph.characteristicWeightNumerator_neg_left`: negating only the covector
  reflects the numerator through `2 (x · x)`.
* `TauCeti.PlumbingGraph.characteristicWeight_conjugate_neg`: the conjugation symmetry
  `χ_{-k}(-x) = χ_k(x)`.
* `TauCeti.PlumbingGraph.characteristicWeight_conjugate_add`: the linear relation
  `χ_{-k}(x) + χ_k(x) = -(x · x)`.
* `TauCeti.PlumbingGraph.characteristicWeight_conjugate_canonical_single`: the conjugate
  canonical weight on a plumbing basis sphere.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose programme includes the conjugation symmetry of the weight function and
the resulting involution of lattice homology. The convention follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} (P : PlumbingGraph V)

section Form

variable [DecidableEq V] [Fintype V]

/-- Negating both the covector and the lattice point fixes the weight numerator: each linear term
`k v * x v` is unchanged and the quadratic term `x · x` is even in `x`. -/
@[simp]
theorem characteristicWeightNumerator_neg_neg (k x : V → ℤ) :
    P.characteristicWeightNumerator (-k) (-x) = P.characteristicWeightNumerator k x := by
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Pi.neg_apply, neg_mul_neg]
  · simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- Negating only the covector reflects the weight numerator through `2 (x · x)`: the quadratic
term is untouched while the linear term changes sign. -/
theorem characteristicWeightNumerator_neg_left (k x : V → ℤ) :
    P.characteristicWeightNumerator (-k) x =
      2 * P.intersectionForm x x - P.characteristicWeightNumerator k x := by
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def]
  have hsum : (∑ v, (-k) v * x v) = -∑ v, k v * x v := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hsum]
  ring

/-- **Conjugation symmetry of the lattice weight.** Conjugating the covector and negating the
lattice point leaves the characteristic weight unchanged: `χ_{-k}(-x) = χ_k(x)`. This is the
identity behind the conjugation involution of lattice homology. -/
@[simp]
theorem characteristicWeight_conjugate_neg (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicWeight (P.conjugate k) (-x) = P.characteristicWeight k x := by
  have h2 : 2 * P.characteristicWeight (P.conjugate k) (-x) =
      2 * P.characteristicWeight k x := by
    rw [two_mul_characteristicWeight, two_mul_characteristicWeight, conjugate_val,
      characteristicWeightNumerator_neg_neg]
  omega

/-- The conjugate and original weights at a fixed lattice point sum to `-(x · x)`: a linear
relation expressing the conjugate weight through the intersection form. -/
theorem characteristicWeight_conjugate_add (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicWeight (P.conjugate k) x + P.characteristicWeight k x =
      -P.intersectionForm x x := by
  have h2 : 2 * (P.characteristicWeight (P.conjugate k) x + P.characteristicWeight k x) =
      2 * -P.intersectionForm x x := by
    rw [mul_add, two_mul_characteristicWeight, two_mul_characteristicWeight, conjugate_val,
      characteristicWeightNumerator_neg_left]
    ring
  omega

/-- The conjugate of the canonical characteristic covector has weight `-P.weight v - 1` on the
plumbing basis sphere at `v`. -/
@[simp]
theorem characteristicWeight_conjugate_canonical_single (v : V) :
    P.characteristicWeight
      (P.conjugate ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩)
      (Pi.single v 1) = -P.weight v - 1 := by
  rw [characteristicWeight_single, conjugate_val]
  simp only [Pi.neg_apply, canonicalCharacteristic_apply]
  omega

end Form

end PlumbingGraph

end TauCeti
