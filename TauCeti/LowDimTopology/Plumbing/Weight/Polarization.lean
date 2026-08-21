/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight.Basic

/-!
# The polarization identity for the plumbing-lattice weight function

Némethi's local weight function `χ_k(x) = -(⟨k, x⟩ + x · x) / 2` is a quadratic function of the
lattice point `x`, whose associated symmetric bilinear form is the negated intersection form. This
file records that quadratic behaviour as a polarization identity: for a characteristic covector `k`
and lattice points `x`, `y`,

`χ_k(x + y) = χ_k(x) + χ_k(y) - x · y`.

The single-direction specialization `y = E_v` is the first-difference recursion that drives the
cube-weight comparisons of Némethi's lattice homology: moving one lattice step in the basis
direction `v` changes the weight by `χ_k(E_v)` minus the pairing of the current point against the
`v`-th sphere.

## Main results

* `TauCeti.PlumbingGraph.characteristicWeightNumerator_add_right`: the weight numerator is quadratic
  in the lattice point, gaining `2 (x · y)` on a sum.
* `TauCeti.PlumbingGraph.characteristicWeight_add`: the polarization identity for `χ_k`.
* `TauCeti.PlumbingGraph.characteristicWeight_add_single`: the first-difference recursion of `χ_k`
  along a basis direction.
* `TauCeti.PlumbingGraph.characteristicWeight_single_add_single`: the value of `χ_k` on a sum of two
  basis spheres in terms of their intersection-matrix entry.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose weight functions are "built from these covectors and the plumbing intersection form" and
whose cube weights obey a first-difference recursion. The convention
`χ_k(x) = -(⟨k, x⟩ + x · x) / 2` and its quadratic behaviour follow Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- The characteristic-weight numerator is quadratic in the lattice point: on a sum it gains twice
the intersection pairing of the two summands. -/
theorem characteristicWeightNumerator_add_right (k x y : V → ℤ) :
    P.characteristicWeightNumerator k (x + y) =
      P.characteristicWeightNumerator k x + P.characteristicWeightNumerator k y +
        2 * P.intersectionForm x y := by
  have hlin : (∑ w, k w * (x + y) w) = (∑ w, k w * x w) + ∑ w, k w * y w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [Pi.add_apply]; ring
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def,
    characteristicWeightNumerator_def, P.intersectionForm_self_add x y, hlin]
  ring

/-- The polarization identity for Némethi's weight function: `χ_k` is quadratic, with associated
symmetric bilinear form the negated intersection form. -/
theorem characteristicWeight_add (k : P.characteristicVectors) (x y : V → ℤ) :
    P.characteristicWeight k (x + y) =
      P.characteristicWeight k x + P.characteristicWeight k y - P.intersectionForm x y := by
  have h : (2 : ℤ) * P.characteristicWeight k (x + y) =
      2 * (P.characteristicWeight k x + P.characteristicWeight k y -
        P.intersectionForm x y) := by
    rw [two_mul_characteristicWeight, characteristicWeightNumerator_add_right,
      mul_sub, mul_add, two_mul_characteristicWeight, two_mul_characteristicWeight]
    ring
  exact mul_left_cancel₀ (by norm_num) h

/-- The first-difference recursion of `χ_k` along a basis direction: taking one lattice step in the
direction `v` subtracts `(k_v + weight v) / 2` and the pairing of the current point against the
`v`-th sphere. This is the step that drives the cube-weight comparisons of lattice homology. -/
@[simp]
theorem characteristicWeight_add_single (k : P.characteristicVectors) (x : V → ℤ) (v : V) :
    P.characteristicWeight k (x + Pi.single v 1) =
      P.characteristicWeight k x - ((k.val v + P.weight v) / 2) -
        ∑ i, x i * P.intersectionMatrix i v := by
  rw [characteristicWeight_add, characteristicWeight_single, P.intersectionForm_single_right x v]
  ring

/-- The value of `χ_k` on a sum of two basis spheres, with the interaction term given by their
intersection-matrix entry: for adjacent spheres this entry is `1`, otherwise `0` off-diagonal. -/
theorem characteristicWeight_single_add_single (k : P.characteristicVectors) (v w : V) :
    P.characteristicWeight k (Pi.single v 1 + Pi.single w 1) =
      P.characteristicWeight k (Pi.single v 1) + P.characteristicWeight k (Pi.single w 1) -
        P.intersectionMatrix v w := by
  rw [characteristicWeight_add, intersectionForm_single]

end PlumbingGraph

/-- A self-validating check on the `A₂` plumbing: the canonical characteristic covector gives weight
`1` on each of the two adjacent spheres, and the polarization identity delivers
`χ(E₀ + E₁) = 1 + 1 - 1 = 1`, the interaction term being the single adjacency. -/
example :
    a2Plumbing.characteristicWeight
        ⟨a2Plumbing.canonicalCharacteristic,
          a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩
        (Pi.single 0 1 + Pi.single 1 1) = 1 := by
  rw [PlumbingGraph.characteristicWeight_single_add_single,
    PlumbingGraph.characteristicWeight_canonical_single,
    PlumbingGraph.characteristicWeight_canonical_single, a2Plumbing_intersectionMatrix]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end TauCeti
