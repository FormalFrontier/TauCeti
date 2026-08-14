/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.Characteristic

/-!
# The characteristic weight function of a plumbing lattice

This file adds the integer-valued quadratic weight attached to a characteristic covector on the
integral lattice of a plumbing graph. For a characteristic covector `k` and a lattice point
`x : V → ℤ`, the numerator

`∑ v, k v * x v + P.intersectionForm x x`

is even, so the lattice-homology weight

`-(∑ v, k v * x v + P.intersectionForm x x) / 2`

is an integer. This is the local `χ_k(x)` function used in the lattice-homology lane before the
cube weights and `ℤ[U]` complexes are introduced.

The numerator is defined for arbitrary covectors, while the weight itself is restricted to
characteristic covectors so that the division by `2` has the expected integer meaning.

## Main definitions

* `TauCeti.PlumbingGraph.characteristicWeightNumerator`: the even numerator
  `⟨k, x⟩ + x · x`.
* `TauCeti.PlumbingGraph.characteristicWeight`: the integer weight `χ_k(x)` for characteristic
  covectors.

## Main results

* `TauCeti.PlumbingGraph.even_characteristicWeightNumerator`: characteristicness makes the
  numerator even.
* `TauCeti.PlumbingGraph.two_mul_characteristicWeight`: the defining equation
  `2 * χ_k(x) = - (⟨k, x⟩ + x · x)`.
* `TauCeti.PlumbingGraph.characteristicWeight_add_two_mul`: shifting a covector by `2l`
  subtracts `⟨l, x⟩` from the weight.
* `TauCeti.PlumbingGraph.characteristicWeight_canonical_single`: the canonical characteristic
  covector gives weight `1` on each basis sphere.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening data asks for plumbing graphs, their lattices, characteristic
covectors, and weight functions. The convention `χ_k(x) = -(k(x) + x · x) / 2` follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- The numerator of the characteristic weight function:
`⟨k, x⟩ + x · x`, where `x · x` is the plumbing intersection form. For a characteristic covector
`k`, this numerator is even; see `even_characteristicWeightNumerator`. -/
noncomputable def characteristicWeightNumerator (k x : V → ℤ) : ℤ :=
  (∑ v, k v * x v) + P.intersectionForm x x

/-- The numerator of the characteristic weight function, expanded as the defining sum. -/
private theorem characteristicWeightNumerator_def_aux (k x : V → ℤ) :
    P.characteristicWeightNumerator k x = (∑ v, k v * x v) + P.intersectionForm x x :=
  rfl

/-- The numerator of the characteristic weight function, expanded as the defining sum. -/
theorem characteristicWeightNumerator_def (k x : V → ℤ) :
    P.characteristicWeightNumerator k x = (∑ v, k v * x v) + P.intersectionForm x x :=
  characteristicWeightNumerator_def_aux P k x

/-- The characteristic-weight numerator is even when `k` is characteristic. This is the
integer-valuedness input for the lattice-homology weight function. -/
theorem even_characteristicWeightNumerator {k : V → ℤ} (hk : P.IsCharacteristicVector k)
    (x : V → ℤ) : Even (P.characteristicWeightNumerator k x) := by
  have hmod :
      (∑ v, k v * x v) ≡ P.intersectionForm x x [ZMOD 2] :=
    (P.isCharacteristicVector_iff_forall_modEq_intersectionForm k).mp hk x
  have hdvd : (2 : ℤ) ∣ P.intersectionForm x x - ∑ v, k v * x v :=
    Int.modEq_iff_dvd.mp hmod
  obtain ⟨m, hm⟩ := hdvd
  refine even_iff_two_dvd.mpr ⟨m + ∑ v, k v * x v, ?_⟩
  calc
    P.characteristicWeightNumerator k x =
        (P.intersectionForm x x - ∑ v, k v * x v) + 2 * ∑ v, k v * x v := by
      rw [characteristicWeightNumerator_def]
      ring
    _ = 2 * (m + ∑ v, k v * x v) := by
      rw [hm]
      ring

/-- The characteristic-weight expression obtained by integer-dividing
`-(⟨k, x⟩ + x · x)` by `2`. For a characteristic covector, the numerator is even by
`even_characteristicWeightNumerator`, and `two_mul_characteristicWeight` states its exact
doubling equation. -/
noncomputable def characteristicWeight (k : P.characteristicVectors) (x : V → ℤ) : ℤ :=
  -(P.characteristicWeightNumerator k.val x / 2)

/-- The characteristic weight as the negative half of its numerator. -/
private theorem characteristicWeight_def_aux (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicWeight k x = -(P.characteristicWeightNumerator k.val x / 2) :=
  rfl

/-- The characteristic weight as the negative half of its numerator. -/
theorem characteristicWeight_def (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicWeight k x = -(P.characteristicWeightNumerator k.val x / 2) :=
  characteristicWeight_def_aux P k x

/-- The defining equation for the integer-valued characteristic weight. -/
theorem two_mul_characteristicWeight (k : P.characteristicVectors) (x : V → ℤ) :
    2 * P.characteristicWeight k x = -P.characteristicWeightNumerator k.val x := by
  have hdvd : (2 : ℤ) ∣ P.characteristicWeightNumerator k.val x :=
    even_iff_two_dvd.mp (P.even_characteristicWeightNumerator k.property x)
  have hcancel : P.characteristicWeightNumerator k.val x / 2 * 2 =
      P.characteristicWeightNumerator k.val x :=
    Int.ediv_mul_cancel hdvd
  rw [characteristicWeight_def]
  linarith

/-- The characteristic weight at the zero lattice point is zero. -/
@[simp]
theorem characteristicWeight_zero (k : P.characteristicVectors) :
    P.characteristicWeight k 0 = 0 := by
  rw [characteristicWeight_def, characteristicWeightNumerator_def]
  rw [map_zero]
  simp

/-- The numerator is additive in its covector argument: shifting `k` by `l` adds the linear
pairing `⟨l, x⟩`. -/
theorem characteristicWeightNumerator_add (k l x : V → ℤ) :
    P.characteristicWeightNumerator (fun v => k v + l v) x =
      P.characteristicWeightNumerator k x + ∑ v, l v * x v := by
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- The numerator for a covector shifted by twice another covector. -/
theorem characteristicWeightNumerator_add_two_mul (k l x : V → ℤ) :
    P.characteristicWeightNumerator (fun v => k v + 2 * l v) x =
      P.characteristicWeightNumerator k x + 2 * ∑ v, l v * x v := by
  rw [P.characteristicWeightNumerator_add k (fun v => 2 * l v) x, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- Shifting a covector by `2l` subtracts the linear pairing `⟨l, x⟩` from the
characteristic weight. -/
theorem characteristicWeight_add_two_mul (k : P.characteristicVectors) (l x : V → ℤ) :
    P.characteristicWeight ⟨fun v => k.val v + 2 * l v, k.property.add_two_mul⟩ x =
      P.characteristicWeight k x - ∑ v, l v * x v := by
  rw [characteristicWeight_def, characteristicWeight_def,
    characteristicWeightNumerator_add_two_mul]
  rw [Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]
  ring

/-- The numerator of any covector on a plumbing basis sphere is the covector coordinate plus the
sphere weight. -/
@[simp]
theorem characteristicWeightNumerator_single (k : V → ℤ) (v : V) :
    P.characteristicWeightNumerator k (Pi.single v 1) = k v + P.weight v := by
  rw [characteristicWeightNumerator_def, intersectionForm_single, intersectionMatrix_diag]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- The numerator of the canonical characteristic covector on a basis sphere is `-2`. -/
theorem characteristicWeightNumerator_canonical_single (v : V) :
    P.characteristicWeightNumerator P.canonicalCharacteristic (Pi.single v 1) = -2 := by
  rw [characteristicWeightNumerator_single]
  simpa [intersectionForm_single, intersectionMatrix_diag] using
    P.canonicalCharacteristic_apply_add_intersection_single v

/-- The characteristic weight of any characteristic covector on a plumbing basis sphere. -/
theorem characteristicWeight_single (k : P.characteristicVectors) (v : V) :
    P.characteristicWeight k (Pi.single v 1) = -((k.val v + P.weight v) / 2) := by
  rw [characteristicWeight_def, characteristicWeightNumerator_single]

/-- The canonical characteristic covector has characteristic weight `1` on each basis sphere. -/
@[simp]
theorem characteristicWeight_canonical_single (v : V) :
    P.characteristicWeight
      ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩
      (Pi.single v 1) = 1 := by
  rw [characteristicWeight_def, characteristicWeightNumerator_canonical_single]
  norm_num

end PlumbingGraph

end TauCeti
