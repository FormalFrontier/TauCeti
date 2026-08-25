/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight.Polarization

/-!
# Spin^c translation equivariance of the plumbing-lattice weight function

Némethi's lattice homology is built from the local weight function `χ_k(x)` for a characteristic
covector `k` and lattice point `x`. Two characteristic covectors index the *same* spin^c structure
exactly when they differ by an element of `2 · A(V)`, where `A` is the intersection form: the
covectors `k` and `k + 2 · A l` for `l : V → ℤ` are two representatives of one spin^c structure.
The lattice homology attached to the two representatives must agree, and the isomorphism between
them is the translation of the lattice argument by `l`.

This file proves the weight-level statement underlying that isomorphism: shifting the covector by
`2 · A l` translates the weight function by `l`, up to the additive constant `χ_k(l)`,

`χ_{k + 2·A l}(x) = χ_k(x + l) - χ_k(l)`.

The proof combines the covector-shift formula `characteristicWeight_add_two_mul` (`Weight.lean`)
with the polarization identity `characteristicWeight_add` (`WeightPolarization.lean`): both sides
reduce to `χ_k(x) - A(x, l)`. Reading the identity through the weight grading, the sublevel sets of
the two representatives correspond under the `l`-translation with a constant grading shift, which is
exactly the degree-preserving bijection of cubical generators that the spin^c invariance of lattice
homology uses.

## Main results

* `TauCeti.PlumbingGraph.characteristicWeight_add_two_mulVec`: shifting the covector by `2 · A l`
  subtracts the intersection pairing `A(x, l)` from the weight.
* `TauCeti.PlumbingGraph.characteristicWeight_add_two_mulVec_eq_sub`: the translation equivariance
  `χ_{k + 2·A l}(x) = χ_k(x + l) - χ_k(l)`.
* `TauCeti.PlumbingGraph.characteristicWeight_add_two_mulVec_le_iff`: the sublevel sets of the two
  spin^c representatives correspond under the `l`-translation, with the constant grading shift
  `χ_k(l)`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose weight functions are built from the covectors and the plumbing intersection form and whose
spin^c structures are the characteristic covectors modulo `2 · A(V)`. The equivariance
`χ_{k + 2·A l}(x) = χ_k(x + l) - χ_k(l)` is the weight-level form of the translation isomorphism
between representatives of a spin^c structure; see Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- Shifting a characteristic covector by `2 · A l`, the covector representing the same spin^c
structure translated by `l`, subtracts the intersection pairing `A(x, l)` from the weight. This is
the covector-shift half of the translation equivariance. -/
theorem characteristicWeight_add_two_mulVec (k : P.characteristicVectors) (m x : V → ℤ) :
    P.characteristicWeight
        ⟨fun v => k.val v + 2 * (P.intersectionMatrix.mulVec m) v, k.property.add_two_mul⟩ x =
      P.characteristicWeight k x - P.intersectionForm x m := by
  rw [characteristicWeight_add_two_mul, sum_intersectionMatrix_mulVec_mul]

/-- Spin^c translation equivariance of Némethi's weight function: shifting the characteristic
covector by `2 · A l` translates the weight by `l`, up to the additive constant `χ_k(l)`,

`χ_{k + 2·A l}(x) = χ_k(x + l) - χ_k(l)`.

The two representatives `k` and `k + 2·A l` of one spin^c structure therefore have weight functions
that agree after translating the lattice argument by `l`; this is the weight-level statement behind
the translation isomorphism of the associated lattice homologies. -/
theorem characteristicWeight_add_two_mulVec_eq_sub (k : P.characteristicVectors) (m x : V → ℤ) :
    P.characteristicWeight
        ⟨fun v => k.val v + 2 * (P.intersectionMatrix.mulVec m) v, k.property.add_two_mul⟩ x =
      P.characteristicWeight k (x + m) - P.characteristicWeight k m := by
  rw [characteristicWeight_add_two_mulVec, characteristicWeight_add]
  ring

/-- The sublevel sets of two spin^c representatives correspond under the `l`-translation, with a
constant grading shift by `χ_k(l)`: a point `x` has shifted-covector weight at most `n` exactly when
its `l`-translate has original weight at most `n + χ_k(l)`. This is the degree-preserving bijection
of cubical generators underlying the spin^c invariance of lattice homology. -/
theorem characteristicWeight_add_two_mulVec_le_iff (k : P.characteristicVectors) (m x : V → ℤ)
    (n : ℤ) :
    P.characteristicWeight
        ⟨fun v => k.val v + 2 * (P.intersectionMatrix.mulVec m) v, k.property.add_two_mul⟩ x ≤ n ↔
      P.characteristicWeight k (x + m) ≤ n + P.characteristicWeight k m := by
  rw [characteristicWeight_add_two_mulVec_eq_sub]
  omega

end PlumbingGraph

/-- A self-validating check on the `A₂` plumbing exercising
`characteristicWeight_add_two_mulVec_eq_sub` at the shift `m = E₀`, point `x = E₁`, and canonical
covector `k`. The theorem reduces the
shifted-covector weight `χ_{k + 2·A E₀}(E₁)` to the translate `χ_k(E₁ + E₀) - χ_k(E₀)`, which
evaluates to `1 - 1 = 0`. -/
example :
    a2Plumbing.characteristicWeight
        ⟨fun v => a2Plumbing.canonicalCharacteristic v +
            2 * (a2Plumbing.intersectionMatrix.mulVec (Pi.single (0 : Fin 2) 1)) v,
          a2Plumbing.isCharacteristicVector_canonicalCharacteristic.add_two_mul⟩
        (Pi.single (1 : Fin 2) 1) = 0 := by
  have translate :
      a2Plumbing.characteristicWeight
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩
          (Pi.single (1 : Fin 2) 1 + Pi.single 0 1)
        - a2Plumbing.characteristicWeight
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩
          (Pi.single 0 1) = 0 := by
    rw [PlumbingGraph.characteristicWeight_single_add_single,
      PlumbingGraph.characteristicWeight_canonical_single,
      PlumbingGraph.characteristicWeight_canonical_single, a2Plumbing_intersectionMatrix]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact (a2Plumbing.characteristicWeight_add_two_mulVec_eq_sub
    ⟨a2Plumbing.canonicalCharacteristic,
      a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩
    (Pi.single 0 1) (Pi.single 1 1)).trans translate

end TauCeti
