/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.LinearCombination
public import TauCeti.LowDimTopology.Plumbing.BlowUp
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# The plumbing-lattice weight function under a blow-up

`Plumbing/BlowUp.lean` builds the first of Neumann's plumbing moves, blowing up a plumbing graph
`P` at a vertex `v`, and splits the blown-up lattice and its covectors along the exceptional class:
the total transform `blowUpVertexEquiv` identifies the blown-up lattice with `(V → ℤ) × ℤ`, under
which the intersection form becomes the orthogonal direct sum `⟨(x, s), (y, t)⟩ = ⟨x, y⟩ - s * t`,
and the dual identification `blowUpCovectorEquiv` pairs the lifted covector `(k, ε)` against the
lifted lattice point `(x, s)` as `⟨k', φ(x, s)⟩ = ⟨k, x⟩ + ε * s`. This file carries that splitting
through Némethi's weight function `χ_k`, the function whose sublevel sets filter the lattice
complex.

Combining the two splittings gives the weight formula

`2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)`

for the characteristic covector `blowUpCharacteristic` of the blow-up determined by `k` and an odd
value `ε` on the exceptional class, so the weight of the blow-up is the old weight plus a
one-variable term in the exceptional multiplicity alone.

That extra term is where the arithmetic happens. It vanishes exactly at `s = 0` and `s = ε`, and
it is *nonnegative for every* `s` once `ε` is a unit of `ℤ`, because no integer lies strictly
between `0` and `±1`. Nonnegativity is what fails for the other odd values: `ε = 3` and the
multiplicity `s = 1` already give `s * (s - ε) = -2`. So for a characteristic covector of the
blow-up carrying a unit on the exceptional class — among them the canonical one, which carries
`-1` — the weight function has the same infimum as the weight function downstairs. Hence

`inf χ_{k'} = inf χ_k`,

the main result: **the infimum of the characteristic weights is unchanged by the blow-up move**.
For a negative-definite plumbing this infimum is the minimal characteristic weight, the numerical
`d`-invariant input of `Weight/Sublevel.lean`. Since the blow-down of a `-1`-framed vertex of
degree one is Neumann's first move and `blowUpVertex_degree_none` exhibits the new vertex as such,
this is the first Neumann-invariance statement for the lattice-homology data.

Lattice homology itself is not touched here; the file works one layer below, at the weight
function that grades it. The weight identity and the equality locus `s ∈ {0, ε}` — the two
exceptional multiplicities over a lattice point of `P` at which the blown-up weight is still the
old weight — are also the combinatorial input a later invariance proof needs.

## Main results

* `TauCeti.PlumbingGraph.two_mul_characteristicWeight_blowUpCharacteristic`: the weight formula
  `2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)` for every odd exceptional value `ε`.
* `TauCeti.PlumbingGraph.characteristicWeight_blowUpCharacteristic_eq_iff`: the blown-up weight
  agrees with the old one exactly at the exceptional multiplicities `s = 0` and `s = ε`, and
  `TauCeti.PlumbingGraph.characteristicWeight_le_blowUpCharacteristic`: for unit `ε`, elsewhere it
  is larger.
* `TauCeti.PlumbingGraph.sInfCharacteristicWeight_blowUpCharacteristic` and
  `TauCeti.PlumbingGraph.sInfCharacteristicWeight_canonicalCharacteristic_blowUpVertex`: the
  infimum of the characteristic weights is unchanged by the blow-up move; for negative-definite
  plumbings, this is equality of the minimal weights.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose programme is "Plumbing trees/graphs and their lattices; Némethi's lattice (co)homology …;
invariance under **Neumann moves**; … `d`-invariant analogues". The plumbing calculus is
W. Neumann, *A calculus for plumbing applied to the topology of complex surface singularities and
degenerating complex curves*, Trans. Amer. Math. Soc. **268** (1981), 299--344; the weight
conventions and the behaviour of `χ_k` under blowing up follow Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Sections 2--3, after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

/-! ### Arithmetic of the exceptional multiplicity

Two integer facts about the term `s * (s - δ)` by which a blow-up changes the weight function.
-/

/-- Two consecutive integers have nonnegative product: no integer lies strictly between `t - 1`
and `t`. -/
private theorem zero_le_mul_sub_one (t : ℤ) : 0 ≤ t * (t - 1) := by
  rcases le_or_gt t 0 with ht | ht
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -t) (by omega : (0 : ℤ) ≤ 1 - t)]
  · exact mul_nonneg (by omega) (by omega)

/-- The exceptional term of a unit exceptional value is nonnegative: rescaling by the unit turns
`s * (s - δ)` into a product of consecutive integers. Nonnegativity fails for the other odd
exceptional values, where already `1 * (1 - ε) < 0` for `ε ≥ 3`. -/
private theorem zero_le_mul_sub_units (δ : ℤˣ) (s : ℤ) : 0 ≤ s * (s - (δ : ℤ)) := by
  have hδ : (δ : ℤ) * (δ : ℤ) = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have hEq : ((δ : ℤ) * s) * ((δ : ℤ) * s - 1) = s * (s - (δ : ℤ)) := by
    linear_combination (s * s) * hδ
  rw [← hEq]
  exact zero_le_mul_sub_one _

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] (P : PlumbingGraph V) (v : V)

/-! ### The weight function of a blow-up -/

section Weight

variable [Fintype V]

/-- The characteristic-weight numerator of a blow-up, in total-transform coordinates: the old
numerator corrected by the exceptional term `ε * s - s * s`.

The linear part comes from the duality of the two identifications and the quadratic part from the
orthogonal splitting `intersectionForm_blowUpVertexEquiv` of the intersection form. No parity
hypothesis is needed, since the numerator is defined for arbitrary covectors. -/
theorem characteristicWeightNumerator_blowUpCovectorEquiv (k x : V → ℤ) (ε s : ℤ) :
    (P.blowUpVertex v).characteristicWeightNumerator (blowUpCovectorEquiv v (k, ε))
        (blowUpVertexEquiv v (x, s)) =
      P.characteristicWeightNumerator k x + ε * s - s * s := by
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def,
    sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv, P.intersectionForm_blowUpVertexEquiv v x x s s]
  ring

/-- **The weight function of a blow-up splits.** In total-transform coordinates the characteristic
weight of the blow-up is the characteristic weight of `P` plus the exceptional term
`s * (s - ε) / 2`, which depends on the exceptional multiplicity alone:

`2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)`.

The identity is stated in doubled form, since the exceptional term is halved by the weight
convention `χ_k = -(⟨k, x⟩ + x · x) / 2`. -/
theorem two_mul_characteristicWeight_blowUpCharacteristic (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) (s : ℤ) :
    2 * (P.blowUpVertex v).characteristicWeight (P.blowUpCharacteristic v k ε hε)
        (blowUpVertexEquiv v (x, s)) =
      2 * P.characteristicWeight k x + s * (s - ε) := by
  rw [two_mul_characteristicWeight, blowUpCharacteristic_val,
    characteristicWeightNumerator_blowUpCovectorEquiv]
  linear_combination -P.two_mul_characteristicWeight k x

/-- The total transform preserves the characteristic weight: at exceptional multiplicity `0` the
weight of the blow-up is the weight of `P`. -/
@[simp]
theorem characteristicWeight_blowUpCharacteristic_zero (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) :
    (P.blowUpVertex v).characteristicWeight (P.blowUpCharacteristic v k ε hε)
        (blowUpVertexEquiv v (x, 0)) = P.characteristicWeight k x := by
  have h := P.two_mul_characteristicWeight_blowUpCharacteristic v k ε hε x 0
  rw [zero_mul, add_zero] at h
  omega

/-- The blown-up weight agrees with the old weight exactly at the two exceptional multiplicities
`0` and `ε`, the two lattice points of the exceptional direction where the term `s * (s - ε)`
vanishes. -/
@[simp]
theorem characteristicWeight_blowUpCharacteristic_eq_iff (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) (s : ℤ) :
    (P.blowUpVertex v).characteristicWeight (P.blowUpCharacteristic v k ε hε)
        (blowUpVertexEquiv v (x, s)) = P.characteristicWeight k x ↔ s = 0 ∨ s = ε := by
  have h := P.two_mul_characteristicWeight_blowUpCharacteristic v k ε hε x s
  constructor
  · intro he
    have hzero : s * (s - ε) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hs | hs
    · exact Or.inl hs
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · rw [zero_mul, add_zero] at h
      omega
    · rw [sub_self, mul_zero, add_zero] at h
      omega

/-- **The blow-up does not lower the weight.** With a unit on the exceptional class, every lattice
point of the blow-up has characteristic weight at least that of the lattice point of `P` it lies
over. -/
theorem characteristicWeight_le_blowUpCharacteristic (k : P.characteristicVectors) (δ : ℤˣ)
    (x : V → ℤ) (s : ℤ) :
    P.characteristicWeight k x ≤
      (P.blowUpVertex v).characteristicWeight
        (P.blowUpCharacteristic v k (δ : ℤ) (by
          rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num))
        (blowUpVertexEquiv v (x, s)) := by
  have hδ : Odd ((δ : ℤ)) := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have h := P.two_mul_characteristicWeight_blowUpCharacteristic v k (δ : ℤ) hδ x s
  have hnn := zero_le_mul_sub_units δ s
  linarith

/-- **The infimum of the characteristic weight is a blow-up invariant.** For a characteristic
covector carrying a unit on the exceptional class, the infimum of the characteristic weight of
the blow-up equals the infimum for the original plumbing.

The two weight functions have the same lower bounds, so no hypothesis on `P` is needed: every
lattice point of the blow-up has weight at least that of the point of `P` it lies over, by
`characteristicWeight_le_blowUpCharacteristic`, and every value downstairs is attained upstairs at
the total transform of the same point, by `characteristicWeight_blowUpCharacteristic_zero`. On a
negative-definite plumbing — the case the theory is stated for — the infimum is a genuine minimum
and is the numerical `d`-invariant input of `Weight/Sublevel.lean`, so this is its invariance under
the first of Neumann's moves. -/
theorem sInfCharacteristicWeight_blowUpCharacteristic
    (k : P.characteristicVectors) (δ : ℤˣ) :
    (P.blowUpVertex v).sInfCharacteristicWeight
        (P.blowUpCharacteristic v k (δ : ℤ) (by
          rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num)) =
      P.sInfCharacteristicWeight k := by
  have hδ : Odd ((δ : ℤ)) := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  rw [sInfCharacteristicWeight_def, sInfCharacteristicWeight_def]
  refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
  · rintro _ ⟨y, rfl⟩
    obtain ⟨⟨x, s⟩, rfl⟩ := (blowUpVertexEquiv v).surjective y
    exact ⟨P.characteristicWeight k x, ⟨x, rfl⟩,
      P.characteristicWeight_le_blowUpCharacteristic v k δ x s⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, ⟨blowUpVertexEquiv v (x, 0), rfl⟩,
      (P.characteristicWeight_blowUpCharacteristic_zero v k (δ : ℤ) hδ x).le⟩

/-- The infimum of the canonical characteristic weight — the adjunction class, which carries the
unit `-1` on the exceptional class — is unchanged by the blow-up move. For negative-definite
plumbings, this infimum is the minimal weight. -/
theorem sInfCharacteristicWeight_canonicalCharacteristic_blowUpVertex :
    (P.blowUpVertex v).sInfCharacteristicWeight
        ⟨(P.blowUpVertex v).canonicalCharacteristic,
          (P.blowUpVertex v).isCharacteristicVector_canonicalCharacteristic⟩ =
      P.sInfCharacteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ := by
  rw [← P.blowUpCharacteristic_canonicalCharacteristic v]
  simpa using P.sInfCharacteristicWeight_blowUpCharacteristic v
    ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ (-1)

end Weight

end PlumbingGraph

/-- A self-validating check on the `A₂` plumbing that the exceptional term of
`two_mul_characteristicWeight_blowUpCharacteristic` really contributes: blowing up at the first
vertex with the canonical covector, the lattice point of exceptional multiplicity `1` over the
origin has weight `1`, while the origin itself has weight `0`. -/
example :
    (a2Plumbing.blowUpVertex 0).characteristicWeight
        (a2Plumbing.blowUpCharacteristic 0
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num))
        (PlumbingGraph.blowUpVertexEquiv 0 (0, 1)) = 1 := by
  have h := a2Plumbing.two_mul_characteristicWeight_blowUpCharacteristic 0
    ⟨a2Plumbing.canonicalCharacteristic,
      a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num) 0 1
  rw [PlumbingGraph.characteristicWeight_zero] at h
  norm_num at h
  omega

/-- A self-validating check on the `A₂` plumbing of the equality locus
`characteristicWeight_blowUpCharacteristic_eq_iff`: the other exceptional multiplicity at which
the blown-up weight agrees with the weight downstairs is `-1`, the value carried by the canonical
covector on the exceptional class. -/
example :
    (a2Plumbing.blowUpVertex 0).characteristicWeight
        (a2Plumbing.blowUpCharacteristic 0
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num))
        (PlumbingGraph.blowUpVertexEquiv 0 (0, -1)) = 0 := by
  have h := (a2Plumbing.characteristicWeight_blowUpCharacteristic_eq_iff 0
    ⟨a2Plumbing.canonicalCharacteristic,
      a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num) 0 (-1)).mpr
      (Or.inr (by norm_num))
  rwa [PlumbingGraph.characteristicWeight_zero] at h

end TauCeti
