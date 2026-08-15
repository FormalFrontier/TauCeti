/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.LinearCombination
public import TauCeti.LowDimTopology.Plumbing.BlowUp
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# The plumbing-lattice weight function under a blow-up

`BlowUp.lean` builds the first of Neumann's plumbing moves, blowing up a plumbing graph `P` at a
vertex `v`, and identifies the blown-up lattice with `(V → ℤ) × ℤ` through the total transform
`blowUpVertexEquiv`, under which the intersection form becomes the orthogonal direct sum
`⟨(x, s), (y, t)⟩ = ⟨x, y⟩ - s * t`. This file carries that splitting through Némethi's weight
function `χ_k`, the function whose sublevel sets filter the lattice complex.

The covector side of the splitting is `blowUpCovectorEquiv`, the identification dual to
`blowUpVertexEquiv`: a covector `k` of `P` together with a value `ε` on the exceptional class
becomes the covector of the blow-up whose pairing against a total transform is
`⟨k', φ(x, s)⟩ = ⟨k, x⟩ + ε * s`. It is characteristic for the blow-up exactly when `k` is
characteristic for `P` and `ε` is odd, and every characteristic covector of the blow-up arises
this way. Combining the two splittings gives the weight formula

`2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)`,

so the weight of the blow-up is the old weight plus a one-variable term in the exceptional
multiplicity alone.

That extra term is where the arithmetic happens. It vanishes exactly at `s = 0` and `s = ε`, and
it is *nonnegative for every* `s` once `ε` is a unit of `ℤ`, because no integer lies strictly
between `0` and `±1`. Nonnegativity is what fails for the other odd values: `ε = 3` and the
multiplicity `s = 1` already give `s * (s - ε) = -2`. So for a characteristic covector of the
blow-up carrying a unit on the exceptional class — among them the canonical one, which carries
`-1` — the weight function has the same minimum as the weight function downstairs. Hence

`inf χ_{k'} = inf χ_k`,

the main result: **the minimal characteristic weight, the numerical `d`-invariant input of
`Weight/Sublevel.lean`, is unchanged by the blow-up move**. Since the blow-down of a `-1`-framed
vertex of degree one is Neumann's first move and `blowUpVertex_degree_none` exhibits the new
vertex as such, this is the first Neumann-invariance statement for the lattice-homology data.

Lattice homology itself is not touched here; the file works one layer below, at the weight
function that grades it. The weight identity and the equality locus `s ∈ {0, ε}` are also the
combinatorial input a later invariance proof needs, since they say that the exceptional direction
of each sublevel set of the blow-up retracts onto the two-element slab lying over the
corresponding sublevel set of `P`.

## Main definitions

* `TauCeti.PlumbingGraph.blowUpCovectorEquiv`: the total-transform identification of the covectors
  of the blow-up with pairs `(k, ε)`, dual to `blowUpVertexEquiv`.
* `TauCeti.PlumbingGraph.blowUpCharacteristic`: the characteristic covector of the blow-up
  determined by a characteristic covector of `P` and an odd value on the exceptional class.

## Main results

* `TauCeti.PlumbingGraph.isCharacteristicVector_blowUpCovectorEquiv_iff` and
  `TauCeti.PlumbingGraph.exists_blowUpCovectorEquiv_eq`: the characteristic covectors of the
  blow-up are exactly the pairs of a characteristic covector of `P` with an odd exceptional value.
* `TauCeti.PlumbingGraph.blowUpCovectorEquiv_canonicalCharacteristic`: the canonical characteristic
  covector of the blow-up is the canonical one of `P` with exceptional value `-1`.
* `TauCeti.PlumbingGraph.two_mul_characteristicWeight_blowUpCharacteristic`: the weight formula
  `2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)` for every odd exceptional value `ε`.
* `TauCeti.PlumbingGraph.characteristicWeight_blowUpCharacteristic_eq_iff`: the blown-up weight
  agrees with the old one exactly at the exceptional multiplicities `s = 0` and `s = ε`, and
  `TauCeti.PlumbingGraph.characteristicWeight_le_blowUpCharacteristic`: for unit `ε`, elsewhere it
  is larger.
* `TauCeti.PlumbingGraph.sInfCharacteristicWeight_blowUpCharacteristic` and
  `TauCeti.PlumbingGraph.sInfCharacteristicWeight_canonicalCharacteristic_blowUpVertex`: the minimal
  characteristic weight is unchanged by the blow-up move.

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

/-! ### The covectors of a blow-up

The lattice of the blow-up is identified with `(V → ℤ) × ℤ` by the total transform
`blowUpVertexEquiv`. This section records the dual identification of its covectors, which is what
turns the weight function of the blow-up into the weight function of `P` plus an exceptional term.
-/

/-- The total-transform identification of the covectors of the blow-up.

A pair `(k, ε)` consisting of a covector `k` of the original plumbing lattice and the value `ε`
on the exceptional class is sent to the covector of the blow-up taking the value `ε` at the new
vertex `none` and `k w - [w = v] ε` at an old vertex `some w`. This is the identification dual to
`blowUpVertexEquiv`: `sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv` says the pairing of
`blowUpCovectorEquiv v (k, ε)` against the total transform of `(x, s)` is `⟨k, x⟩ + ε * s`, so
`k` is the restriction of the covector to the image of the old lattice and `ε` is its value on
the exceptional class.

Beware that the old coordinates are *not* simply retained: the value at `some v` is corrected by
`ε`, because the basis vector `Pi.single (some v) 1` of the blow-up is the proper transform of the
sphere `v`, not its total transform. -/
def blowUpCovectorEquiv (v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim p.2 fun w => p.1 w - if w = v then p.2 else 0
  map_add' p q := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        split_ifs <;> ring
  map_smul' c p := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring
  invFun k := (fun w => k (some w) + (if w = v then k none else 0), k none)
  left_inv p := by
    rw [Prod.ext_iff]
    refine ⟨funext fun w => ?_, rfl⟩
    simp only [Option.elim_some, Option.elim_none]
    split_ifs <;> ring
  right_inv k := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some]
        split_ifs <;> ring

/-- The value of a lifted covector on the exceptional class. -/
@[simp]
theorem blowUpCovectorEquiv_apply_none (k : V → ℤ) (ε : ℤ) :
    blowUpCovectorEquiv v (k, ε) none = ε :=
  (rfl)

/-- The value of a lifted covector at an old vertex, corrected at the blown-up vertex. -/
@[simp]
theorem blowUpCovectorEquiv_apply_some (k : V → ℤ) (ε : ℤ) (w : V) :
    blowUpCovectorEquiv v (k, ε) (some w) = k w - if w = v then ε else 0 :=
  (rfl)

/-- At the blown-up vertex the lifted covector is corrected by the exceptional value. -/
theorem blowUpCovectorEquiv_apply_some_self (k : V → ℤ) (ε : ℤ) :
    blowUpCovectorEquiv v (k, ε) (some v) = k v - ε := by
  simp

/-- Away from the blown-up vertex the lifted covector keeps its old values. -/
theorem blowUpCovectorEquiv_apply_some_of_ne (k : V → ℤ) (ε : ℤ) {w : V} (h : w ≠ v) :
    blowUpCovectorEquiv v (k, ε) (some w) = k w := by
  simp [h]

/-- The inverse identification reads off the value on the exceptional class and undoes the
correction at the blown-up vertex. -/
@[simp]
theorem blowUpCovectorEquiv_symm_apply (k : Option V → ℤ) :
    (blowUpCovectorEquiv v).symm k =
      (fun w => k (some w) + (if w = v then k none else 0), k none) :=
  (rfl)

/-- The canonical characteristic covector of the blow-up is the canonical characteristic covector
of `P` carrying the value `-1` on the exceptional class.

This is the adjunction formula for a blow-up: the exceptional sphere has square `-1`, so
`K(E) + E · E = -2` forces `K(E) = -1`. -/
theorem blowUpCovectorEquiv_canonicalCharacteristic :
    blowUpCovectorEquiv v (P.canonicalCharacteristic, -1) =
      (P.blowUpVertex v).canonicalCharacteristic := by
  funext a
  cases a with
  | none => simp
  | some w =>
      simp only [blowUpCovectorEquiv_apply_some, canonicalCharacteristic_apply,
        blowUpVertex_weight_some]
      split_ifs <;> ring

/-- A lifted covector is characteristic for the blow-up exactly when the covector it lifts is
characteristic for `P` and its value on the exceptional class is odd.

Oddness is the parity condition at the new `-1`-framed vertex; at an old vertex the correction
`[w = v] ε` and the framing drop `[w = v]` cancel modulo two precisely because `ε` is odd. -/
theorem isCharacteristicVector_blowUpCovectorEquiv_iff (k : V → ℤ) (ε : ℤ) :
    (P.blowUpVertex v).IsCharacteristicVector (blowUpCovectorEquiv v (k, ε)) ↔
      P.IsCharacteristicVector k ∧ Odd ε := by
  simp only [isCharacteristicVector_iff, Int.ModEq, Int.odd_iff]
  constructor
  · intro h
    have hnone := h none
    rw [blowUpCovectorEquiv_apply_none, blowUpVertex_weight_none] at hnone
    refine ⟨fun w => ?_, by omega⟩
    have hw := h (some w)
    rcases eq_or_ne w v with rfl | hwv
    · rw [blowUpCovectorEquiv_apply_some_self, blowUpVertex_weight_some_self] at hw
      omega
    · rw [blowUpCovectorEquiv_apply_some_of_ne (h := hwv),
        blowUpVertex_weight_some_of_ne (h := hwv)] at hw
      omega
  · rintro ⟨hk, hε⟩ a
    cases a with
    | none => rw [blowUpCovectorEquiv_apply_none, blowUpVertex_weight_none]; omega
    | some w =>
        have hw := hk w
        rcases eq_or_ne w v with rfl | hwv
        · rw [blowUpCovectorEquiv_apply_some_self, blowUpVertex_weight_some_self]
          omega
        · rw [blowUpCovectorEquiv_apply_some_of_ne (h := hwv),
            blowUpVertex_weight_some_of_ne (h := hwv)]
          omega

/-- Every characteristic covector of a blow-up is the lift of a characteristic covector of `P`
carrying an odd value on the exceptional class. Together with
`isCharacteristicVector_blowUpCovectorEquiv_iff` this parametrizes the characteristic covectors of
a blow-up completely. -/
theorem exists_blowUpCovectorEquiv_eq (k : (P.blowUpVertex v).characteristicVectors) :
    ∃ (l : P.characteristicVectors) (ε : ℤ), Odd ε ∧
      blowUpCovectorEquiv v (l.val, ε) = k.val := by
  obtain ⟨p, hp⟩ := (blowUpCovectorEquiv v).surjective k.val
  obtain ⟨hl, hε⟩ :=
    (P.isCharacteristicVector_blowUpCovectorEquiv_iff v p.1 p.2).mp (hp ▸ k.property)
  exact ⟨⟨p.1, hl⟩, p.2, hε, hp⟩

/-- The characteristic covector of the blow-up of `P` at `v` determined by a characteristic
covector `k` of `P` and an odd value `ε` on the exceptional class.

Every odd exceptional value gives a characteristic covector, although only the unit values
`ε = ±1` make the extra weight term `s * (s - ε)` nonnegative at every exceptional multiplicity;
see `characteristicWeight_le_blowUpCharacteristic`. The canonical characteristic covector of a
blow-up is the case `ε = -1` of `k` canonical, by
`blowUpCharacteristic_canonicalCharacteristic`. -/
def blowUpCharacteristic (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpVertex v).characteristicVectors :=
  ⟨blowUpCovectorEquiv v (k.val, ε),
    (P.isCharacteristicVector_blowUpCovectorEquiv_iff v k.val ε).mpr ⟨k.property, hε⟩⟩

/-- The underlying covector of `blowUpCharacteristic` is the lift of the underlying covector. -/
@[simp]
theorem blowUpCharacteristic_val (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpCharacteristic v k ε hε).val = blowUpCovectorEquiv v (k.val, ε) :=
  (rfl)

/-- The canonical characteristic covector of a blow-up is the canonical characteristic covector of
`P` with the unit `-1` on the exceptional class. -/
theorem blowUpCharacteristic_canonicalCharacteristic :
    P.blowUpCharacteristic v
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ (-1)
          (by norm_num) =
      ⟨(P.blowUpVertex v).canonicalCharacteristic,
        (P.blowUpVertex v).isCharacteristicVector_canonicalCharacteristic⟩ := by
  refine Subtype.ext ?_
  rw [blowUpCharacteristic_val]
  simpa using P.blowUpCovectorEquiv_canonicalCharacteristic v

/-! ### The weight function of a blow-up -/

section Weight

variable [Fintype V]

/-- The two total-transform identifications are dual to one another: the pairing of the lifted
covector `(k, ε)` against the lifted lattice point `(x, s)` is `⟨k, x⟩ + ε * s`. -/
theorem sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv (k x : V → ℤ) (ε s : ℤ) :
    ∑ a, blowUpCovectorEquiv v (k, ε) a * blowUpVertexEquiv v (x, s) a =
      (∑ w, k w * x w) + ε * s := by
  rw [Fintype.sum_option]
  simp only [blowUpCovectorEquiv_apply_none, blowUpCovectorEquiv_apply_some,
    blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v fun w => ε * x w]
  simp only [Finset.mem_univ, ite_true]
  ring

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
theorem characteristicWeight_le_blowUpCharacteristic (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (hunit : IsUnit ε) (x : V → ℤ) (s : ℤ) :
    P.characteristicWeight k x ≤
      (P.blowUpVertex v).characteristicWeight (P.blowUpCharacteristic v k ε hε)
        (blowUpVertexEquiv v (x, s)) := by
  have h := P.two_mul_characteristicWeight_blowUpCharacteristic v k ε hε x s
  obtain ⟨δ, rfl⟩ := hunit
  have hnn := zero_le_mul_sub_units δ s
  linarith

/-- **The minimal characteristic weight is a blow-up invariant.** For a characteristic covector
carrying a unit on the exceptional class, the infimum of the characteristic weight of the blow-up
equals the infimum for the original plumbing.

One inequality is `characteristicWeight_le_blowUpCharacteristic`, since every lattice point of the
blow-up lies over one of `P`; the other evaluates the blown-up weight at the total transform of a
minimizer, where `characteristicWeight_blowUpCharacteristic_zero` returns the old value. The
infimum is the numerical `d`-invariant input of `Weight/Sublevel.lean`, so this is its invariance
under the first of Neumann's moves. -/
theorem sInfCharacteristicWeight_blowUpCharacteristic (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) (hunit : IsUnit ε) :
    (P.blowUpVertex v).sInfCharacteristicWeight (P.blowUpCharacteristic v k ε hε) =
      P.sInfCharacteristicWeight k := by
  have hblow : (P.blowUpVertex v).IsNegativeDefinite :=
    (P.isNegativeDefinite_blowUpVertex_iff v).mpr h
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx⟩ := P.exists_characteristicWeight_eq_sInfCharacteristicWeight h k
    calc
      (P.blowUpVertex v).sInfCharacteristicWeight (P.blowUpCharacteristic v k ε hε)
          ≤ (P.blowUpVertex v).characteristicWeight (P.blowUpCharacteristic v k ε hε)
              (blowUpVertexEquiv v (x, 0)) :=
        (P.blowUpVertex v).sInfCharacteristicWeight_le hblow _ _
      _ = P.characteristicWeight k x :=
        P.characteristicWeight_blowUpCharacteristic_zero v k ε hε x
      _ = P.sInfCharacteristicWeight k := hx
  · refine (P.blowUpVertex v).le_sInfCharacteristicWeight _ fun y => ?_
    obtain ⟨⟨x, s⟩, rfl⟩ := (blowUpVertexEquiv v).surjective y
    exact (P.sInfCharacteristicWeight_le h k x).trans
      (P.characteristicWeight_le_blowUpCharacteristic v k ε hε hunit x s)

/-- The minimal weight of the canonical characteristic covector — the adjunction class, which
carries the unit `-1` on the exceptional class — is unchanged by the blow-up move. -/
theorem sInfCharacteristicWeight_canonicalCharacteristic_blowUpVertex (h : P.IsNegativeDefinite) :
    (P.blowUpVertex v).sInfCharacteristicWeight
        ⟨(P.blowUpVertex v).canonicalCharacteristic,
          (P.blowUpVertex v).isCharacteristicVector_canonicalCharacteristic⟩ =
      P.sInfCharacteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ := by
  rw [← P.blowUpCharacteristic_canonicalCharacteristic v,
    P.sInfCharacteristicWeight_blowUpCharacteristic v h _ (-1) (by norm_num) (by norm_num)]

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
