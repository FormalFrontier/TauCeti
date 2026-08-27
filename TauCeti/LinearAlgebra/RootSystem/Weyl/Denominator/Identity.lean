/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber

public section

/-!
# The Weyl denominator identity

The **Weyl denominator identity** is the equality

`∏_{α > 0} (1 - e^{-α}) = ∑_{w ∈ W} sgn(w) e^{w(ρ) - ρ}`

in the integral group algebra `ℤ[M]` of the weight space of a root system: the Weyl denominator
`TauCeti.weylDenominator` is the Weyl numerator `TauCeti.weylNumerator` of the weight `0`. It is
the case `λ = 0` of the Weyl character formula, and the combinatorial input that formula is proved
from; in the shifted normalization used here both sides are already `ρ`-free, the classical
symmetric form `∏_{α>0}(e^{α/2} - e^{-α/2}) = ∑_w sgn(w) e^{w(ρ)}` being `e^{ρ}` times this one.

## The proof

Both sides transform by the sign character under the dot action `w ⬝ x = w(x + ρ) - ρ` on the
exponents: for the numerator this is a reindexing of its defining sum
(`TauCeti.coeff_weylNumerator_dotAction_index`), for the denominator it is
`TauCeti.coeff_weylDenominator_dotAction`. A coefficient may therefore be compared after moving
its exponent into the fundamental domain of the dot action, that is to an `x` whose shift
`x + ρ` is dominant. There the two elements have the *same* support, namely `{0}`:

* the exponents of the denominator lie in the negative cone, so a nonvanishing coefficient at such
  an `x` forces `-x` to be a nonnegative combination of the simple roots; integrality then upgrades
  `⟨x, αᵢ^∨⟩ ≥ -1` to `⟨x, αᵢ^∨⟩ ≥ 0` except on the wall `⟨x, αᵢ^∨⟩ = -1`, where the coefficient
  vanishes anyway, and a dominant weight of the negative cone is `0`
  (`TauCeti.eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone`);
* the exponents of the numerator of `0` are the `w ⬝ 0 = w(ρ) - ρ`, and `w(ρ)` is dominant only
  for `w = 1`, because `ρ` is *strictly* dominant and the Weyl group acts freely there.

Both coefficients at `0` are `1`, so the two elements agree.

## Main results

* `TauCeti.eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone`: **a dominant weight lying in
  the negative cone is zero**, the positive-definiteness input of the proof.
* `TauCeti.coeff_weylNumerator_dotAction_index`: the coefficients of the numerator transform by
  the sign character under the dot action on the exponent.
* `TauCeti.coeff_weylDenominator_zero` and `TauCeti.weylDenominator_ne_zero`: the constant
  coefficient of `Δ` is `1`, so `Δ` does not vanish.
* `TauCeti.weylNumerator_zero_eq_weylDenominator`: **the Weyl denominator identity.**
* `TauCeti.support_coeff_weylDenominator` and `TauCeti.card_support_coeff_weylDenominator`: the
  denominator is supported exactly on the dot orbit of `0`, so all the cancellation in the product
  of `|Φ⁺|` binomials leaves exactly `|W|` terms.

## References

This is the "Weyl denominator identity" step of Layer 6 ("the Weyl character, dimension, and
Kostant formulas") of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose
chosen route to the character formula proves the denominator identity combinatorially and concludes
by Weyl alternation. As with `TauCeti.weylVector` and `TauCeti.dotAction`, the combinatorics lives
at the level of an abstract root pairing.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.3.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII, §7.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

/-! ### A dominant weight of the negative cone vanishes

The canonical form `RootPairing.RootForm` pairs a dominant weight nonnegatively with every simple
root, so it pairs a dominant weight of the negative cone nonpositively with itself; being positive
definite on the span of the roots, it forces the weight to vanish. -/

section Definite

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [Finite ι] [CharZero R] in
/-- The canonical form against a root is the coroot functional of that root, up to the positive
factor `⟨α, α⟩ / 2`. This is the reflection-invariance of the form, read at the reflection in that
root. -/
private lemma two_mul_rootForm_root_apply [Fintype ι] (j : ι) (y : M) :
    2 * P.RootForm (P.root j) y = P.RootForm (P.root j) (P.root j) * P.coroot' j y := by
  have h := P.rootForm_reflection_reflection_apply j (P.root j) y
  rw [_root_.RootPairing.reflection_apply_self, _root_.RootPairing.reflection_apply] at h
  simp only [map_neg, LinearMap.neg_apply, map_sub, map_smul, smul_eq_mul] at h
  linear_combination -h

omit [Finite ι] in
/-- The canonical form of a simple root against a weight of the dominant chamber is nonnegative. -/
private lemma zero_le_rootForm_root_apply [Fintype ι] {j : ι} {y : M}
    (hy : 0 ≤ P.coroot' j y) : 0 ≤ P.RootForm (P.root j) y := by
  have h2 : (0 : R) < 2 := zero_lt_two
  have : NeZero (2 : R) := ⟨h2.ne'⟩
  have hpos : 0 < P.RootForm (P.root j) (P.root j) :=
    P.rootForm_pos_of_ne_zero (Submodule.subset_span (Set.mem_range_self j)) (P.ne_zero j)
  have h := two_mul_rootForm_root_apply P j y
  linarith [mul_nonneg hpos.le hy]

variable {P b}

/-- **A dominant weight lying in the negative cone is zero.** Pairing `x` with the nonnegative
combination of simple roots that `-x` is, the canonical form takes a nonpositive value at `x`
against itself; it is nonnegative there in any case, so it vanishes, and it is positive definite on
the span of the roots. -/
theorem eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone {y : M}
    (hy : y ∈ dominantChamber P b) (hneg : -y ∈ posRootCone P b) : y = 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp hneg
  have hspan : y ∈ P.rootSpan R := by
    have hmem : -y ∈ P.rootSpan R := by
      rw [hf]
      exact Submodule.sum_mem _ fun j _ ↦
        nsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
    simpa using neg_mem hmem
  have hle : P.RootForm y y ≤ 0 := by
    have hexp : P.RootForm (-y) y = ∑ j ∈ b.support, (f j : R) * P.RootForm (P.root j) y := by
      rw [hf, map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    have hnonneg : 0 ≤ P.RootForm (-y) y := by
      rw [hexp]
      exact Finset.sum_nonneg fun j hj ↦
        mul_nonneg (Nat.cast_nonneg _)
          (zero_le_rootForm_root_apply P ((mem_dominantChamber P b y).mp hy j hj))
    rw [map_neg, LinearMap.neg_apply] at hnonneg
    linarith
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hspan
    (le_antisymm hle (P.zero_le_rootForm y))

end Definite

/-! ### The support of the denominator

Only the negative cone carries coefficients of `Δ`, and there the simple coroots take integer
values. Together with the vanishing on the walls of the dot action this pins the dot-dominant part
of the support down to `{0}`. -/

section Support

omit [Finite ι] [CharZero R] in
/-- **The simple coroots take integer values on the positive root cone.** The cone is generated by
the simple roots, on which the coroot functionals are the entries of the Cartan matrix. -/
theorem exists_intCast_eq_coroot'_of_mem_posRootCone [P.IsCrystallographic] {u : M}
    (hu : u ∈ posRootCone P b) (i : ι) : ∃ n : ℤ, P.coroot' i u = (n : R) := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hu
  refine ⟨∑ j ∈ b.support, (f j : ℤ) * P.pairingIn ℤ j i, ?_⟩
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_nsmul, _root_.RootPairing.root_coroot'_eq_pairing, nsmul_eq_mul,
    ← P.algebraMap_pairingIn ℤ j i]
  simp

/-- **The Weyl denominator is supported in the negative cone.** Expanding the product, an exponent
of `Δ` is minus a sum of positive roots. -/
theorem neg_mem_posRootCone_of_coeff_weylDenominator_ne_zero {y : M}
    (hy : (weylDenominator P b).coeff y ≠ 0) : -y ∈ posRootCone P b := by
  by_contra hcon
  refine hy (coeff_weylDenominator_eq_zero P b fun T hT hEq ↦ hcon ?_)
  rw [hEq, neg_neg]
  exact AddSubmonoid.sum_mem _ fun j hj ↦ root_mem_posRootCone_of_mem_posRoots P b
    ((mem_posRootsFinset P b j).mp (hT hj))

/-- **The constant coefficient of the Weyl denominator is one**: the empty subset is the only set
of positive roots summing to zero. -/
theorem coeff_weylDenominator_zero : (weylDenominator P b).coeff 0 = 1 := by
  classical
  rw [weylDenominator_eq_sum_powerset]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single ∅]
  · simp
  · refine fun T hT hne ↦ Finsupp.single_eq_of_ne' (neg_ne_zero.mpr ?_)
    exact sum_root_ne_zero_of_mem_posRoots P b (Finset.nonempty_iff_ne_empty.mpr hne)
      fun j hj ↦ (mem_posRootsFinset P b j).mp (Finset.mem_powerset.mp hT hj)
  · simp

/-- **The Weyl denominator does not vanish**, its coefficient at the exponent `0` being `1`. -/
theorem weylDenominator_ne_zero : weylDenominator P b ≠ 0 := fun hcon ↦ by
  have h := coeff_weylDenominator_zero P b
  rw [hcon] at h
  simp at h

variable [Invertible (2 : R)] [LinearOrder R] [IsStrictOrderedRing R] [P.IsCrystallographic]
  [P.IsReduced]

/-- **The only dot-dominant exponent of the Weyl denominator is `0`.** A nonzero coefficient at `y`
puts `-y` in the positive root cone, so every `⟨y, αᵢ^∨⟩` is an integer; being at least `-1` by
dot-dominance and different from `-1` because `Δ` vanishes on that wall, it is nonnegative. A
dominant `y` of the negative cone is `0`. -/
theorem coeff_weylDenominator_eq_zero_of_add_weylVector_mem_dominantChamber {y : M}
    (hdom : y + weylVector P b ∈ dominantChamber P b) (hy : y ≠ 0) :
    (weylDenominator P b).coeff y = 0 := by
  by_contra hne
  have hcone := neg_mem_posRootCone_of_coeff_weylDenominator_ne_zero P b hne
  refine hy (eq_zero_of_mem_dominantChamber_of_neg_mem_posRootCone ?_ hcone)
  refine (mem_dominantChamber P b y).mpr fun i hi ↦ ?_
  obtain ⟨n, hn⟩ := exists_intCast_eq_coroot'_of_mem_posRootCone P b hcone i
  rw [map_neg] at hn
  have hval : P.coroot' i y = ((-n : ℤ) : R) := by push_cast; linear_combination -hn
  -- Dot-dominance bounds the pairing below by `-1`, and the wall of `sᵢ` is excluded.
  have hge : ((-1 : ℤ) : R) ≤ ((-n : ℤ) : R) := by
    have hb := (mem_dominantChamber P b _).mp hdom i hi
    rw [coroot'_add_weylVector P b hi, hval] at hb
    push_cast
    linarith
  have hwall : (-n : ℤ) ≠ -1 := by
    intro hcon
    refine hne (coeff_weylDenominator_eq_zero_of_coroot'_eq_neg_one P b hi ?_)
    rw [hval, hcon]
    push_cast
    ring
  have : (0 : ℤ) ≤ -n := by
    have := (Int.cast_le (R := R)).mp hge
    omega
  rw [hval]
  exact_mod_cast this

end Support

/-! ### The identity -/

section Identity

variable [Invertible (2 : R)] [LinearOrder R] [IsStrictOrderedRing R] [P.IsCrystallographic]
  [P.IsReduced] [P.flip.IsReduced] [Fintype P.weylGroup]

omit [P.flip.IsReduced] in
/-- **The coefficients of the Weyl numerator transform by the sign character under the dot action
on the exponent**: `[e^{v ⬝ y}] N(λ) = sgn(v) [e^y] N(λ)`.

Unlike `TauCeti.weylNumerator_dotAction`, which moves the *weight* `λ`, this moves the exponent the
coefficient is read at; it is the reindexing `w ↦ v⁻¹ w` of the defining sum. -/
theorem coeff_weylNumerator_dotAction_index (lam : M) (v : P.weylGroup) (y : M) :
    (weylNumerator P b lam).coeff (dotAction P b v y)
      = (weylSign P b v : ℤ) * (weylNumerator P b lam).coeff y := by
  classical
  simp only [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finset.mul_sum]
  refine Fintype.sum_bijective (fun w ↦ v⁻¹ * w) (Group.mulLeft_bijective v⁻¹) _ _ fun w ↦ ?_
  have hsign : (weylSign P b v : ℤ) * (weylSign P b (v⁻¹ * w) : ℤ) = (weylSign P b w : ℤ) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  by_cases h : dotAction P b (v⁻¹ * w) lam = y
  · have h' : dotAction P b w lam = dotAction P b v y := by
      rw [← h, ← dotAction_mul, mul_inv_cancel_left]
    rw [h', h, Finsupp.single_eq_same, Finsupp.single_eq_same]
    exact hsign.symm
  · have h' : dotAction P b w lam ≠ dotAction P b v y := fun hc ↦
      h (by rw [dotAction_mul, hc, dotAction_inv_dotAction])
    rw [Finsupp.single_eq_of_ne' h', Finsupp.single_eq_of_ne' h, mul_zero]

/-- **The constant coefficient of the Weyl numerator of `0` is one**: the identity is the only
Weyl-group element fixing `0` for the dot action. -/
theorem coeff_weylNumerator_zero_zero : (weylNumerator P b 0).coeff 0 = 1 := by
  have h := coeff_weylNumerator_dotAction P b (zero_mem_dominantChamber P b) (1 : P.weylGroup)
  rw [dotAction_one] at h
  simpa using h

/-- **The only dot-dominant exponent of the Weyl numerator of `0` is `0`.** Its exponents are the
`w ⬝ 0 = w(ρ) - ρ`, and `ρ` is strictly dominant, where the Weyl group acts freely. -/
theorem coeff_weylNumerator_zero_eq_zero_of_add_weylVector_mem_dominantChamber {y : M}
    (hdom : y + weylVector P b ∈ dominantChamber P b) (hy : y ≠ 0) :
    (weylNumerator P b 0).coeff y = 0 := by
  refine coeff_weylNumerator_eq_zero P b fun v hv ↦ hy ?_
  have hshift : v • weylVector P b ∈ dominantChamber P b := by
    have hv' := dotAction_add_weylVector P b v 0
    rw [hv, zero_add] at hv'
    rw [← hv']
    exact hdom
  rw [← hv, eq_one_of_smul_mem_dominantChamber P b v
    (weylVector_mem_openDominantChamber P b) hshift, dotAction_one]

/-- **The Weyl denominator identity**: `∏_{α>0} (1 - e^{-α}) = ∑_{w ∈ W} sgn(w) e^{w(ρ) - ρ}`, that
is, the Weyl denominator is the Weyl numerator of the weight `0`.

Both sides transform by the sign character under the dot action on exponents, so their coefficients
may be compared after moving an exponent into the fundamental domain; there both are supported on
`{0}` alone, with coefficient `1`. -/
theorem weylNumerator_zero_eq_weylDenominator :
    weylNumerator P b 0 = weylDenominator P b := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun y ↦ ?_)
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b (y + weylVector P b)
  have hdom : dotAction P b w y + weylVector P b ∈ dominantChamber P b := by
    rw [dotAction_add_weylVector]
    exact hw
  have hkey : (weylNumerator P b 0).coeff (dotAction P b w y)
      = (weylDenominator P b).coeff (dotAction P b w y) := by
    by_cases hzero : dotAction P b w y = 0
    · rw [hzero, coeff_weylDenominator_zero, coeff_weylNumerator_zero_zero]
    · rw [coeff_weylNumerator_zero_eq_zero_of_add_weylVector_mem_dominantChamber P b hdom hzero,
        coeff_weylDenominator_eq_zero_of_add_weylVector_mem_dominantChamber P b hdom hzero]
  rw [coeff_weylNumerator_dotAction_index P b 0 w y, coeff_weylDenominator_dotAction P b w y]
    at hkey
  exact mul_left_cancel₀ (Units.ne_zero (weylSign P b w)) hkey

/-- **The Weyl denominator is supported exactly on the dot orbit of `0`**, the weights
`w(ρ) - ρ`. -/
theorem support_coeff_weylDenominator [DecidableEq M] :
    (weylDenominator P b).coeff.support
      = Finset.univ.image fun w : P.weylGroup ↦ dotAction P b w 0 := by
  rw [← weylNumerator_zero_eq_weylDenominator]
  exact support_coeff_weylNumerator P b (zero_mem_dominantChamber P b)

/-- **The expanded Weyl denominator has exactly `|W|` terms.** All the cancellation in
`∏_{α>0}(1 - e^{-α})`, a product of `|Φ⁺|` binomials, leaves one term for each Weyl-group
element. -/
theorem card_support_coeff_weylDenominator :
    (weylDenominator P b).coeff.support.card = Fintype.card P.weylGroup := by
  rw [← weylNumerator_zero_eq_weylDenominator]
  exact card_support_coeff_weylNumerator P b (zero_mem_dominantChamber P b)

end Identity

end TauCeti
