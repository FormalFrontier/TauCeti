/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import TauCeti.RingTheory.Localization.DenIdeal

/-!
# A valuation subring that separates a point and is small on a prescribed ideal

Stacks 090P, in Mathlib as `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`,
separates a point from a subring integrally closed in a field: for `R ≤ K` with `K` a field and
`z ∉ R`, some valuation subring `V ⊇ R` still misses `z`. Independently,
`Ideal.image_subset_nonunits_valuationSubring` puts a prescribed proper ideal `J` of `R` inside
the non-units of some valuation subring containing `R`. **Neither gives both at once**, and the
valuative criterion for integrality by *continuous* valuations needs both of a single `V`:
missing `z` is what refutes integrality, while `J` landing strictly below `1` is what makes the
induced valuation continuous when `J` is an ideal of definition.

## The hypothesis that combines them

Both conclusions can be read off one maximal ideal `𝔪` of `R`: the point is separated when `𝔪`
contains every denominator of `z` — the `s ∈ R` with `s * z ∈ R`, which are the denominator
ideal `Algebra.denIdeal K z` — and `J` lands below `1` when `𝔪` contains `J`. So the
hypothesis the construction actually needs is that the denominators and `J` sit inside a common
proper ideal, i.e. that their supremum is not `⊤`; that is what the main theorem assumes.

The form this takes in practice is that a *power* of `J` consists of denominators. That implies
the supremum hypothesis — choose `𝔪` over the denominators, and primality pulls `J` itself into
it — so the power-based statement is a corollary, recorded here because it is the shape a
topological ring hands over: multiplication by `z` is continuous and the powers of an ideal of
definition are a neighbourhood basis of `0`, so some power of it multiplies `z` back into any
given open subring. That step is topological and is left to the caller, which is why this file
states algebraic hypotheses and sits beside the Mathlib lemma it refines.

## Main results

* `Subring.exists_le_valuationSubring_notMem_valuation_lt_one` : the combined statement, under
  the supremum hypothesis.
* `Subring.exists_le_valuationSubring_notMem_valuation_lt_one_of_pow_mul_mem` : the corollary
  under the power hypothesis.
* `LocalSubring.isIntegrallyClosedIn_ofPrime` : localising at a prime preserves integral
  closedness in `K`, which is what lets Stacks 090P part (2) apply to the local subring built
  in that proof.
* `LocalSubring.notMem_ofPrime_of_denIdeal_le` : a point whose denominators all lie in `𝔪` is
  still missing from the localisation at `𝔪`.

## References

* [The Stacks Project](https://stacks.math.columbia.edu/tag/090P), Tag 090P.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.18, whose proof
  is given there as the citation [Hu2, Lemma 3.3].

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Presheaf.lean`,
declarations `conductorIdeal`, `conductorIdeal_ne_top`, `notMem_ofPrime_of_conductor_le`,
`isIntegrallyClosedIn_ofPrime` and `exists_valuationSubring_of_notMem_integralClosure`, where
this argument is carried out. **Adapted, not copied.** That development states the result for a
topological ring with a pair of definition, with `R` the integral closure of an open subring in
a fraction field, and defines its own `conductorIdeal`; here the statement is purely algebraic —
an arbitrary subring integrally closed in `K`, an arbitrary ideal, and the explicit hypothesis
that it generates a proper ideal together with the denominators of `z` — and the denominators
are this repository's existing `Algebra.denIdeal` rather than a new definition.
-/

public section

variable {K : Type*} [Field K]

namespace LocalSubring

/-- **Localising at a prime preserves integral closedness in `K`.** If `x : K` is integral over
`R` localised at `𝔪`, clearing denominators makes `m • x` integral over `R` itself for some
`m ∉ 𝔪`; closedness of `R` puts `m • x` in `R`, and `m` is a unit downstairs. -/
theorem isIntegrallyClosedIn_ofPrime (R : Subring K) [IsIntegrallyClosedIn R K]
    (𝔪 : Ideal R) [𝔪.IsPrime] :
    IsIntegrallyClosedIn (LocalSubring.ofPrime R 𝔪).toSubring K := by
  set L := (LocalSubring.ofPrime R 𝔪).toSubring
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  obtain ⟨⟨m, hm⟩, hmx⟩ := hx.exists_multiple_integral_of_isLocalization 𝔪.primeCompl x
  have hmx_R : m • x ∈ R := Subring.isIntegrallyClosedIn_iff.mp inferInstance hmx
  have hmx_L : m • x ∈ L := LocalSubring.le_ofPrime R 𝔪 hmx_R
  -- `m` is a unit downstairs, so dividing by it stays inside `L`
  obtain ⟨u, hu⟩ := IsLocalization.map_units L (⟨m, hm⟩ : 𝔪.primeCompl)
  -- `R → L → K` is a tower and `L → K` is the subring coercion, so `u` reads as `m` in `K`
  have hval : ((u : L) : K) = algebraMap R K m := by
    rw [hu, IsScalarTower.algebraMap_apply R L K, Algebra.algebraMap_ofSubsemiring_apply]
  have hinv : ((↑u⁻¹ : L) : K) * ((u : L) : K) = 1 := by
    rw [← Subring.coe_mul, u.inv_mul, Subring.coe_one]
  have hx_eq : x = ((↑u⁻¹ : L) : K) * (m • x) := by
    rw [Algebra.smul_def, ← hval, ← mul_assoc, hinv, one_mul]
  exact hx_eq ▸ L.mul_mem (↑u⁻¹ : L).2 hmx_L

/-- **A point survives the localisation as long as all its denominators lie in `𝔪`.** Writing
`z = a / s` with `s ∉ 𝔪` exhibits `s` as a denominator of `z`, hence puts `s` in `𝔪`. -/
theorem notMem_ofPrime_of_denIdeal_le (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] {z : K}
    (hden : Algebra.denIdeal K z ≤ 𝔪) :
    z ∉ (LocalSubring.ofPrime R 𝔪).toSubring := by
  intro hmem
  obtain ⟨⟨a, ⟨s, hs⟩⟩, heq⟩ :=
    IsLocalization.surj 𝔪.primeCompl (⟨z, hmem⟩ : (LocalSubring.ofPrime R 𝔪).toSubring)
  have h1 : z * (s : K) = (a : K) := congrArg (Subring.subtype _) heq
  have hs_den : s ∈ Algebra.denIdeal K z :=
    (Algebra.mem_denIdeal_iff K).mpr
      ⟨a, by simpa [Algebra.algebraMap_ofSubsemiring_apply, mul_comm] using h1⟩
  exact hs (hden hs_den)

end LocalSubring

namespace Subring

/-- **A valuation subring separating `z` and strictly below `1` on `J`.** Let `R` be a subring
of a field `K`, integrally closed in `K`, let `z : K`, and let `J` be an ideal of `R` which
together with the denominators of `z` generates a proper ideal. Then a single valuation subring
`V ⊇ R` both misses `z` and has valuation `< 1` at every element of `J`.

The hypothesis is what the construction needs and no more: one maximal ideal `𝔪` above the
supremum serves both halves. It forces `z ∉ R`, since `z ∈ R` makes `1` a denominator and the
denominator ideal `⊤`.

This refines Stacks 090P: the separation alone is
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`, and the bound on `J` alone is
`Ideal.image_subset_nonunits_valuationSubring`. Taking `J = ⊥` recovers the former, so the
strength here is that one `V` does both. -/
theorem exists_le_valuationSubring_notMem_valuation_lt_one (R : Subring K)
    [IsIntegrallyClosedIn R K] {z : K} {J : Ideal R}
    (hsup : Algebra.denIdeal K z ⊔ J ≠ ⊤) :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ z ∉ V ∧
      ∀ a ∈ J, V.valuation (a : K) < 1 := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hsup
  have : 𝔪.IsPrime := h𝔪.isPrime
  have hJ𝔪 : J ≤ 𝔪 := le_sup_right.trans hle
  -- localise at `𝔪`; the point survives and integral closedness is preserved
  have : IsIntegrallyClosedIn (LocalSubring.ofPrime R 𝔪).toSubring K :=
    LocalSubring.isIntegrallyClosedIn_ofPrime R 𝔪
  obtain ⟨V, hVdom, hzV⟩ := LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (LocalSubring.notMem_ofPrime_of_denIdeal_le R 𝔪 (le_sup_left.trans hle))
  refine ⟨V, (LocalSubring.le_ofPrime R 𝔪).trans hVdom.1, hzV, fun a ha ↦ ?_⟩
  -- domination carries the maximal ideal of the localisation into that of `V`
  have haL : (⟨(a : K), LocalSubring.le_ofPrime R 𝔪 a.2⟩ :
      (LocalSubring.ofPrime R 𝔪).toSubring) ∈
      IsLocalRing.maximalIdeal (LocalSubring.ofPrime R 𝔪).toSubring :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔪 a).mpr (hJ𝔪 ha)
  have : IsLocalHom (Subring.inclusion hVdom.1) := hVdom.2
  exact (ValuationSubring.valuation_lt_one_iff V _).mp
    (map_nonunit (Subring.inclusion hVdom.1) _ haL)

/-- **The power form of `Subring.exists_le_valuationSubring_notMem_valuation_lt_one`.** If a
power of `J` consists of denominators of `z ∉ R`, then the denominators and `J` do lie in a
common proper ideal: a maximal ideal above the denominators contains `J ^ n`, hence `J`.

This is the shape a topological ring supplies, with `J` an ideal of definition and `n` given by
continuity of multiplication by `z`. -/
theorem exists_le_valuationSubring_notMem_valuation_lt_one_of_pow_mul_mem (R : Subring K)
    [IsIntegrallyClosedIn R K] {z : K} (hz : z ∉ R) {J : Ideal R} {n : ℕ}
    (hJ : ∀ a ∈ J ^ n, (a : K) * z ∈ R) :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ z ∉ V ∧
      ∀ a ∈ J, V.valuation (a : K) < 1 := by
  -- the denominators are proper: `1` is a denominator only if `z` already lies in `R`
  have hS_ne_top : Algebra.denIdeal K z ≠ ⊤ := fun h ↦ hz (by
    have h1 : (1 : R) ∈ Algebra.denIdeal K z := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := (Algebra.mem_denIdeal_iff K).mp h1
    have hzt : z = (t : K) := by
      simpa [Algebra.algebraMap_ofSubsemiring_apply] using ht
    rw [hzt]
    exact t.2)
  obtain ⟨𝔪, h𝔪, hS𝔪⟩ := Ideal.exists_le_maximal _ hS_ne_top
  have : 𝔪.IsPrime := h𝔪.isPrime
  -- a power of `J` consists of denominators, so primality puts `J` itself inside `𝔪`
  have hJ𝔪 : J ≤ 𝔪 := Ideal.IsPrime.le_of_pow_le
    (le_trans (fun a ha ↦ (Algebra.mem_denIdeal_iff K).mpr ⟨⟨_, hJ a ha⟩, rfl⟩) hS𝔪)
  exact exists_le_valuationSubring_notMem_valuation_lt_one R fun htop ↦
    h𝔪.ne_top (eq_top_iff.mpr (htop ▸ sup_le hS𝔪 hJ𝔪))

end Subring
