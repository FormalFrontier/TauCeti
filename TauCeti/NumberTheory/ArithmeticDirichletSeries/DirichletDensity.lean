/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
public import TauCeti.NumberTheory.NumberField.PrimeIdeal
-- See the implementation notes: this second, private import is what lets
-- `NumberField.Set.hasDirichletDensity_iff_tendsto` be stated at all.
import all Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Convergence of the prime-ideal zeta sum, and the calculus of Dirichlet density

Mathlib defines the partial sum `NumberField.Set.primeIdealZetaSum S s = ∑_{𝔭 ∈ S} N(𝔭) ^ (-s)`
over a set `S` of height-one primes of `𝓞 K`, and says that `S` has Dirichlet density `δ` when the
ratio `primeIdealZetaSum S s / primeIdealZetaSum univ s` tends to `δ` as `s → 1⁺`. What Mathlib
does not record is that those sums converge at all: their summability is exactly the convergence
of the Dedekind zeta series to the right of `1`. This file supplies that input and spends it on
the part of the density calculus that does not need the all-prime asymptotic of the denominator.

## Main results

* `TauCeti.summable_absNorm_rpow_neg_iff`: the sum of `N(I) ^ (-x)` over the *nonzero integral
  ideals* of `𝓞 K` converges exactly for `x > 1`; this is the real-variable form of
  `TauCeti.LSeriesSummable_normCoeff_one_iff`.
* `NumberField.summable_absNorm_rpow_neg` and `NumberField.Set.summable_absNorm_rpow_neg`: hence
  the prime-ideal family, and each of its subfamilies, is summable at every real `s > 1`.
* `NumberField.Set.primeIdealZetaSum_mono`, `NumberField.Set.primeIdealZetaSum_union`,
  `NumberField.Set.primeIdealZetaSum_add_primeIdealZetaSum_compl` and
  `NumberField.Set.primeIdealZetaSum_univ_pos`: monotonicity, additivity over a disjoint union,
  complementation, and positivity of the partial sums at `s > 1`.
* `NumberField.Set.IsLowerDirichletDensityBound` and
  `NumberField.Set.IsUpperDirichletDensityBound`: the one-sided epsilon bounds on the density
  ratio, and `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`, which turns a
  matching pair of them into a genuine density.
* `NumberField.Set.hasDirichletDensity_of_subset_of_subset`: the resulting squeeze.
* `NumberField.Set.HasDirichletDensity.union`,
  `NumberField.Set.HasDirichletDensity.finsetBiUnion`,
  `NumberField.Set.hasDirichletDensity_univ` and `NumberField.Set.HasDirichletDensity.compl`:
  the additivity laws.

## Implementation notes

`NumberField.Set.HasDirichletDensity S δ` is by definition the statement that the density ratio
tends to `δ` along `𝓝[>] 1`, but Mathlib neither exposes that body nor records an unfolding lemma
for it, so downstream modules cannot see through the definition. This file therefore takes the
Mathlib module a second time as a private `import all`, which makes the body visible to proofs
without making this file's public interface depend on it, and states the unfolding once as
`NumberField.Set.hasDirichletDensity_iff_tendsto`. Every proof below goes through that lemma into
the `Filter.Tendsto` API rather than through definitional unfolding.

The `tsum` lemmas about the partial sums are applied to the summand under the name
`zetaSummand`, a private abbreviation for `fun 𝔭 ↦ N(𝔭) ^ (-s)`; naming it turns the
higher-order matching those lemmas would otherwise need into ordinary rewriting.

The one-sided bounds are deliberately *bounds*: every `δ' ≤ δ` is again a lower bound, every
`δ' ≥ δ` again an upper bound, and a set satisfying both for the same `δ` is exactly one with
density `δ`. Genuine lower and upper densities would be the `liminf` and `limsup` of the ratio,
are unique, and are not defined here.

Every statement about the partial sums carries the hypothesis `1 < s`, without which the family is
not summable and `tsum` returns its junk value `0`. The density laws need it only on a
right neighbourhood of `1`, where it is automatic.

Two natural companions are deliberately absent, because both need the all-prime normalization
`primeIdealZetaSum univ s = log (1/(s-1)) + O(1)`, hence the Euler product and the higher
prime-power estimate: that a finite set of primes has density zero, and that the density is
unchanged by a finite symmetric difference. They are the next step of the layer.

## Roadmap role

This is Layer **7.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, together with the
part of Layer **7.3** that does not depend on the normalization of Layer 7.2. The pinned Mathlib
already contains `Mathlib/NumberTheory/NumberField/DirichletDensity.lean`, so the layer's opening
task — adopting `NumberField.Set.primeIdealZetaSum`, `NumberField.Set.HasDirichletDensity` and
`NumberField.Set.dirichletDensity` rather than redefining them — is discharged by consuming that
file directly; every declaration below extends it in its own namespace.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, for the elementary density calculus.
-/

public section

open Filter IsDedekindDomain NumberField Set Topology
open scoped nonZeroDivisors NumberField

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K]

/-! ### The Dedekind zeta series in real form -/

/-- At a real point the ideal terms of the trivial weight have absolute value `N(I) ^ (-x)`, so the
two families are summable together. -/
private theorem summable_idealTerm_one_iff (x : ℝ) :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) (x : ℂ)) ↔
      Summable fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-x) := by
  rw [← summable_norm_iff]
  refine summable_congr fun I ↦ ?_
  rw [norm_idealTerm, Complex.ofReal_re, Pi.one_apply, norm_one,
    Real.rpow_neg (Nat.cast_nonneg _), one_div]

open scoped ComplexOrder in
/-- **The Dedekind zeta series in real form.** The sum of `N(I) ^ (-x)` over the nonzero integral
ideals of `𝓞 K` converges exactly for `x > 1`.

This is the real-variable shadow of `TauCeti.LSeriesSummable_normCoeff_one_iff`: the trivial weight
is nonnegative, so no cancellation occurs inside a norm fibre and the ungrouped ideal-indexed sum
converges precisely where the regrouped Dedekind zeta series does. -/
theorem summable_absNorm_rpow_neg_iff {x : ℝ} :
    Summable (fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-x)) ↔ 1 < x := by
  rw [← summable_idealTerm_one_iff K x]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h)
  · exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
      ((LSeriesSummable_normCoeff_one_iff K).mpr (by simpa using h))

end TauCeti

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Absolute convergence of the prime-ideal zeta sum -/

/-- The prime ideals of `𝓞 K` form a subfamily of the nonzero integral ideals, so the prime-ideal
zeta series converges absolutely at every real `s > 1`. -/
theorem summable_absNorm_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
  ((TauCeti.summable_absNorm_rpow_neg_iff K).mpr hs).comp_injective
    (i := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ : (Ideal (𝓞 K))⁰))
    fun _ _ h ↦ HeightOneSpectrum.ext (by simpa [Subtype.ext_iff] using h)

end NumberField

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]
variable {S T U : Set (HeightOneSpectrum (𝓞 K))} {s δ : ℝ}

/-- The summand of the prime-ideal zeta series, as a function on all height-one primes. -/
private noncomputable def zetaSummand (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    HeightOneSpectrum (𝓞 K) → ℝ :=
  fun 𝔭 ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)

/-- `NumberField.Set.primeIdealZetaSum_def` with the summand named, so that the general `tsum`
lemmas apply by rewriting instead of by higher-order matching. -/
private theorem primeIdealZetaSum_eq_tsum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    S.primeIdealZetaSum s = ∑' 𝔭 : S, zetaSummand K s 𝔭 :=
  primeIdealZetaSum_def S s

private theorem zetaSummand_pos (𝔭 : HeightOneSpectrum (𝓞 K)) (s : ℝ) : 0 < zetaSummand K s 𝔭 := by
  have h : (Ideal.absNorm 𝔭.asIdeal : ℝ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using 𝔭.ne_bot
  exact Real.rpow_pos_of_pos ((Nat.cast_nonneg _).lt_of_ne' h) _

/-- Every subfamily of the prime-ideal zeta series converges absolutely at a real `s > 1`. -/
theorem summable_absNorm_rpow_neg (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : S ↦ (Ideal.absNorm (𝔭 : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ^ (-s) :=
  (_root_.NumberField.summable_absNorm_rpow_neg hs).subtype _

/-! ### Elementary algebra of the partial sums -/

/-- The partial sums of the prime-ideal zeta series are monotone in the set of primes, at every
real `s > 1`. -/
theorem primeIdealZetaSum_mono (hST : S ⊆ T) (hs : 1 < s) :
    S.primeIdealZetaSum s ≤ T.primeIdealZetaSum s := by
  rw [primeIdealZetaSum_eq_tsum, primeIdealZetaSum_eq_tsum]
  exact Summable.tsum_le_tsum_of_inj (fun 𝔭 : S ↦ (⟨𝔭.1, hST 𝔭.2⟩ : T))
    (fun _ _ h ↦ Subtype.ext (by simpa [Subtype.ext_iff] using h))
    (fun _ _ ↦ (zetaSummand_pos _ s).le) (fun _ ↦ le_rfl)
    (S.summable_absNorm_rpow_neg hs) (T.summable_absNorm_rpow_neg hs)

/-- The partial sums of the prime-ideal zeta series are additive over a disjoint union of sets of
primes, at every real `s > 1`. -/
theorem primeIdealZetaSum_union (hd : Disjoint S T) (hs : 1 < s) :
    (S ∪ T).primeIdealZetaSum s = S.primeIdealZetaSum s + T.primeIdealZetaSum s := by
  rw [primeIdealZetaSum_eq_tsum, primeIdealZetaSum_eq_tsum, primeIdealZetaSum_eq_tsum]
  exact Summable.tsum_union_disjoint (f := zetaSummand K s) hd (S.summable_absNorm_rpow_neg hs)
    (T.summable_absNorm_rpow_neg hs)

/-- A set of primes and its complement split the full prime-ideal zeta sum, at every real
`s > 1`. -/
theorem primeIdealZetaSum_add_primeIdealZetaSum_compl (S : Set (HeightOneSpectrum (𝓞 K)))
    (hs : 1 < s) :
    S.primeIdealZetaSum s + Sᶜ.primeIdealZetaSum s =
      primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s := by
  rw [primeIdealZetaSum_eq_tsum, primeIdealZetaSum_eq_tsum, primeIdealZetaSum_eq_tsum,
    tsum_univ (zetaSummand K s)]
  exact Summable.tsum_add_tsum_compl (S.summable_absNorm_rpow_neg hs)
    (Sᶜ.summable_absNorm_rpow_neg hs)

/-- The full prime-ideal zeta sum is positive at every real `s > 1`: a number field has at least
one nonzero prime ideal, and every summand is positive. -/
theorem primeIdealZetaSum_univ_pos (hs : 1 < s) :
    0 < primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s := by
  obtain ⟨𝔭⟩ : Nonempty (HeightOneSpectrum (𝓞 K)) := inferInstance
  rw [primeIdealZetaSum_eq_tsum, tsum_univ (zetaSummand K s)]
  exact (_root_.NumberField.summable_absNorm_rpow_neg hs).tsum_pos
    (fun 𝔮 ↦ (zetaSummand_pos 𝔮 s).le) 𝔭 (zetaSummand_pos 𝔭 s)

/-- The full prime-ideal zeta sum is nonzero at every real `s > 1`, so the density ratio is a
genuine quotient there. -/
theorem primeIdealZetaSum_univ_ne_zero (hs : 1 < s) :
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s ≠ 0 :=
  (primeIdealZetaSum_univ_pos hs).ne'

/-! ### One-sided density bounds -/

/-- Unfolding lemma for Mathlib's `NumberField.Set.HasDirichletDensity`: having Dirichlet density
`δ` is convergence of the density ratio to `δ` as `s → 1⁺`. -/
theorem hasDirichletDensity_iff_tendsto :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
        primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ) :=
  Iff.rfl

/-- `δ` is a **lower Dirichlet density bound** for `S` when, for every `ε > 0`, the density ratio
of `S` eventually exceeds `δ - ε` as `s → 1⁺`.

This is a bound, not a density: it does not determine `δ`, and `S` need not have a density at all.
The genuine lower density would be the `liminf` of the ratio, and is unique. -/
def IsLowerDirichletDensityBound (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ s : ℝ in 𝓝[>] 1,
    δ - ε < S.primeIdealZetaSum s / primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s

/-- `δ` is an **upper Dirichlet density bound** for `S` when, for every `ε > 0`, the density ratio
of `S` eventually stays below `δ + ε` as `s → 1⁺`.

This is a bound, not a density: it does not determine `δ`, and `S` need not have a density at all.
The genuine upper density would be the `limsup` of the ratio, and is unique. -/
def IsUpperDirichletDensityBound (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ s : ℝ in 𝓝[>] 1,
    S.primeIdealZetaSum s / primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s < δ + ε

/-- A set with a Dirichlet density has it as a lower bound. -/
theorem HasDirichletDensity.isLowerDirichletDensityBound (h : S.HasDirichletDensity δ) :
    S.IsLowerDirichletDensityBound δ :=
  fun _ hε ↦ (hasDirichletDensity_iff_tendsto.mp h).eventually_const_lt (by linarith)

/-- A set with a Dirichlet density has it as an upper bound. -/
theorem HasDirichletDensity.isUpperDirichletDensityBound (h : S.HasDirichletDensity δ) :
    S.IsUpperDirichletDensityBound δ :=
  fun _ hε ↦ (hasDirichletDensity_iff_tendsto.mp h).eventually_lt_const (by linarith)

/-- **Matching one-sided bounds give a density.** If `δ` is both an upper and a lower Dirichlet
density bound for `S`, then `S` has Dirichlet density `δ`. -/
theorem hasDirichletDensity_of_upperBound_of_lowerBound (hup : S.IsUpperDirichletDensityBound δ)
    (hlo : S.IsLowerDirichletDensityBound δ) : S.HasDirichletDensity δ := by
  refine hasDirichletDensity_iff_tendsto.mpr (Metric.tendsto_nhds.mpr fun ε hε ↦ ?_)
  filter_upwards [hlo ε hε, hup ε hε] with s h₁ h₂
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Having Dirichlet density `δ` is exactly having `δ` as both an upper and a lower bound. -/
theorem hasDirichletDensity_iff :
    S.HasDirichletDensity δ ↔
      S.IsUpperDirichletDensityBound δ ∧ S.IsLowerDirichletDensityBound δ :=
  ⟨fun h ↦ ⟨h.isUpperDirichletDensityBound, h.isLowerDirichletDensityBound⟩,
    fun h ↦ hasDirichletDensity_of_upperBound_of_lowerBound h.1 h.2⟩

/-- The density ratio is monotone in the set of primes, on a right neighbourhood of `1`. -/
private theorem eventually_ratio_le (hST : S ⊆ T) :
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      S.primeIdealZetaSum s / primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s ≤
        T.primeIdealZetaSum s / primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s := by
  filter_upwards [eventually_mem_nhdsWithin] with s hmem
  have hs : (1 : ℝ) < s := mem_Ioi.mp hmem
  have hpos := primeIdealZetaSum_univ_pos (K := K) hs
  have hle := primeIdealZetaSum_mono hST hs
  gcongr

/-- A lower density bound for a set is a lower density bound for any larger set. -/
theorem IsLowerDirichletDensityBound.mono (h : S.IsLowerDirichletDensityBound δ) (hST : S ⊆ T) :
    T.IsLowerDirichletDensityBound δ := by
  intro ε hε
  filter_upwards [h ε hε, eventually_ratio_le hST] with s h₁ h₂
  exact h₁.trans_le h₂

/-- An upper density bound for a set is an upper density bound for any smaller set. -/
theorem IsUpperDirichletDensityBound.anti (h : T.IsUpperDirichletDensityBound δ) (hST : S ⊆ T) :
    S.IsUpperDirichletDensityBound δ := by
  intro ε hε
  filter_upwards [h ε hε, eventually_ratio_le hST] with s h₁ h₂
  exact h₂.trans_lt h₁

/-! ### The squeeze, and comparison of densities -/

/-- **Squeeze for Dirichlet density.** A set caught between two sets of the same density has that
density. -/
theorem hasDirichletDensity_of_subset_of_subset (hST : S ⊆ T) (hTU : T ⊆ U)
    (hS : S.HasDirichletDensity δ) (hU : U.HasDirichletDensity δ) : T.HasDirichletDensity δ :=
  hasDirichletDensity_of_upperBound_of_lowerBound (hU.isUpperDirichletDensityBound.anti hTU)
    (hS.isLowerDirichletDensityBound.mono hST)

/-- Dirichlet density is monotone: a subset of a set of primes has the smaller density. -/
theorem HasDirichletDensity.le_of_subset {a b : ℝ} (hS : S.HasDirichletDensity a)
    (hT : T.HasDirichletDensity b) (hST : S ⊆ T) : a ≤ b :=
  le_of_tendsto_of_tendsto (hasDirichletDensity_iff_tendsto.mp hS)
    (hasDirichletDensity_iff_tendsto.mp hT) (eventually_ratio_le hST)

/-! ### Unions and complements -/

/-- **Additivity of Dirichlet density over a disjoint union.** -/
theorem HasDirichletDensity.union {a b : ℝ} (hd : Disjoint S T) (hS : S.HasDirichletDensity a)
    (hT : T.HasDirichletDensity b) : (S ∪ T).HasDirichletDensity (a + b) := by
  refine hasDirichletDensity_iff_tendsto.mpr (Filter.Tendsto.congr' ?_
    ((hasDirichletDensity_iff_tendsto.mp hS).add (hasDirichletDensity_iff_tendsto.mp hT)))
  filter_upwards [eventually_mem_nhdsWithin] with s hmem
  have hs : (1 : ℝ) < s := mem_Ioi.mp hmem
  rw [primeIdealZetaSum_union hd hs, add_div]

/-- The set of all nonzero primes has Dirichlet density `1`. -/
theorem hasDirichletDensity_univ :
    HasDirichletDensity (univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  refine hasDirichletDensity_iff_tendsto.mpr (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards [eventually_mem_nhdsWithin] with s hmem
  have hs : (1 : ℝ) < s := mem_Ioi.mp hmem
  exact (div_self (primeIdealZetaSum_univ_ne_zero hs)).symm

/-- **Complementation.** If `S` has Dirichlet density `δ`, its complement has density `1 - δ`. -/
theorem HasDirichletDensity.compl (h : S.HasDirichletDensity δ) :
    Sᶜ.HasDirichletDensity (1 - δ) := by
  refine hasDirichletDensity_iff_tendsto.mpr (Filter.Tendsto.congr' ?_
    (tendsto_const_nhds.sub (hasDirichletDensity_iff_tendsto.mp h)))
  filter_upwards [eventually_mem_nhdsWithin] with s hmem
  have hs : (1 : ℝ) < s := mem_Ioi.mp hmem
  have hpos := primeIdealZetaSum_univ_pos (K := K) hs
  have hsplit := primeIdealZetaSum_add_primeIdealZetaSum_compl S hs
  field_simp
  linarith

/-- **Additivity of Dirichlet density over a finite pairwise-disjoint family.** -/
theorem HasDirichletDensity.finsetBiUnion {ι : Type*} {t : Finset ι}
    {A : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    (hd : (t : Set ι).Pairwise (Function.onFun Disjoint A))
    (h : ∀ i ∈ t, (A i).HasDirichletDensity (d i)) :
    (⋃ i ∈ t, A i).HasDirichletDensity (∑ i ∈ t, d i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using hasDirichletDensity_empty
  | insert a t ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      have hsub : (t : Set ι) ⊆ (insert a t : Finset ι) :=
        Finset.coe_subset.mpr (Finset.subset_insert a t)
      refine HasDirichletDensity.union ?_ (h a (Finset.mem_insert_self a t))
        (ih (hd.mono hsub) fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
      refine Set.disjoint_iUnion_right.mpr fun i ↦ Set.disjoint_iUnion_right.mpr fun hi ↦ ?_
      exact hd (Finset.mem_coe.mpr (Finset.mem_insert_self a t))
        (hsub (Finset.mem_coe.mpr hi)) fun hai ↦ ha (hai ▸ hi)

end NumberField.Set
