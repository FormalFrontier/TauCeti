/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The Cauchy principal value of a contour integral on a set (Hungerbühler–Wasem)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **Cauchy
principal value** of the contour integral `∮_γ f` *excising a symmetric `ε`-ball about each point of
a finite singular set simultaneously*: `HasCauchyPV γ a b f v` says there is a finite set `S ⊆ ℂ`
for which the truncated integrand along `γ` over `[a, b]`, zeroed within `ε` of any point of `S`, is
eventually `IntervalIntegrable` and its integral tends to `v` as `ε → 0⁺`.

This is the set-level (`…On`) companion of `HasCauchyPVAt` (`CauchyPrincipalValue.lean`), which
excises a single prescribed point `z₀`; the naming mirrors Mathlib's `MeromorphicAt` (at a point)
versus `MeromorphicOn` (on a set). The **finite excision set** `S` is bound **existentially**, so
the predicate is intrinsic to `(γ, f)` and stays faithful to the roadmap's `S`-free signature: it
holds when *some* finite set satisfies the two clauses. A prescribed set — for instance the pole set
of the generalized residue theorem, with intended value `2πi · ∑_{s ∈ S} n_γ(s) · res f s` — can be
used as the witness once its integrability and `Tendsto` clauses have been proved. Enlarging a
witness leaves the limit unchanged, so the value is well-defined (`HasCauchyPV.unique`), named by
`cauchyPV`; this file does not prove that any particular set satisfies the clauses.

As with `HasCauchyPVAt`, the predicate carries a truncated-**integrability** clause alongside the
`Tendsto` clause. Without it the `Tendsto` clause alone would be met vacuously by integrands whose
truncations are non-integrable, since a Bochner interval integral of a non-integrable function is
`0` by convention. This keeps the principal value honest and separate from ordinary integrability
of `f` (which fails at an on-curve singularity), never silently identifying the two.

## Main definitions

* `HasCauchyPVWith γ a b f S v` — the same with the excision set `S` **prescribed**; the form
  that concatenates, since adjacent subcurves must share it (`PrincipalValue/Concat.lean`)
* `HasCauchyPV γ a b f v` — some finite excision set makes the truncated integrals converge to `v`
  (the primary predicate).
* `CauchyPVExists γ a b f` — the principal value exists (`∃ v, HasCauchyPV γ a b f v`).

## Main results

* `hasCauchyPV_iff`, `cauchyPVExists_iff` — restate the predicates as their defining existentials,
  so consumers can characterize them without unfolding the definitions.
* `HasCauchyPV.intro` builds the predicate from a witnessing set `S` and its two clauses, while
  `CauchyPVExists.intro` builds existence from a `HasCauchyPV` witness.
* `HasCauchyPVAt.hasCauchyPV`, `CauchyPVExistsAt.cauchyPVExists` — the single-point principal value
  at `z₀` is the set-level principal value with `S = {z₀}`: the excision `‖γ t − z₀‖ > ε` is exactly
  the `S = {z₀}` case of the set excision.
* `HasCauchyPVWith.of_integrable_of_crossings_measure_zero` and its finite-crossings wrapper
  `HasCauchyPVWith.of_integrable_of_finite_crossings` — where
  the integrand is integrable and the curve meets the excised points on a null set of parameters
  (in particular, finitely often), the principal value is the ordinary integral **for any
  prescribed excision set**
* `HasCauchyPV.of_integrable` — if the ordinary contour integrand is interval-integrable, the empty
  excision witnesses that the principal value is the ordinary integral (as when no on-curve
  singularity of `f` obstructs integrability).
* `HasCauchyPV.zero`, `HasCauchyPV.const_mul`, `HasCauchyPV.congr_along_curve` (and their
  `CauchyPVExists` forms) — the excision-set-preserving operations: the zero integrand, scaling by a
  constant, and replacing `f` by a function agreeing with it along `γ`; these need no change of the
  witnessing set.
* `HasCauchyPV.unique`, `cauchyPV`, `HasCauchyPV.cauchyPV_eq`, `cauchyPV_zero`,
  `CauchyPVExists.hasCauchyPV_cauchyPV` — the value is well-defined (independent of the witnessing
  set), so `cauchyPV γ a b f` names it (junk value `0` when none exists).
* `HasCauchyPV.symm`, `CauchyPVExists.symm`, `cauchyPV_symm` — reversing the interval orientation
  negates the set-level principal value.
* `HasCauchyPV.add`, `HasCauchyPV.sum` (and their `CauchyPVExists` forms) — additivity in `f`;
  reconciling the summands' *different* excision sets on their union needs the curve continuous
  on `[[a, b]]`, unlike the excision-set-preserving operations above.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (the multi-point principal value
`CauchyPrincipalValueExistsOn`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of
the contour-integration roadmap, with the singular set bound existentially and the
truncated-integrability clause added.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **The Cauchy principal value with a prescribed excision set.** Identical to `HasCauchyPV`
except that the finite set `S` of excised points is an explicit parameter rather than
existentially bound, which is what makes the principal values along adjacent subcurves
concatenable. -/
def HasCauchyPVWith (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (S : Finset ℂ) (v : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        MeasureTheory.volume a b) ∧
    Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
      (𝓝[>] 0) (𝓝 v)

/-- `HasCauchyPVWith` unfolded into its two clauses — eventual integrability of the excised
integrand and convergence of the excised integrals — so consumers need not unfold the
definition. -/
theorem hasCauchyPVWith_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {v : ℂ} :
    HasCauchyPVWith γ a b f S v ↔
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
          (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        MeasureTheory.volume a b) ∧
        Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
          (𝓝[>] 0) (𝓝 v) :=
  Iff.rfl

/-- The **Cauchy principal value on a set** of the contour integral `∮_γ f` exists with value `v`:
there is a finite set `S ⊆ ℂ` such that the truncated integrand along `γ` over `[a, b]`, zeroed
within a symmetric `ε`-ball of any point of `S`, is eventually `IntervalIntegrable` and its integral
tends to `v` as `ε → 0⁺`. The set is existential so the predicate stays `S`-free, intrinsic to
`(γ, f)`; the integrability clause prevents the `Tendsto` clause from being met vacuously through
the convention that a Bochner integral of a non-integrable function is `0`. Set-level companion of
`HasCauchyPVAt` (raw `γ : ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPV (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  ∃ S : Finset ℂ, HasCauchyPVWith γ a b f S v

/-- Restatement of `HasCauchyPV` as the existence of a finite excision set making the excised
integrand eventually integrable and its integrals convergent, so consumers can characterize the
predicate without unfolding its definition. -/
theorem hasCauchyPV_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} :
    HasCauchyPV γ a b f v ↔
      ∃ S : Finset ℂ,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
            (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
            MeasureTheory.volume a b) ∧
          Tendsto (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
            (𝓝[>] 0) (𝓝 v) :=
  Iff.rfl

/-- Constructor for `HasCauchyPV` from a witnessing finite set `S` and its two clauses — eventual
integrability of the `S`-excised integrand and convergence of the excised integrals — without
unfolding the definition. -/
theorem HasCauchyPV.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} (S : Finset ℂ)
    (h_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
        (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        MeasureTheory.volume a b)
    (h_tendsto : Tendsto
        (fun ε ↦ ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        (𝓝[>] 0) (𝓝 v)) :
    HasCauchyPV γ a b f v :=
  ⟨S, h_int, h_tendsto⟩

/-- Forgetting the witness recovers the existentially-bound form. -/
theorem HasCauchyPVWith.hasCauchyPV {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {v : ℂ}
    (h : HasCauchyPVWith γ a b f S v) : HasCauchyPV γ a b f v :=
  HasCauchyPV.intro S h.1 h.2

/-- `HasCauchyPV` is exactly `HasCauchyPVWith` with the excision set existentially quantified.

This is the abstraction-preserving bridge between the two forms, and is **not** redundant with
the definition: under the module system `HasCauchyPV`'s body is not exposed outside this file,
so `Iff.rfl` proves this only here and consumers elsewhere cannot unfold their way across. The
sibling `hasCauchyPV_iff` expands the truncation body instead, which loses the abstraction. -/
theorem hasCauchyPV_iff_exists_hasCauchyPVWith {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ} :
    HasCauchyPV γ a b f v ↔ ∃ S : Finset ℂ, HasCauchyPVWith γ a b f S v :=
  Iff.rfl

/-- The Cauchy principal value on a set exists: shorthand for `∃ v, HasCauchyPV γ a b f v`. -/
def CauchyPVExists (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ v : ℂ, HasCauchyPV γ a b f v

/-- Characterization of `CauchyPVExists` as the existence of a principal value — the
eliminator/constructor interface, so downstream users need not unfold the definition. -/
theorem cauchyPVExists_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    CauchyPVExists γ a b f ↔ ∃ v, HasCauchyPV γ a b f v :=
  Iff.rfl

/-- Constructor for `CauchyPVExists` from a `HasCauchyPV` witness. -/
theorem CauchyPVExists.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) : CauchyPVExists γ a b f :=
  ⟨v, h⟩

/-- **From a point to a set.** The single-point principal value at `z₀` is the set-level principal
value with `S = {z₀}`: the single-point excision `‖γ t − z₀‖ > ε` (keep) is exactly the negation of
the set excision `∃ s ∈ {z₀}, ‖γ t − s‖ ≤ ε` (zero). -/
theorem HasCauchyPVAt.hasCauchyPV {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : HasCauchyPV γ a b f L := by
  have hbody : ∀ (ε : ℝ) (t : ℝ),
      (if ∃ s ∈ ({z₀} : Finset ℂ), ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        = if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0 := by
    intro ε t
    simp only [Finset.mem_singleton, exists_eq_left]
    by_cases h' : ‖γ t - z₀‖ ≤ ε
    · rw [if_pos h', if_neg (not_lt.mpr h')]
    · rw [if_neg h', if_pos (not_le.mp h')]
  refine ⟨{z₀}, ?_, ?_⟩
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact (intervalIntegrable_congr fun t _ => hbody ε t).mpr hε
  · refine h.tendsto.congr fun ε => ?_
    exact (intervalIntegral.integral_congr fun t _ => hbody ε t).symm

/-- Existence form of `HasCauchyPVAt.hasCauchyPV`: if the single-point principal value at `z₀`
exists, so does the set-level principal value. -/
theorem CauchyPVExistsAt.cauchyPVExists {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) : CauchyPVExists γ a b f :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  ⟨_, hL.hasCauchyPV⟩

/-- **Integrable integrand.** If the ordinary contour integrand `t ↦ f (γ t) · γ'(t)` is
`IntervalIntegrable` on `[a, b]`, then the empty excision (`S = ∅`) is inert, so the principal value
exists and equals the ordinary contour integral `∫_a^b f (γ t) · γ'(t) dt`. -/
theorem HasCauchyPV.of_integrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    HasCauchyPV γ a b f (∫ t in a..b, f (γ t) * deriv γ t) := by
  refine ⟨∅, ?_, ?_⟩
  · filter_upwards with ε
    simpa using hf_int
  · refine tendsto_const_nhds.congr fun ε => ?_
    exact intervalIntegral.integral_congr fun t _ => by simp

/-- If `z` is none of the finitely many points of `S`, then for all small enough `ε > 0` the point
`z` is farther than `ε` from every point of `S`; i.e. the excision at `S` eventually keeps `z`. -/
private theorem eventually_not_exists_mem_le (z : ℂ) (S : Finset ℂ) (h : ∀ s ∈ S, z ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∃ s ∈ S, ‖z - s‖ ≤ ε := by
  have key : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ S, ε < ‖z - s‖ := by
    rw [Filter.eventually_all_finset]
    intro s hs
    have hpos : (0 : ℝ) < ‖z - s‖ := by rw [norm_pos_iff, sub_ne_zero]; exact h s hs
    exact nhdsWithin_le_nhds (Iio_mem_nhds hpos)
  filter_upwards [key] with ε hε
  rintro ⟨s, hs, hle⟩
  exact absurd hle (not_le.mpr (hε s hs))

/-- **An integrable integrand has principal value the ordinary integral, for *any* prescribed
excision set.** Where the contour integrand is interval-integrable and the curve meets the excised
points only on a null set of parameters, shrinking the excised neighbourhoods recovers the ordinary
integral: for each fixed `ε` the excision may perturb the integrand on a set of positive measure,
but as `ε → 0⁺` the excised integrands converge almost everywhere to the original one, since the
limiting crossing set is null.

The strength here is that `S` is arbitrary: the conclusion holds for whatever excision set another
principal value happens to be witnessed by, which is what lets an arc carrying no singularity be
subtracted off via `HasCauchyPVWith.sub_right` without knowing that witness. Compare
`HasCauchyPV.of_integrable`, which proves the weaker existential form by exhibiting `S = ∅`. -/
theorem HasCauchyPVWith.of_integrable_of_crossings_measure_zero {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (S : Finset ℂ) (hγ : AEMeasurable γ (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b)
    (h_null : MeasureTheory.volume (⋃ s ∈ S, Set.uIoc a b ∩ γ ⁻¹' {s}) = 0) :
    HasCauchyPVWith γ a b f S (∫ t in a..b, f (γ t) * deriv γ t) := by
  classical
  set g : ℝ → ℂ := fun t => f (γ t) * deriv γ t with hg
  have hmeas : ∀ ε : ℝ, MeasureTheory.NullMeasurableSet {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε}
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := fun ε => by
    have hset : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} = ⋃ s ∈ S, {t | ‖γ t - s‖ ≤ ε} := by ext t; simp
    refine hset ▸ MeasureTheory.NullMeasurableSet.biUnion S.countable_toSet fun s _ => ?_
    exact nullMeasurableSet_le ((hγ.sub_const s).norm) aemeasurable_const
  have hsm : ∀ ε : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g t)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := fun ε =>
    (h_int.def'.aestronglyMeasurable.indicator₀ (hmeas ε).compl).congr
      (Filter.Eventually.of_forall fun t => by
        dsimp only
        by_cases h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
        · rw [Set.indicator_of_notMem (by simpa using h), if_pos h]
        · rw [Set.indicator_of_mem (by simpa using h), if_neg h])
  have hle : ∀ ε : ℝ, ∀ t : ℝ,
      ‖(if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g t)‖ ≤ ‖g t‖ := fun ε t => by
    by_cases h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε <;> simp [h]
  have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      Filter.Tendsto (fun ε : ℝ => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g t)
        (𝓝[>] 0) (𝓝 (g t)) := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_null] with t ht htI
    have hne : ∀ s ∈ S, γ t ≠ s := fun s hs hst =>
      ht (Set.mem_biUnion hs ⟨htI, hst⟩)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_not_exists_mem_le (γ t) S hne] with ε hε
    exact (if_neg hε).symm
  refine ⟨Filter.Eventually.of_forall fun ε =>
      h_int.mono_fun (hsm ε) (Filter.Eventually.of_forall (hle ε)), ?_⟩
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖)
    (Filter.Eventually.of_forall hsm)
    (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun t _ => hle ε t)
    h_int.norm hae

/-- Finite-crossings form of `HasCauchyPVWith.of_integrable_of_crossings_measure_zero`: a curve
meeting each excised point only finitely often meets them on a null set of parameters. This is
the form contour arguments consume: `IsPwC1ImmersionOn.finite_crossings` (HW Prop 2.2) supplies
finiteness on the closed interval, from which this follows by `Set.Finite.subset` along
`Set.uIoc_subset_uIcc`. -/
theorem HasCauchyPVWith.of_integrable_of_finite_crossings {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (S : Finset ℂ) (hγ : AEMeasurable γ (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b)
    (h_fin : ∀ s ∈ S, (Set.uIoc a b ∩ γ ⁻¹' {s}).Finite) :
    HasCauchyPVWith γ a b f S (∫ t in a..b, f (γ t) * deriv γ t) :=
  .of_integrable_of_crossings_measure_zero S hγ h_int
    ((S.finite_toSet.biUnion fun s hs => h_fin s hs).measure_zero _)

/-- **Zero integrand.** The principal value of the zero integrand is `0`, witnessed by the empty
excision: the truncated integrand is identically `0`, hence integrable with vanishing integral. -/
theorem HasCauchyPV.zero {γ : ℝ → ℂ} {a b : ℝ} : HasCauchyPV γ a b (fun _ => 0) 0 := by
  refine ⟨∅, ?_, ?_⟩
  · filter_upwards with ε
    simp
  · simp

/-- **Scaling by a constant.** Scaling the integrand by `c : ℂ` scales the principal value by `c`,
reusing the same excision set: the truncation and the integral both commute with multiplication by
the constant `c`. -/
theorem HasCauchyPV.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) (c : ℂ) : HasCauchyPV γ a b (fun z => c * f z) (c * v) := by
  obtain ⟨S, hint, htend⟩ := h
  have hbody : ∀ (ε : ℝ) (t : ℝ),
      (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else (fun z => c * f z) (γ t) * deriv γ t)
        = c * (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) := by
    intro ε t
    by_cases hc : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · simp [hc]
    · simp [hc, mul_assoc]
  refine ⟨S, ?_, ?_⟩
  · filter_upwards [hint] with ε hε
    exact (intervalIntegrable_congr fun t _ => hbody ε t).mpr (hε.const_mul c)
  · refine (htend.const_mul c).congr fun ε => ?_
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => (hbody ε t).symm

/-- **Changing the curve.** Two curves that agree on the open parameter interval
have the same principal value: both the excision test `‖γ t - s‖ ≤ ε` and the integrand
`f (γ t) * deriv γ t` are computed pointwise from the curve, the derivatives agree automatically
because the interval is open, and the endpoints do not affect an interval integral.

This is what lets a contour identity be restated along a more convenient parametrization — for
instance replacing a piece of a closed contour by the straight line it traces. -/
theorem HasCauchyPVWith.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} {v : ℂ}
    (h : HasCauchyPVWith γ₁ a b f S v) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    HasCauchyPVWith γ₂ a b f S v := by
  have h_deriv : Set.EqOn (deriv γ₁) (deriv γ₂) (Set.uIoo a b) := h_eq.deriv isOpen_Ioo
  rw [hasCauchyPVWith_iff] at h ⊢
  have hbody : ∀ ε : ℝ, ∀ t ∈ Set.uIoo a b,
      (if ∃ s ∈ S, ‖γ₁ t - s‖ ≤ ε then 0 else f (γ₁ t) * deriv γ₁ t)
        = if ∃ s ∈ S, ‖γ₂ t - s‖ ≤ ε then 0 else f (γ₂ t) * deriv γ₂ t := by
    intro ε t ht
    rw [h_eq ht, h_deriv ht]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    exact (intervalIntegrable_congr_uIoo fun t ht => hbody ε t ht).mp hε
  · exact h.2.congr fun ε => intervalIntegral.integral_congr_uIoo fun t ht => hbody ε t ht

/-- Curve congruence for the primary predicate: `HasCauchyPVWith.congr_curve` with the excision
set re-hidden, so consumers need not name it. -/
theorem HasCauchyPV.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ₁ a b f v) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    HasCauchyPV γ₂ a b f v :=
  let ⟨_, hS⟩ := hasCauchyPV_iff_exists_hasCauchyPVWith.mp h
  (hS.congr_curve h_eq).hasCauchyPV

/-- Existence form of `HasCauchyPV.congr_curve`. -/
theorem CauchyPVExists.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ₁ a b f) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    CauchyPVExists γ₂ a b f :=
  let ⟨_, hv⟩ := h
  ⟨_, hv.congr_curve h_eq⟩

/-- **Congruence along the curve.** If `f` and `g` agree along `γ` on the open interval `Set.uIoo a
b`, they share the same principal value there, with the same excision set (the endpoints are
invisible to the interval integral; the excised integrand reads `f` only through `f (γ t)`). -/
theorem HasCauchyPV.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) (hfg : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    HasCauchyPV γ a b g v := by
  obtain ⟨S, hint, htend⟩ := h
  have hbody : ∀ ε : ℝ, ∀ t ∈ Set.uIoo a b,
      (if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t)
        = if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else g (γ t) * deriv γ t := by
    intro ε t ht
    by_cases hc : ∃ s ∈ S, ‖γ t - s‖ ≤ ε
    · simp [hc]
    · simp [hc, hfg t ht]
  refine ⟨S, ?_, ?_⟩
  · filter_upwards [hint] with ε hε
    exact (intervalIntegrable_congr_uIoo fun t ht => hbody ε t ht).mp hε
  · refine htend.congr fun ε => ?_
    exact intervalIntegral.integral_congr_uIoo fun t ht => hbody ε t ht

/-- Existence form of `HasCauchyPV.zero`: the principal value of the zero integrand exists. -/
theorem CauchyPVExists.zero {γ : ℝ → ℂ} {a b : ℝ} : CauchyPVExists γ a b (fun _ => 0) :=
  .intro HasCauchyPV.zero

/-- Existence form of `HasCauchyPV.const_mul`: if the principal value of `f` exists, so does that of
`fun z => c * f z`. -/
theorem CauchyPVExists.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) (c : ℂ) : CauchyPVExists γ a b (fun z => c * f z) :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  ⟨_, hv.const_mul c⟩

/-- Existence form of `HasCauchyPV.congr_along_curve`: agreement along `γ` on `Set.uIoo a b`
transports existence of the principal value from `f` to `g`. -/
theorem CauchyPVExists.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) (hfg : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    CauchyPVExists γ a b g :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  ⟨_, hv.congr_along_curve hfg⟩

/-- The `S`-excised contour integrand `t ↦ f (γ t) · γ'(t)`, set to `0` within a symmetric
`ε`-ball of any point of the finite set `S`. This names the integrand whose truncated integral
defines the set-level principal value, keeping the enlargement-inertness proof readable. -/
private noncomputable def truncatedIntegrand (γ : ℝ → ℂ) (f : ℂ → ℂ) (S : Finset ℂ) (ε t : ℝ) :
    ℂ :=
  if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t

/-- On the level set `{x | g x = c}`, the derivative of `g` vanishes off a countable set: a point
of the level set with nonzero derivative cannot be an accumulation point of the level set (else its
derivative would be `0` by `deriv_zero_of_frequently_const`), hence it is isolated on the left in
the level set, and left-isolated points of a set in `ℝ` form a countable set. -/
private theorem countable_setOf_deriv_ne_zero_on_fiber (g : ℝ → ℂ) (c : ℂ) :
    {x : ℝ | g x = c ∧ deriv g x ≠ 0}.Countable := by
  refine (countable_setOfPred_isolated_left_within (s := {x | g x = c})).mono ?_
  rintro x ⟨hgx, hderiv⟩
  refine ⟨hgx, ?_⟩
  have hfreq : ∀ᶠ y in 𝓝[≠] x, g y ≠ c := by
    rw [← Filter.not_frequently]
    exact fun h => hderiv (deriv_zero_of_frequently_const h)
  have h2 : {y | g y = c}ᶜ ∈ 𝓝[Set.Iio x] x :=
    nhdsWithin_mono x (fun y hy => ne_of_lt hy) hfreq
  rw [Set.inter_comm, nhdsWithin_inter']
  exact Filter.inf_principal_eq_bot.mpr h2

/-- **A separating, integrable excision radius.** If the truncated integrands for `S₁` and `S₂` are
eventually integrable as `ε → 0⁺`, there is a single `ε₀ > 0` at which both are integrable and at
which distinct points of `S₁` and `S₂` are more than `2 * ε₀` apart. -/
private theorem exists_pos_separating_intervalIntegrable_truncatedIntegrand {γ : ℝ → ℂ} {a b : ℝ}
    {f : ℂ → ℂ} (S₁ S₂ : Finset ℂ)
    (hint₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₁ ε) MeasureTheory.volume a b)
    (hint₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₂ ε) MeasureTheory.volume a b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ (∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₁ ≠ s₂ → 2 * ε₀ < ‖s₁ - s₂‖) ∧
      IntervalIntegrable (truncatedIntegrand γ f S₁ ε₀) MeasureTheory.volume a b ∧
      IntervalIntegrable (truncatedIntegrand γ f S₂ ε₀) MeasureTheory.volume a b := by
  have hdist : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₁ ≠ s₂ → 2 * ε < ‖s₁ - s₂‖ := by
    rw [Filter.eventually_all_finset]
    intro s₁ hs₁
    rw [Filter.eventually_all_finset]
    intro s₂ hs₂
    rcases eq_or_ne s₁ s₂ with hEq | hNe
    · exact Filter.Eventually.of_forall fun ε hne => absurd hEq hne
    · have hpos : (0 : ℝ) < ‖s₁ - s₂‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hNe
      have h0 : ∀ᶠ ε in 𝓝 (0 : ℝ), 2 * ε < ‖s₁ - s₂‖ := by
        filter_upwards [Iio_mem_nhds (div_pos hpos (by norm_num : (0 : ℝ) < 2))] with ε hε
        rw [Set.mem_Iio] at hε; linarith
      filter_upwards [nhdsWithin_le_nhds h0] with ε hε _; exact hε
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧
      (∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₁ ≠ s₂ → 2 * ε < ‖s₁ - s₂‖) ∧
      IntervalIntegrable (truncatedIntegrand γ f S₁ ε) MeasureTheory.volume a b ∧
      IntervalIntegrable (truncatedIntegrand γ f S₂ ε) MeasureTheory.volume a b := by
    filter_upwards [self_mem_nhdsWithin, hdist, hint₁, hint₂] with ε hpos hd h1 h2
    exact ⟨hpos, hd, h1, h2⟩
  exact hev.exists

/-- **Pointwise domination of the truncated difference.** When distinct points of `S₁` and `S₂` are
more than `2 * ε₀` apart and `ε < ε₀`, the truncated-integrand difference at `ε` is bounded
pointwise by the sum of the `ε₀`-truncation norms: a point excised at `ε` by one set but not the
other is, by the `2·ε₀`-separation, more than `ε₀` from that other set — so the other set's
`ε₀`-truncation retains the full integrand value there, and that value dominates the difference. -/
private theorem norm_truncatedIntegrand_sub_le {γ : ℝ → ℂ} {f : ℂ → ℂ} {S₁ S₂ : Finset ℂ}
    {ε ε₀ : ℝ} (t : ℝ) (hεlt : ε < ε₀)
    (hP1 : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₁ ≠ s₂ → 2 * ε₀ < ‖s₁ - s₂‖) :
    ‖truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t‖ ≤
      ‖truncatedIntegrand γ f S₁ ε₀ t‖ + ‖truncatedIntegrand γ f S₂ ε₀ t‖ := by
  classical
  simp only [truncatedIntegrand]
  by_cases h1 : ∃ s ∈ S₁, ‖γ t - s‖ ≤ ε <;> by_cases h2 : ∃ s ∈ S₂, ‖γ t - s‖ ≤ ε
  · simp only [if_pos h1, if_pos h2, sub_self, norm_zero]
    positivity
  · have hfar2 : ¬ ∃ s ∈ S₂, ‖γ t - s‖ ≤ ε₀ := by
      rintro ⟨s₂, hs₂, hle₂⟩
      obtain ⟨s₁, hs₁, hle₁⟩ := h1
      have hs12 : s₁ ≠ s₂ := by rintro rfl; exact h2 ⟨s₁, hs₂, hle₁⟩
      have htri : ‖s₁ - s₂‖ ≤ ‖γ t - s₂‖ + ‖γ t - s₁‖ := by
        have he : s₁ - s₂ = (γ t - s₂) - (γ t - s₁) := by ring
        rw [he]; exact norm_sub_le _ _
      have := hP1 s₁ hs₁ s₂ hs₂ hs12
      linarith
    rw [if_pos h1, if_neg h2, if_neg hfar2, zero_sub, norm_neg]
    exact le_add_of_nonneg_left (norm_nonneg _)
  · have hfar1 : ¬ ∃ s ∈ S₁, ‖γ t - s‖ ≤ ε₀ := by
      rintro ⟨s₁, hs₁, hle₁⟩
      obtain ⟨s₂, hs₂, hle₂⟩ := h2
      have hs12 : s₁ ≠ s₂ := by rintro rfl; exact h1 ⟨s₁, hs₁, hle₂⟩
      have htri : ‖s₁ - s₂‖ ≤ ‖γ t - s₂‖ + ‖γ t - s₁‖ := by
        have he : s₁ - s₂ = (γ t - s₂) - (γ t - s₁) := by ring
        rw [he]; exact norm_sub_le _ _
      have := hP1 s₁ hs₁ s₂ hs₂ hs12
      linarith
    rw [if_neg h1, if_pos h2, if_neg hfar1, sub_zero]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [if_neg h1, if_neg h2, sub_self, norm_zero]
    positivity

/-- **Pointwise a.e. vanishing of the truncated difference.** For almost every `t`, the
truncated-integrand difference tends to `0` as `ε → 0⁺`: off the null set where `γ` meets `S₁ ∪ S₂`
with nonzero derivative, either the excess `f (γ t) · γ' t` already vanishes, or `γ t` avoids both
excision sets and both truncations eventually keep it. -/
private theorem tendsto_truncatedIntegrand_sub_ae {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (S₁ S₂ : Finset ℂ) :
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      Tendsto (fun ε => truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  classical
  have hNcount : {t : ℝ | deriv γ t ≠ 0 ∧ γ t ∈ (↑(S₁ ∪ S₂) : Set ℂ)}.Countable := by
    have hsub : {t : ℝ | deriv γ t ≠ 0 ∧ γ t ∈ (↑(S₁ ∪ S₂) : Set ℂ)} ⊆
        ⋃ c ∈ (↑(S₁ ∪ S₂) : Set ℂ), {t : ℝ | γ t = c ∧ deriv γ t ≠ 0} := by
      rintro t ⟨hd, hc⟩
      exact Set.mem_biUnion hc ⟨rfl, hd⟩
    exact ((S₁ ∪ S₂).finite_toSet.countable.biUnion
      (fun c _ => countable_setOf_deriv_ne_zero_on_fiber γ c)).mono hsub
  have hN0 : MeasureTheory.volume {t : ℝ | deriv γ t ≠ 0 ∧ γ t ∈ (↑(S₁ ∪ S₂) : Set ℂ)} = 0 :=
    hNcount.measure_zero _
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hN0] with t htN _hI
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_not] at htN
  rcases htN with hd | hc
  · have hF0 : f (γ t) * deriv γ t = 0 := by rw [hd, mul_zero]
    have hzero : (fun ε => truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t)
        = fun _ => (0 : ℂ) := by
      funext ε
      simp only [truncatedIntegrand, hF0, ite_self, sub_zero]
    rw [hzero]
    exact tendsto_const_nhds
  · rw [Finset.coe_union, Set.mem_union, not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hne1 : ∀ s ∈ S₁, γ t ≠ s := by
      intro s hs heq
      exact hc1 (by rw [heq]; exact Finset.mem_coe.mpr hs)
    have hne2 : ∀ s ∈ S₂, γ t ≠ s := by
      intro s hs heq
      exact hc2 (by rw [heq]; exact Finset.mem_coe.mpr hs)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_not_exists_mem_le (γ t) S₁ hne1,
      eventually_not_exists_mem_le (γ t) S₂ hne2] with ε h1 h2
    simp only [truncatedIntegrand, if_neg h1, if_neg h2, sub_self]

/-- **Enlargement inertness of the excision set (difference form).** For finite excision sets `S₁`
and `S₂` whose truncated integrands are eventually integrable, the difference of the two truncated
contour integrals tends to `0` as `ε → 0⁺`. On the overlap the truncations agree; the mass on the
symmetric difference sits within `ε` of finitely many points and, being dominated by a fixed-`ε₀`
truncation (using that the excision sets are finite and disjoint from each other's excess points),
is killed in the limit by dominated convergence, the excess `f (γ ·) · γ'` vanishing a.e. on each
singleton fibre of `γ`. -/
private theorem tendsto_integral_truncatedIntegrand_sub {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (S₁ S₂ : Finset ℂ)
    (hint₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₁ ε) MeasureTheory.volume a b)
    (hint₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₂ ε) MeasureTheory.volume a b) :
    Tendsto (fun ε => (∫ t in a..b, truncatedIntegrand γ f S₁ ε t)
        - ∫ t in a..b, truncatedIntegrand γ f S₂ ε t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨ε₀, hε₀pos, hP1, hII₁, hII₂⟩ :=
    exists_pos_separating_intervalIntegrable_truncatedIntegrand S₁ S₂ hint₁ hint₂
  have hltε₀ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ := nhdsWithin_le_nhds (Iio_mem_nhds hε₀pos)
  -- Measurability of the difference integrand.
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (fun t => truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hint₁, hint₂] with ε h1 h2
    exact (h1.aestronglyMeasurable_restrict_uIoc).sub (h2.aestronglyMeasurable_restrict_uIoc)
  -- The difference is dominated by the `ε₀`-truncations.
  have hbnd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      ‖truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t‖ ≤
        ‖truncatedIntegrand γ f S₁ ε₀ t‖ + ‖truncatedIntegrand γ f S₂ ε₀ t‖ := by
    filter_upwards [hltε₀] with ε hεlt
    exact MeasureTheory.ae_of_all _ (fun t _ => norm_truncatedIntegrand_sub_le t hεlt hP1)
  have hbdint : IntervalIntegrable
      (fun t => ‖truncatedIntegrand γ f S₁ ε₀ t‖ + ‖truncatedIntegrand γ f S₂ ε₀ t‖)
      MeasureTheory.volume a b := (hII₁.norm).add (hII₂.norm)
  -- Pointwise a.e. convergence to `0`: off a countable (null) set of `t`, the difference vanishes.
  have hlim : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      Tendsto (fun ε => truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 ((fun _ => (0 : ℂ)) t)) :=
    tendsto_truncatedIntegrand_sub_ae S₁ S₂
  -- Dominated convergence gives that the integral of the difference tends to `0`.
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := a) (b := b) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε t => truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t)
    (f := fun _ => (0 : ℂ))
    (bound := fun t => ‖truncatedIntegrand γ f S₁ ε₀ t‖ + ‖truncatedIntegrand γ f S₂ ε₀ t‖)
    hmeas hbnd hbdint hlim
  have hDCT' : Tendsto (fun ε => ∫ t in a..b,
      (truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hDCT
  have hCsplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in a..b, (truncatedIntegrand γ f S₁ ε t - truncatedIntegrand γ f S₂ ε t))
        = (∫ t in a..b, truncatedIntegrand γ f S₁ ε t)
          - ∫ t in a..b, truncatedIntegrand γ f S₂ ε t := by
    filter_upwards [hint₁, hint₂] with ε h1 h2
    exact intervalIntegral.integral_sub h1 h2
  exact hDCT'.congr' hCsplit

/-- **Uniqueness of the set-level principal value.** Any two values of the Cauchy principal value on
a set coincide. Unlike the single-point case, the two witnesses may use *different* finite excision
sets; enlargement inertness (`tendsto_integral_truncatedIntegrand_sub`) shows the difference of
their truncated integrals vanishes in the limit, so the two limits agree. -/
theorem HasCauchyPV.unique {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v₁ v₂ : ℂ}
    (h₁ : HasCauchyPV γ a b f v₁) (h₂ : HasCauchyPV γ a b f v₂) : v₁ = v₂ := by
  obtain ⟨S₁, hint₁, htend₁⟩ := h₁
  obtain ⟨S₂, hint₂, htend₂⟩ := h₂
  have hint₁' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₁ ε) MeasureTheory.volume a b := hint₁
  have hint₂' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f S₂ ε) MeasureTheory.volume a b := hint₂
  have htend₁' : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f S₁ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₁) := htend₁
  have htend₂' : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f S₂ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₂) := htend₂
  have hdiff := tendsto_integral_truncatedIntegrand_sub S₁ S₂ hint₁' hint₂'
  have hsub := htend₁'.sub htend₂'
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hdiff)

/-- The **value** of the set-level Cauchy principal value: the common limit when it exists, and the
junk value `0` otherwise. Read it off a `HasCauchyPV` witness via `HasCauchyPV.cauchyPV_eq`. -/
noncomputable def cauchyPV (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  open Classical in
  if h : ∃ v, HasCauchyPV γ a b f v then h.choose else 0

/-- If `HasCauchyPV γ a b f v`, then `cauchyPV γ a b f = v`: the value function reads off the
principal value whenever it exists, by uniqueness. -/
theorem HasCauchyPV.cauchyPV_eq {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) : cauchyPV γ a b f = v := by
  have hex : ∃ v, HasCauchyPV γ a b f v := ⟨v, h⟩
  rw [cauchyPV, dif_pos hex]
  exact hex.choose_spec.unique h

/-- Value form of `HasCauchyPV.congr_curve`: curves agreeing on the open parameter interval have
the same principal value, whether or not it exists (both sides are `0` when it does not). -/
theorem cauchyPV_congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) : cauchyPV γ₁ a b f = cauchyPV γ₂ a b f := by
  by_cases h : ∃ v, HasCauchyPV γ₁ a b f v
  · obtain ⟨v, hv⟩ := h
    rw [hv.cauchyPV_eq, (hv.congr_curve h_eq).cauchyPV_eq]
  · have h2 : ¬ ∃ v, HasCauchyPV γ₂ a b f v := fun ⟨v, hv⟩ =>
      h ⟨v, hv.congr_curve h_eq.symm⟩
    rw [cauchyPV, dif_neg h, cauchyPV, dif_neg h2]

/-- The value form of `HasCauchyPV.zero`: the principal value of the zero integrand is `0`. -/
@[simp]
theorem cauchyPV_zero {γ : ℝ → ℂ} {a b : ℝ} :
    cauchyPV γ a b (fun _ => 0) = 0 :=
  HasCauchyPV.zero.cauchyPV_eq

/-- The set-level Cauchy principal value over a zero-length interval is `0`. -/
theorem HasCauchyPV.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    HasCauchyPV γ a a f 0 := by
  simpa only [intervalIntegral.integral_same] using
    HasCauchyPV.of_integrable (γ := γ) (a := a) (b := a) (f := f) IntervalIntegrable.refl

/-- If the two endpoints are equal, the set-level Cauchy principal value is `0`. -/
theorem HasCauchyPV.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    HasCauchyPV γ a b f 0 := by
  subst b
  exact HasCauchyPV.refl γ a f

/-- Existence form of `HasCauchyPV.refl`: a zero-length interval always has a set-level Cauchy
principal value. -/
theorem CauchyPVExists.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    CauchyPVExists γ a a f :=
  CauchyPVExists.intro (HasCauchyPV.refl γ a f)

/-- Existence form of `HasCauchyPV.of_eq`. -/
theorem CauchyPVExists.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    CauchyPVExists γ a b f :=
  CauchyPVExists.intro (HasCauchyPV.of_eq γ hab f)

/-- Value form of `HasCauchyPV.refl`: the set-level Cauchy principal value on `[a, a]` is `0`. -/
@[simp]
theorem cauchyPV_same (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    cauchyPV γ a a f = 0 :=
  (HasCauchyPV.refl γ a f).cauchyPV_eq

/-- Value form of `HasCauchyPV.of_eq`. -/
theorem cauchyPV_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    cauchyPV γ a b f = 0 :=
  (HasCauchyPV.of_eq γ hab f).cauchyPV_eq

/-- If the set-level principal value exists, it holds at the canonical value `cauchyPV`. This
recovers a `HasCauchyPV` statement from mere existence. -/
theorem CauchyPVExists.hasCauchyPV_cauchyPV {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) : HasCauchyPV γ a b f (cauchyPV γ a b f) := by
  obtain ⟨v, hv⟩ := h
  rw [hv.cauchyPV_eq]
  exact hv

/-- Reversing the interval orientation negates a set-level Cauchy principal value. -/
theorem HasCauchyPV.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {v : ℂ}
    (h : HasCauchyPV γ a b f v) :
    HasCauchyPV γ b a f (-v) := by
  obtain ⟨S, hint, htend⟩ := hasCauchyPV_iff.mp h
  refine HasCauchyPV.intro S ?_ ?_
  · filter_upwards [hint] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) htend.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) a b).symm

/-- Existence of a set-level Cauchy principal value is invariant under reversing the interval
orientation. -/
theorem CauchyPVExists.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) :
    CauchyPVExists γ b a f :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  cauchyPVExists_iff.mpr ⟨_, hv.symm⟩

/-- Value form of `HasCauchyPV.symm`: if the set-level principal value exists on `[a, b]`, then
the value on `[b, a]` is its negative. -/
theorem cauchyPV_symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (h : CauchyPVExists γ a b f) :
    cauchyPV γ b a f = -cauchyPV γ a b f :=
  h.hasCauchyPV_cauchyPV.symm.cauchyPV_eq

/-- Enlarging the excision set preserves interval-integrability of the truncated integrand: the
extra excision at `S'` only zeroes the integrand within the `[[a, b]]`-closed set where some
`s ∈ S'` comes within `ε` of the curve, so integrability transfers from `S` to `S ∪ S'`. Needs
the curve continuous on `[[a, b]]`. -/
private theorem truncatedIntegrand_union_integrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b)) {S : Finset ℂ} {ε : ℝ} (S' : Finset ℂ)
    (h : IntervalIntegrable (truncatedIntegrand γ f S ε) MeasureTheory.volume a b) :
    IntervalIntegrable (truncatedIntegrand γ f (S ∪ S') ε) MeasureTheory.volume a b := by
  have hK_closed : IsClosed {t ∈ Set.uIcc a b | ∃ s ∈ S', ‖γ t - s‖ ≤ ε} := by
    have he : {t ∈ Set.uIcc a b | ∃ s ∈ S', ‖γ t - s‖ ≤ ε}
        = ⋃ s ∈ S', {t ∈ Set.uIcc a b | ‖γ t - s‖ ≤ ε} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      tauto
    rw [he]
    refine Set.Finite.isClosed_biUnion S'.finite_toSet fun s _ => ?_
    exact ((hγ_cont.sub continuousOn_const).norm).preimage_isClosed_of_isClosed
      (by rw [← Set.Icc_min_max]; exact isClosed_Icc) isClosed_Iic
  have hid : truncatedIntegrand γ f (S ∪ S') ε
      = Set.indicator {t : ℝ | ¬ ∃ s ∈ S', ‖γ t - s‖ ≤ ε} (truncatedIntegrand γ f S ε) := by
    funext t
    have hunion : (∃ s ∈ S ∪ S', ‖γ t - s‖ ≤ ε)
        ↔ (∃ s ∈ S, ‖γ t - s‖ ≤ ε) ∨ ∃ s ∈ S', ‖γ t - s‖ ≤ ε := by
      constructor
      · rintro ⟨s, hs, hle⟩
        rcases Finset.mem_union.mp hs with h' | h'
        exacts [Or.inl ⟨s, h', hle⟩, Or.inr ⟨s, h', hle⟩]
      · rintro (⟨s, hs, hle⟩ | ⟨s, hs, hle⟩)
        exacts [⟨s, Finset.mem_union_left _ hs, hle⟩, ⟨s, Finset.mem_union_right _ hs, hle⟩]
    simp only [truncatedIntegrand, hunion, Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h1 : ∃ s ∈ S, ‖γ t - s‖ ≤ ε <;> by_cases h2 : ∃ s ∈ S', ‖γ t - s‖ ≤ ε <;>
      simp [h1, h2]
  rw [intervalIntegrable_iff] at h ⊢
  rw [hid]
  refine (h.indicator hK_closed.measurableSet.compl).congr_fun (fun t ht => ?_)
    measurableSet_uIoc
  have htIcc : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
  by_cases h2 : ∃ s ∈ S', ‖γ t - s‖ ≤ ε
  · rw [Set.indicator_of_notMem
      (show t ∉ {t ∈ Set.uIcc a b | ∃ s ∈ S', ‖γ t - s‖ ≤ ε}ᶜ from
        fun hKc => hKc ⟨htIcc, h2⟩),
      Set.indicator_of_notMem
        (by simp only [Set.mem_ofPred_eq, not_not]; exact h2)]
  · rw [Set.indicator_of_mem
      (show t ∈ {t ∈ Set.uIcc a b | ∃ s ∈ S', ‖γ t - s‖ ≤ ε}ᶜ from
        fun hK => absurd hK.2 h2),
      Set.indicator_of_mem (by simp only [Set.mem_ofPred_eq]; exact h2)]

/-- **Additivity.** The set-level principal value is additive: if `f₁` and `f₂` each have a
principal value along `γ`, so does `f₁ + f₂`, with the sum as value. The summands may excise
different finite sets, reconciled on the union `S₁ ∪ S₂`; this needs the curve continuous on
`[[a, b]]`, unlike `const_mul`, which reuses a single excision set. -/
theorem HasCauchyPV.add {γ : ℝ → ℂ} {a b : ℝ} {f₁ f₂ : ℂ → ℂ} {v₁ v₂ : ℂ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (h₁ : HasCauchyPV γ a b f₁ v₁) (h₂ : HasCauchyPV γ a b f₂ v₂) :
    HasCauchyPV γ a b (fun z => f₁ z + f₂ z) (v₁ + v₂) := by
  obtain ⟨S₁, hint₁, htend₁⟩ := h₁
  obtain ⟨S₂, hint₂, htend₂⟩ := h₂
  have hint₁' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f₁ S₁ ε) MeasureTheory.volume a b := hint₁
  have hint₂' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f₂ S₂ ε) MeasureTheory.volume a b := hint₂
  have htend₁' : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f₁ S₁ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₁) := htend₁
  have htend₂' : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f₂ S₂ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₂) := htend₂
  have hI1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f₁ (S₁ ∪ S₂) ε) MeasureTheory.volume a b :=
    hint₁'.mono fun ε hε => truncatedIntegrand_union_integrable hγ_cont S₂ hε
  have hI2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f₂ (S₁ ∪ S₂) ε) MeasureTheory.volume a b := by
    have hc := hint₂'.mono fun ε hε => truncatedIntegrand_union_integrable hγ_cont S₁ hε
    simpa only [Finset.union_comm S₂ S₁] using hc
  have hT1 : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f₁ (S₁ ∪ S₂) ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₁) := by
    simpa using htend₁'.sub (tendsto_integral_truncatedIntegrand_sub S₁ (S₁ ∪ S₂) hint₁' hI1)
  have hT2 : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f₂ (S₁ ∪ S₂) ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v₂) := by
    simpa using htend₂'.sub (tendsto_integral_truncatedIntegrand_sub S₂ (S₁ ∪ S₂) hint₂' hI2)
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · filter_upwards [hI1, hI2] with ε h1 h2
    refine (intervalIntegrable_congr (g := fun t => truncatedIntegrand γ f₁ (S₁ ∪ S₂) ε t
      + truncatedIntegrand γ f₂ (S₁ ∪ S₂) ε t) fun t _ => ?_).mpr (h1.add h2)
    simp only [truncatedIntegrand]; split_ifs <;> ring
  · refine Filter.Tendsto.congr' ?_ (hT1.add hT2)
    filter_upwards [hI1, hI2] with ε h1 h2
    rw [← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun t _ => by
      simp only [truncatedIntegrand]; split_ifs <;> ring

/-- **Finite additivity.** A finite sum of set-level principal values is the principal value of the
summed integrand — the additive companion to `HasCauchyPV.const_mul`, built from `zero` and `add`
(hence the curve-continuity hypothesis). -/
theorem HasCauchyPV.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {f : ι → ℂ → ℂ} {v : ι → ℂ}
    {s : Finset ι} (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (h : ∀ i ∈ s, HasCauchyPV γ a b (f i) (v i)) :
    HasCauchyPV γ a b (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasCauchyPV.zero
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add hγ_cont
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Congruence along the curve off excised points**: if `f` and `g` agree along `γ` at every
parameter where `γ` avoids the finite set `P`, a principal value of `f` is one of `g` — the
witnessing excision enlarges to include `P`, and off the enlarged excision the curve avoids
`P`. Needs the curve continuous on `[[a, b]]` for the enlargement. -/
theorem HasCauchyPV.congr_along_curve_off {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {v : ℂ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b)) (P : Finset ℂ)
    (h : HasCauchyPV γ a b f v)
    (h_eq : ∀ t ∈ Set.uIoo a b, γ t ∉ (P : Set ℂ) → f (γ t) = g (γ t)) :
    HasCauchyPV γ a b g v := by
  obtain ⟨T, hint, htend⟩ := h
  have hint' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f T ε) MeasureTheory.volume a b := hint
  have hI : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (truncatedIntegrand γ f (T ∪ P) ε) MeasureTheory.volume a b :=
    hint'.mono fun ε hε => truncatedIntegrand_union_integrable hγ_cont P hε
  have hT : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f (T ∪ P) ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    have htend' : Tendsto (fun ε => ∫ t in a..b, truncatedIntegrand γ f T ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 v) := htend
    simpa using htend'.sub (tendsto_integral_truncatedIntegrand_sub T (T ∪ P) hint' hI)
  have h_body : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.uIoo a b,
      truncatedIntegrand γ f (T ∪ P) ε t = truncatedIntegrand γ g (T ∪ P) ε t := by
    intro ε hε t ht
    by_cases hex : ∃ s ∈ T ∪ P, ‖γ t - s‖ ≤ ε
    · simp only [truncatedIntegrand, if_pos hex]
    · have h_off : γ t ∉ (P : Set ℂ) := fun hp =>
        hex ⟨γ t, Finset.mem_union_right _ (Finset.mem_coe.mp hp), by simp [hε.le]⟩
      simp only [truncatedIntegrand, if_neg hex, h_eq t ht h_off]
  refine ⟨T ∪ P, ?_, ?_⟩
  · filter_upwards [hI, self_mem_nhdsWithin] with ε hε hε_pos
    exact (intervalIntegrable_congr_uIoo fun t ht => h_body ε hε_pos t ht).mp hε
  · refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact intervalIntegral.integral_congr_uIoo fun t ht => h_body ε hε_pos t ht

/-- Existence form of `HasCauchyPV.add`. -/
theorem CauchyPVExists.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (hf : CauchyPVExists γ a b f) (hg : CauchyPVExists γ a b g) :
    CauchyPVExists γ a b (fun z => f z + g z) :=
  let ⟨_, hvf⟩ := cauchyPVExists_iff.mp hf
  let ⟨_, hvg⟩ := cauchyPVExists_iff.mp hg
  ⟨_, hvf.add hγ_cont hvg⟩

/-- Existence form of `HasCauchyPV.sum`. -/
theorem CauchyPVExists.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {f : ι → ℂ → ℂ} {s : Finset ι}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (h : ∀ i ∈ s, CauchyPVExists γ a b (f i)) :
    CauchyPVExists γ a b (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using HasCauchyPV.zero⟩
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact CauchyPVExists.add hγ_cont (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end TauCeti.Contour
