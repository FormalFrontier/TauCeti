/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# The Cauchy principal value of a contour integral at a point (Hungerbühler–Wasem)

For a curve `γ : ℝ → ℂ` on `[a, b]`, an integrand `f : ℂ → ℂ`, and a point `z₀ ∈ ℂ`, this file
defines the **Cauchy principal value** of the contour integral `∮_γ f` *excising a symmetric
`ε`-ball about `z₀`*: the limit as `ε → 0⁺` of the truncated integral
`∫_a^b 𝟙[‖γ t − z₀‖ > ε] · f (γ t) · γ'(t) dt`. This is the value one must use in place of the
ordinary contour integral exactly when a singularity of `f` sits *on* the curve at `z₀`, where the
integrand is not integrable; away from `z₀` the truncation is eventually inert and the principal
value collapses to the ordinary integral (`HasCauchyPVAt.of_avoidance`).

The predicate carries **two** conditions: that the truncated integrand is (eventually) genuinely
`IntervalIntegrable`, and that the truncated integrals converge. The integrability clause is
essential: without it the `Tendsto` clause alone is met vacuously by functions whose truncations are
non-integrable, since a Bochner interval integral of a non-integrable function is `0` by convention.
This keeps the principal value honest and separate from ordinary integrability of `f` (which fails
at the on-curve singularity), never silently identifying the two.

This is the single-point companion of the roadmap's `HasCauchyPV` predicate: `HasCauchyPVAt`
symmetrically excises one prescribed point `z₀`, the case that defines the generalized winding
number `n_{z₀}(γ) = (2πi)⁻¹ · PV ∮_γ dz/(z − z₀)` and that feeds the on-curve residue theory
(Hungerbühler–Wasem, arXiv:1808.00997). The naming mirrors Mathlib's `MeromorphicAt` (at a point)
versus `MeromorphicOn` (on a set).

## Main definitions

* `HasCauchyPVAt γ a b f z₀ L` — the truncations are eventually integrable and their integrals tend
  to `L` (the primary predicate).
* `cauchyPVAt γ a b f z₀` — the value of that limit (`limUnder`-based; junk when it does not exist).
* `CauchyPVExistsAt γ a b f z₀` — the principal value exists (`∃ L, HasCauchyPVAt γ a b f z₀ L`).

## Main results

* `hasCauchyPVAt_iff` — restates the predicate as its two defining clauses, so consumers can
  characterize `HasCauchyPVAt` without unfolding its hidden body; the value `cauchyPVAt` is read off
  a witness through `HasCauchyPVAt.cauchyPVAt_eq`.
* `HasCauchyPVAt.intro` — build the predicate from its two clauses; `HasCauchyPVAt.tendsto`,
  `HasCauchyPVAt.eventually_intervalIntegrable` — the clauses as named accessors;
  `HasCauchyPVAt.cauchyPVAt_eq`, `HasCauchyPVAt.unique` — the value and its uniqueness;
  `cauchyPVExistsAt_iff`, `CauchyPVExistsAt.intro`, `CauchyPVExistsAt.hasCauchyPVAt_cauchyPVAt` —
  package/unpack existence and recover the predicate at `cauchyPVAt`.
* `HasCauchyPVAt.congr_along_curve`, `cauchyPVAt_congr_along_curve` — the integrand only matters
  along `γ` on `[a, b]`;
* `HasCauchyPVAt.congr_curve_ae`, `CauchyPVExistsAt.congr_curve_ae`, `cauchyPVAt_congr_curve_ae`
  — the *curve* only matters up to null sets: the principal value is unchanged when the curves
  agree almost everywhere on the integration interval and their derivatives agree almost
  everywhere *where the curve misses `z₀`* (the truncation deletes the integrand at `z₀`);
  `HasCauchyPVAt.congr_curve`, `CauchyPVExistsAt.congr_curve`, `cauchyPVAt_congr_curve` — the
  pointwise corollaries, needing agreement only on the open interval `Set.uIoo a b`;
  `HasCauchyPVAt.zero`, `HasCauchyPVAt.const_mul`, `HasCauchyPVAt.add`, `HasCauchyPVAt.sum` (and the
  `CauchyPVExistsAt` forms) — the principal value is `ℂ`-linear in the integrand, including over
  finite sums.
* `HasCauchyPVAt.of_avoidance` — if `γ` avoids `z₀` on `[a, b]` and the integrand is integrable
  there, the principal value is the ordinary integral (`cauchyPVExistsAt_of_avoidance` is the
  existence form).
* `HasCauchyPVAt.translate`, `CauchyPVExistsAt.translate`, `cauchyPVAt_translate` — simultaneous
  translation of the curve, point, and integrand preserves the principal value.
* `HasCauchyPVAt.const_mul_curve`, `CauchyPVExistsAt.const_mul_curve`,
  `cauchyPVAt_const_mul_curve` — simultaneous nonzero scaling of the curve and point, with the
  integrand rescaled by `z ↦ c⁻¹ * f (c⁻¹ * z)`, preserves the principal value; the value form
  needs no existence hypothesis.
* `HasCauchyPVAt.symm`, `CauchyPVExistsAt.symm`, `cauchyPVAt_symm` — reversing the interval
  orientation negates the single-point principal value.
* `HasCauchyPVAt.concat` — the principal values on `[a, b]` and `[b, c]` add
  (`CauchyPVExistsAt.concat` is the existence form).

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project, file
`ForMathlib/ClassicalCPV.lean`, specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of
the contour-integration roadmap, and strengthened with the truncated-integrability clause.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The **Cauchy principal value at `z₀`** of the contour integral `∮_γ f` exists with value `L`:
the truncated integrand along `γ` over `[a, b]`, excluding the symmetric `ε`-ball about `z₀`, is
eventually `IntervalIntegrable`, and its integral tends to `L` as `ε → 0⁺`. The integrability clause
prevents the `Tendsto` clause from being met vacuously through the convention that a Bochner
integral of a non-integrable function is `0`. Primary API predicate (raw `γ : ℝ → ℂ`, `[a, b]`). -/
def HasCauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) (L : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L)

/-- Restatement of `HasCauchyPVAt` as the conjunction of its two defining clauses — eventual
integrability of the excised integrand and convergence of the excised integrals — so consumers can
characterize the predicate without unfolding its definition. -/
theorem hasCauchyPVAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ} :
    HasCauchyPVAt γ a b f z₀ L ↔
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
          (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
        Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
          (𝓝[>] 0) (𝓝 L) :=
  Iff.rfl

/-- The **Cauchy principal value at `z₀`** of `∮_γ f`, excluding the symmetric `ε`-ball about `z₀`.
`limUnder`-based; returns junk when the limit does not exist, so use `HasCauchyPVAt` for the
predicate and `HasCauchyPVAt.cauchyPVAt_eq` to read the value off it. -/
def cauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value at `z₀` exists: shorthand for `∃ L, HasCauchyPVAt γ a b f z₀ L`. -/
def CauchyPVExistsAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, HasCauchyPVAt γ a b f z₀ L

/-- Characterization of `CauchyPVExistsAt` as the existence of a principal value — the
eliminator/constructor interface, so downstream users need not unfold the definition. -/
theorem cauchyPVExistsAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b f z₀ ↔ ∃ L, HasCauchyPVAt γ a b f z₀ L :=
  Iff.rfl

/-- Constructor for `CauchyPVExistsAt` from a `HasCauchyPVAt` witness. -/
theorem CauchyPVExistsAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : CauchyPVExistsAt γ a b f z₀ :=
  ⟨L, h⟩

/-- **The `ε`-truncated integrand is interval-integrable from a bound off the ball**: whenever
`f ∘ γ` is bounded by `M` at distance `> ε` from `z₀` and the truncated integrand is
a.e.-strongly measurable, the truncated integrand is dominated by `M · ‖deriv γ‖`. -/
theorem intervalIntegrable_truncated_mul_deriv {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    {a b M ε : ℝ}
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    (h_aesm : MeasureTheory.AEStronglyMeasurable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (h_bd : ∀ t : ℝ, ε < ‖γ t - z₀‖ → ‖f (γ t)‖ ≤ M) :
    IntervalIntegrable (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      MeasureTheory.volume a b := by
  refine (hderiv_int.norm.const_mul M).mono_fun h_aesm
    (Filter.Eventually.of_forall fun t => ?_)
  -- β-reduce the two sides of the a.e. bound
  change ‖if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0‖ ≤ ‖M * ‖deriv γ t‖‖
  by_cases h_far : ‖γ t - z₀‖ > ε
  · rw [if_pos h_far, norm_mul]
    calc ‖f (γ t)‖ * ‖deriv γ t‖
        ≤ M * ‖deriv γ t‖ := mul_le_mul_of_nonneg_right (h_bd t h_far) (norm_nonneg _)
      _ ≤ ‖M * ‖deriv γ t‖‖ := le_abs_self _
  · rw [if_neg h_far, norm_zero]
    positivity

/-- Constructor for `HasCauchyPVAt` from its two clauses — eventual integrability of the excised
integrand and convergence of the excised integrals — without unfolding the definition. -/
theorem HasCauchyPVAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b)
    (htendsto : Tendsto
      (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPVAt γ a b f z₀ L :=
  ⟨hint, htendsto⟩

/-- The convergence clause of `HasCauchyPVAt`: the excised integrals tend to the value. -/
theorem HasCauchyPVAt.tendsto {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L) :=
  h.2

/-- The integrability clause of `HasCauchyPVAt`: the excised integrand is eventually integrable. -/
theorem HasCauchyPVAt.eventually_intervalIntegrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    {L : ℂ} (h : HasCauchyPVAt γ a b f z₀ L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b :=
  h.1

/-- If `HasCauchyPVAt γ a b f z₀ L`, then `cauchyPVAt γ a b f z₀ = L`: the value function reads off
the limit whenever it exists. -/
theorem HasCauchyPVAt.cauchyPVAt_eq {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : cauchyPVAt γ a b f z₀ = L :=
  h.2.limUnder_eq

/-- The value of the Cauchy principal value at `z₀` is unique. -/
theorem HasCauchyPVAt.unique {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h₁ : HasCauchyPVAt γ a b f z₀ L₁) (h₂ : HasCauchyPVAt γ a b f z₀ L₂) : L₁ = L₂ :=
  tendsto_nhds_unique h₁.2 h₂.2

/-- If the principal value exists, it holds at the canonical value `cauchyPVAt`. This recovers a
`HasCauchyPVAt` statement from mere existence, as the winding-number value definition needs. -/
theorem CauchyPVExistsAt.hasCauchyPVAt_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    HasCauchyPVAt γ a b f z₀ (cauchyPVAt γ a b f z₀) := by
  obtain ⟨_, hL⟩ := h
  rwa [hL.cauchyPVAt_eq]

/-- The principal value depends on the integrand only through its values along `γ` on the open
interval between `a` and `b`: if `f = g` on the image of `γ` restricted to `Set.uIoo a b`, their
principal values agree (endpoint values are invisible to the interval integral). -/
theorem HasCauchyPVAt.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (h_eq : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    HasCauchyPVAt γ a b g z₀ L := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    refine (intervalIntegrable_congr_uIoo fun t ht => ?_).mp hε
    simp only [h_eq t ht]
  · refine Filter.Tendsto.congr (fun ε => intervalIntegral.integral_congr_uIoo fun t ht => ?_) h.2
    simp only [h_eq t ht]

/-- Value form of `HasCauchyPVAt.congr_along_curve`: the raw `cauchyPVAt` value only depends on
the integrand along `γ` on the open interval between `a` and `b`. -/
theorem cauchyPVAt_congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    cauchyPVAt γ a b f z₀ = cauchyPVAt γ a b g z₀ := by
  unfold cauchyPVAt
  congr 1
  ext ε
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  simp only [h_eq t ht]

/-- `EqOn` on the open interval gives almost-everywhere equality on the half-open integration
interval: the two differ only at the right endpoint, which is null. -/
private theorem aeEq_restrict_uIoc_of_eqOn_uIoo {u v : ℝ → ℂ} {a b : ℝ}
    (h : Set.EqOn u v (Set.uIoo a b)) :
    u =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] v := by
  -- `uIoc` and `uIoo` differ only at the right endpoint, so they restrict the measure equally.
  have hrestrict : MeasureTheory.volume.restrict (Set.uIoc a b)
      = MeasureTheory.volume.restrict (Set.uIoo a b) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc.symm
  rw [hrestrict]
  exact h.aeEq_restrict measurableSet_Ioo

/-- The `ε`-truncated integrands of two curves that agree almost everywhere — with derivatives
agreeing almost everywhere off `z₀` — are themselves equal almost everywhere, for every positive
`ε`. Positivity is what makes the derivative hypothesis enough: at a point with `γ₁ t = z₀` the
truncation deletes both integrands. -/
private theorem truncated_integrand_congr_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t)
    {ε : ℝ} (hε : 0 < ε) :
    (fun t => if ‖γ₁ t - z₀‖ > ε then f (γ₁ t) * deriv γ₁ t else 0)
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
    (fun t => if ‖γ₂ t - z₀‖ > ε then f (γ₂ t) * deriv γ₂ t else 0) := by
  filter_upwards [h_eq, h_deriv] with t ht htd
  by_cases hz : γ₁ t = z₀
  · rw [if_neg, if_neg] <;> simp [hz, ← ht, hε.not_gt]
  · simp only [ht, htd hz]

/-- **The principal value depends on the curve only up to null sets.** If `γ₁` and `γ₂` agree
almost everywhere on the integration interval, and their derivatives agree almost everywhere
*where the curve misses `z₀`*, their contour principal values agree.

Derivative agreement is only needed off `z₀`: the `ε`-truncation deletes the integrand wherever
`‖γ t - z₀‖ ≤ ε`, so for the positive `ε` the principal value ranges over, a point with
`γ₁ t = z₀` contributes `0` whatever the derivative there is. Curve agreement alone is still not
enough — the integrand contains `deriv γ`. -/
theorem HasCauchyPVAt.congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ₁ a b f z₀ L)
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    HasCauchyPVAt γ₂ a b f z₀ L := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, self_mem_nhdsWithin] with ε hε hpos
    exact (intervalIntegrable_congr_ae
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hpos))).mp hε
  · refine Filter.Tendsto.congr' ?_ h.2
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact intervalIntegral.integral_congr_ae_restrict
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hε))

/-- The principal value depends on the **curve** only through its values on the open interval
between `a` and `b`. Agreement on the *open* interval is enough even though the integrand involves
`deriv γ`, because an open set is a neighbourhood of each of its points (`Set.EqOn.deriv`), and
the endpoints are invisible to the interval integral. -/
theorem HasCauchyPVAt.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ₁ a b f z₀ L) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    HasCauchyPVAt γ₂ a b f z₀ L :=
  h.congr_curve_ae (aeEq_restrict_uIoc_of_eqOn_uIoo h_eq)
    ((aeEq_restrict_uIoc_of_eqOn_uIoo (h_eq.deriv isOpen_Ioo)).mono fun _ ht _ => ht)

/-- Existence form of `HasCauchyPVAt.congr_curve_ae`. -/
theorem CauchyPVExistsAt.congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ₁ a b f z₀)
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    CauchyPVExistsAt γ₂ a b f z₀ :=
  let ⟨_, hL⟩ := h
  CauchyPVExistsAt.intro (hL.congr_curve_ae h_eq h_deriv)

/-- Existence form of `HasCauchyPVAt.congr_curve`. -/
theorem CauchyPVExistsAt.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ₁ a b f z₀) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    CauchyPVExistsAt γ₂ a b f z₀ :=
  let ⟨_, hL⟩ := h
  CauchyPVExistsAt.intro (hL.congr_curve h_eq)

/-- Value form of `HasCauchyPVAt.congr_curve_ae`: the raw `cauchyPVAt` value is unchanged when the
curves agree almost everywhere on the integration interval and their derivatives agree almost
everywhere where the curve misses `z₀`. Curve equality alone does not suffice — the integrand
contains `deriv γ`. -/
theorem cauchyPVAt_congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    cauchyPVAt γ₁ a b f z₀ = cauchyPVAt γ₂ a b f z₀ := by
  have hev : (fun ε => ∫ t in a..b, if ‖γ₁ t - z₀‖ > ε then f (γ₁ t) * deriv γ₁ t else 0)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε => ∫ t in a..b, if ‖γ₂ t - z₀‖ > ε then f (γ₂ t) * deriv γ₂ t else 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact intervalIntegral.integral_congr_ae_restrict
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hε))
  unfold cauchyPVAt Filter.limUnder
  rw [Filter.map_congr hev]

/-- Value form of `HasCauchyPVAt.congr_curve`. -/
theorem cauchyPVAt_congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    cauchyPVAt γ₁ a b f z₀ = cauchyPVAt γ₂ a b f z₀ :=
  cauchyPVAt_congr_curve_ae (aeEq_restrict_uIoc_of_eqOn_uIoo h_eq)
    ((aeEq_restrict_uIoc_of_eqOn_uIoo (h_eq.deriv isOpen_Ioo)).mono fun _ ht _ => ht)

/-- Scalar multiplication: if the principal value of `f` is `L`, that of `c • f` is `c • L`. -/
theorem HasCauchyPVAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt γ a b (fun z => c * f z) z₀ (c * L) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    exact (intervalIntegrable_congr (g := fun t => c * if ‖γ t - z₀‖ > ε
      then f (γ t) * deriv γ t else 0) fun t _ => by
        simp only []; split_ifs <;> ring).mpr (hε.const_mul c)
  · refine Filter.Tendsto.congr (fun ε => ?_) (h.2.const_mul c)
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by simp only []; split_ifs <;> ring

/-- Additivity: the principal values of `f` and `g` add to that of `f + g`. Together with
`HasCauchyPVAt.const_mul` this is the `ℂ`-linearity of the principal value in the integrand. -/
theorem HasCauchyPVAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVAt γ a b f z₀ L₁) (hg : HasCauchyPVAt γ a b g z₀ L₂) :
    HasCauchyPVAt γ a b (fun z => f z + g z) z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with ε hfi hgi
    refine (intervalIntegrable_congr (g := fun t =>
      (if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
        + if ‖γ t - z₀‖ > ε then g (γ t) * deriv γ t else 0) fun t _ => ?_).mpr (hfi.add hgi)
    simp only [gt_iff_lt]
    split_ifs <;> simp [add_mul]
  · refine Filter.Tendsto.congr' ?_ (hf.2.add hg.2)
    filter_upwards [hf.1, hg.1] with ε hfi hgi
    rw [← intervalIntegral.integral_add hfi hgi]
    exact intervalIntegral.integral_congr fun t _ => by split_ifs <;> ring

/-- The principal value of the zero integrand is `0` — the additive identity for
`HasCauchyPVAt.add`. -/
theorem HasCauchyPVAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    HasCauchyPVAt γ a b (fun _ => 0) z₀ 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards with ε
    simpa only [zero_mul, ite_self] using intervalIntegrable_const
  · simpa only [zero_mul, ite_self, intervalIntegral.integral_zero] using tendsto_const_nhds

/-- The value form of `HasCauchyPVAt.zero`: the principal value of the zero integrand is `0`. -/
@[simp]
theorem cauchyPVAt_zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    cauchyPVAt γ a b (fun _ => 0) z₀ = 0 :=
  HasCauchyPVAt.zero.cauchyPVAt_eq

/-- The Cauchy principal value at a single point over a zero-length interval is `0`. -/
theorem HasCauchyPVAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a a f z₀ 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards with ε
    exact IntervalIntegrable.refl
  · simpa only [intervalIntegral.integral_same] using tendsto_const_nhds (x := (0 : ℂ))

/-- If the two endpoints are equal, the single-point Cauchy principal value is `0`. -/
theorem HasCauchyPVAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a b f z₀ 0 := by
  subst b
  exact HasCauchyPVAt.refl γ a f z₀

/-- Existence form of `HasCauchyPVAt.refl`: a zero-length interval always has a single-point
Cauchy principal value. -/
theorem CauchyPVExistsAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a a f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.refl γ a f z₀)

/-- Existence form of `HasCauchyPVAt.of_eq`. -/
theorem CauchyPVExistsAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a b f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.of_eq γ hab f z₀)

/-- Value form of `HasCauchyPVAt.refl`: the single-point Cauchy principal value on `[a, a]` is
`0`. -/
@[simp]
theorem cauchyPVAt_same (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a a f z₀ = 0 :=
  (HasCauchyPVAt.refl γ a f z₀).cauchyPVAt_eq

/-- Value form of `HasCauchyPVAt.of_eq`. -/
theorem cauchyPVAt_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a b f z₀ = 0 :=
  (HasCauchyPVAt.of_eq γ hab f z₀).cauchyPVAt_eq

/-- **Finite additivity.** The principal value of a finite sum of integrands is the sum of their
principal values. With `HasCauchyPVAt.zero` and `HasCauchyPVAt.add` this extends the `ℂ`-linearity
of the principal value to finite sums, as the generalized residue theorem's residue sum needs. -/
theorem HasCauchyPVAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, HasCauchyPVAt γ a b (f i) z₀ (L i)) :
    HasCauchyPVAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasCauchyPVAt.zero
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Avoidance.** If `γ` stays away from `z₀` throughout `[a, b]` and the ordinary contour
integrand is integrable there, the symmetric excision is eventually inert, so the principal value
exists and equals the ordinary contour integral. -/
theorem HasCauchyPVAt.of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    HasCauchyPVAt γ a b f z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_uIcc.exists_isMinOn
    Set.nonempty_uIcc (h_cont.sub continuousOn_const).norm
  have hpos : 0 < ‖γ t₀ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  refine ⟨?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
    refine (intervalIntegrable_congr fun t ht => ?_).mpr hf_int
    exact if_pos (lt_of_lt_of_le hε.2 (ht₀_min (Set.uIoc_subset_uIcc ht)))
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioo 0 ‖γ t₀ - z₀‖, Ioo_mem_nhdsGT hpos, fun ε hε => ?_⟩
    exact intervalIntegral.integral_congr fun t ht =>
      (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

/-- **Concatenation.** The principal values along adjacent subcurves `[a, b]` and `[b, c]` add to
the principal value along `[a, c]`. The integrability of the excised integrand across `[a, c]` and
the additivity of the integral both follow from the two given principal values, so no ordering or
separate integrability hypothesis is needed. -/
theorem HasCauchyPVAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPVAt γ a b f z₀ L₁) (h_bc : HasCauchyPVAt γ b c f z₀ L₂) :
    HasCauchyPVAt γ a c f z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact hab_int.trans hbc_int
  · refine Filter.Tendsto.congr' ?_ (h_ab.2.add h_bc.2)
    filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact intervalIntegral.integral_add_adjacent_intervals hab_int hbc_int

/-- Existence form of `HasCauchyPVAt.of_avoidance`. -/
theorem cauchyPVExistsAt_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    CauchyPVExistsAt γ a b f z₀ :=
  ⟨_, HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int⟩

/-- Existence-level scalar multiplication: scaling preserves existence of the principal value. -/
theorem CauchyPVExistsAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt γ a b (fun z => c * f z) z₀ :=
  let ⟨_, hL⟩ := h
  ⟨_, hL.const_mul c⟩

/-- Existence-level additivity: existence of the principal values of `f` and `g` gives that of
`f + g`. -/
theorem CauchyPVExistsAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : CauchyPVExistsAt γ a b f z₀) (hg : CauchyPVExistsAt γ a b g z₀) :
    CauchyPVExistsAt γ a b (fun z => f z + g z) z₀ :=
  let ⟨_, hLf⟩ := hf
  let ⟨_, hLg⟩ := hg
  ⟨_, hLf.add hLg⟩

/-- Existence-level: the zero integrand has a principal value. -/
theorem CauchyPVExistsAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b (fun _ => 0) z₀ :=
  ⟨0, HasCauchyPVAt.zero⟩

/-- Existence-level finite additivity: if each summand has a principal value, so does the finite
sum of integrands. -/
theorem CauchyPVExistsAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, CauchyPVExistsAt γ a b (f i) z₀) :
    CauchyPVExistsAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using HasCauchyPVAt.zero⟩
  | @insert j s hj ih =>
    obtain ⟨Lj, hLj⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨Ls, hLs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨Lj + Ls, by simpa only [Finset.sum_insert hj] using hLj.add hLs⟩

/-- Simultaneously translating the curve and the excision point preserves a single-point Cauchy
principal value, provided the integrand is translated back by the same amount. -/
theorem HasCauchyPVAt.translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) L := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    refine (intervalIntegrable_congr fun t _ => ?_).mpr hε
    simp [add_sub_add_right_eq_sub, add_sub_cancel_right, deriv_add_const]
  · refine h.tendsto.congr fun ε => ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp [add_sub_add_right_eq_sub, add_sub_cancel_right, deriv_add_const]

/-- Existence form of `HasCauchyPVAt.translate`: simultaneous translation preserves existence of a
single-point Cauchy principal value. -/
theorem CauchyPVExistsAt.translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hL.translate c)

/-- Value form of `HasCauchyPVAt.translate`: simultaneous translation preserves the single-point
Cauchy principal value. -/
theorem cauchyPVAt_translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) :
    cauchyPVAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c)
      = cauchyPVAt γ a b f z₀ := by
  unfold cauchyPVAt
  congr 1
  ext ε
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [add_sub_add_right_eq_sub, add_sub_cancel_right, deriv_add_const]

/-- Pointwise identity behind the scaling lemmas: multiplying the curve and excision point by a
nonzero `c` and rescaling the integrand by `z ↦ c⁻¹ * f (c⁻¹ * z)` turns the scaled truncated
integrand at radius `ε` into the original truncated integrand at radius `ε / ‖c‖`. The rescaling
factor `c⁻¹` cancels the derivative factor `c`, and the excision radius rescales by `‖c‖`. Shared by
`HasCauchyPVAt.const_mul_curve` and `cauchyPVAt_const_mul_curve`. -/
private theorem truncated_const_mul_curve_eq {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0)
    (ε t : ℝ) :
    (if ‖c * γ t - c * z₀‖ > ε then
        (fun z => c⁻¹ * f (c⁻¹ * z)) (c * γ t) * deriv (fun t => c * γ t) t else 0)
      = if ‖γ t - z₀‖ > ε / ‖c‖ then f (γ t) * deriv γ t else 0 := by
  by_cases hεt : ‖γ t - z₀‖ > ε / ‖c‖
  · have hscaled : ‖c * γ t - c * z₀‖ > ε := by
      rw [← mul_sub, norm_mul]
      have hmul := mul_lt_mul_of_pos_right hεt (norm_pos_iff.mpr hc)
      have hmul' : ε < ‖γ t - z₀‖ * ‖c‖ := by
        simpa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc)] using hmul
      simpa [mul_comm] using hmul'
    rw [if_pos hscaled, if_pos hεt, deriv_const_mul_field]
    simp only [inv_mul_cancel_left₀ hc]
    rw [mul_mul_mul_comm, inv_mul_cancel₀ hc, one_mul]
  · have hscaled : ¬ ‖c * γ t - c * z₀‖ > ε := by
      rw [← mul_sub, norm_mul, not_lt]
      rw [not_lt] at hεt
      have hmul := mul_le_mul_of_nonneg_right hεt (norm_nonneg c)
      rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc), mul_comm] at hmul
    rw [if_neg hscaled, if_neg hεt]

/-- Simultaneously scaling the curve and the excision point by a nonzero complex number `c`
preserves a single-point Cauchy principal value, provided the integrand is rescaled by
`z ↦ c⁻¹ * f (c⁻¹ * z)`: the excision radius rescales by `‖c‖` and, after this rescaling, the two
truncated integrands agree along the scaled curve. -/
theorem HasCauchyPVAt.const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) {c : ℂ} (hc : c ≠ 0) :
    HasCauchyPVAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀) L := by
  have hscale : Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      Filter.TendstoNhdsWithinIoi.mul_const (b := ‖c‖⁻¹) (c := 0)
        (inv_pos.mpr (norm_pos_iff.mpr hc)) (tendsto_id (x := 𝓝[>] (0 : ℝ)))
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [hscale.eventually h.eventually_intervalIntegrable] with ε hε
    exact (intervalIntegrable_congr fun t _ => truncated_const_mul_curve_eq hc ε t).mpr hε
  · refine h.tendsto.comp hscale |>.congr' ?_
    filter_upwards with ε
    exact intervalIntegral.integral_congr fun t _ => (truncated_const_mul_curve_eq hc ε t).symm

/-- Existence form of `HasCauchyPVAt.const_mul_curve`: nonzero scaling of the curve and excision
point preserves existence of a single-point Cauchy principal value. -/
theorem CauchyPVExistsAt.const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) {c : ℂ} (hc : c ≠ 0) :
    CauchyPVExistsAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hL.const_mul_curve hc)

/-- Reindexing a `limUnder` by a self-map of the source filter that fixes it leaves the value
unchanged: if `Filter.map φ F = F`, then `limUnder F (g ∘ φ) = limUnder F g`, even when the limit
does not exist. -/
private theorem limUnder_comp_of_map_eq {α : Type*} {β : Type*} [TopologicalSpace β] [Nonempty β]
    {F : Filter α} {φ : α → α} (hφ : Filter.map φ F = F) (g : α → β) :
    Filter.limUnder F (g ∘ φ) = Filter.limUnder F g := by
  unfold Filter.limUnder
  rw [← Filter.map_map, hφ]

/-- Value form of `HasCauchyPVAt.const_mul_curve`: simultaneous nonzero scaling of the curve and the
excision point preserves the raw single-point Cauchy principal *value*, with no existence
hypothesis. Scaling only reindexes the excision radius by the order-isomorphism `ε ↦ ε / ‖c‖`, which
fixes the filter `𝓝[>] 0`, so the underlying `limUnder` is unchanged even when it does not
converge. -/
theorem cauchyPVAt_const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0) :
    cauchyPVAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀)
      = cauchyPVAt γ a b f z₀ := by
  have hmap : Filter.map (fun ε : ℝ => ε / ‖c‖) (𝓝[>] (0 : ℝ)) = 𝓝[>] (0 : ℝ) := by
    have hx : (0 : ℝ) < ‖c‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hc)
    have hcne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hsurj : Function.Surjective (fun x : ℝ => ‖c‖⁻¹ * x) := fun y =>
      ⟨‖c‖ * y, by simpa using inv_mul_cancel_left₀ hcne y⟩
    have hfun : (fun ε : ℝ => ε / ‖c‖) = fun ε => ‖c‖⁻¹ * ε := funext fun ε => div_eq_inv_mul ε ‖c‖
    rw [hfun]
    conv_lhs => rw [← comap_mulLeft_nhdsGT_zero hx]
    exact Filter.map_comap_of_surjective hsurj _
  have hbodyeq : (fun ε : ℝ => ∫ t in a..b, if ‖c * γ t - c * z₀‖ > ε then
        (fun z => c⁻¹ * f (c⁻¹ * z)) (c * γ t) * deriv (fun t => c * γ t) t else 0)
      = (fun ε' : ℝ => ∫ t in a..b, if ‖γ t - z₀‖ > ε' then f (γ t) * deriv γ t else 0)
          ∘ (fun ε => ε / ‖c‖) :=
    funext fun ε =>
      intervalIntegral.integral_congr fun t _ => truncated_const_mul_curve_eq hc ε t
  calc cauchyPVAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀)
      = Filter.limUnder (𝓝[>] (0 : ℝ))
          ((fun ε' : ℝ => ∫ t in a..b, if ‖γ t - z₀‖ > ε' then f (γ t) * deriv γ t else 0)
            ∘ (fun ε => ε / ‖c‖)) := congrArg (Filter.limUnder (𝓝[>] (0 : ℝ))) hbodyeq
    _ = Filter.limUnder (𝓝[>] (0 : ℝ))
          (fun ε' : ℝ => ∫ t in a..b, if ‖γ t - z₀‖ > ε' then f (γ t) * deriv γ t else 0) :=
        limUnder_comp_of_map_eq hmap _
    _ = cauchyPVAt γ a b f z₀ := rfl

/-- Reversing the interval orientation negates a single-point Cauchy principal value. -/
theorem HasCauchyPVAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    HasCauchyPVAt γ b a f z₀ (-L) := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) h.tendsto.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) a b).symm

/-- Existence of a single-point Cauchy principal value is invariant under reversing the interval
orientation. -/
theorem CauchyPVExistsAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    CauchyPVExistsAt γ b a f z₀ :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  cauchyPVExistsAt_iff.mpr ⟨_, hL.symm⟩

/-- Value form of `HasCauchyPVAt.symm`: if the single-point principal value exists on `[a, b]`,
then the value on `[b, a]` is its negative. -/
theorem cauchyPVAt_symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    cauchyPVAt γ b a f z₀ = -cauchyPVAt γ a b f z₀ :=
  h.hasCauchyPVAt_cauchyPVAt.symm.cauchyPVAt_eq

/-- Existence form of `HasCauchyPVAt.concat`. -/
theorem CauchyPVExistsAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_ab : CauchyPVExistsAt γ a b f z₀) (h_bc : CauchyPVExistsAt γ b c f z₀) :
    CauchyPVExistsAt γ a c f z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂⟩

end TauCeti.Contour

end
