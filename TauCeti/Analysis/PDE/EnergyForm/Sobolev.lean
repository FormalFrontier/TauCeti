/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Integrability
public import TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic
public import TauCeti.Analysis.Sobolev.Poincare.W1p0

/-!
# The divergence-form energy form on `H¹(Ω)`, and Gårding's inequality

Lane D, item 16 of `TauCetiRoadmap/PDE/README.md` asks for the weak energy form

`a(u, v) = ∫_Ω aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v`

of a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`, together with **Gårding's
inequality** `a(u, u) ≥ α‖u‖²_{H¹} - β‖u‖²_{L²}` and, on `H¹₀(Ω)`, coercivity. The pointwise
and raw-jet halves of that program are already in place: `TauCeti.PDE.energyIntegrand` is the
pointwise jet form and `TauCeti.PDE.energyFormIntegral` its integral against a measure, stated
for raw jet fields `X → ℝ × EuclideanSpace ℝ ι` because the Sobolev space was a separate
prerequisite. That prerequisite is now `TauCeti.W1p`, and this file joins the two.

## The energy form on Sobolev functions

`TauCeti.PDE.jetField u` is the raw value-gradient jet field `x ↦ (u x, ∇u x)` of a Sobolev
function, and `TauCeti.PDE.energyFormH1 a b c u v` integrates the pointwise energy density
against it. Both components of the jet are `L²` on `Ω`, so the energy density of two Sobolev
functions is integrable as soon as the coefficients are measurable and bounded
(`TauCeti.PDE.UniformlyEllipticOn.integrable_energyIntegrand_jetField`): no integrability side
condition has to be carried at a use site, unlike for raw jet fields.

## Gårding, and what coercivity needs

The pointwise Gårding bound absorbs the drift by Young's inequality, paying for it out of half
of the ellipticity floor, and integrating it gives

`a(u, u) ≥ (λ/2)‖∇u‖²_{L²} - (β²/2λ)‖u‖²_{L²}`

for every `u ∈ H¹(Ω)`, with `λ` the lower ellipticity constant, `β` a bound for the drift and
`c ≥ 0` (`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self`). This is *not yet*
coercivity: the negative `L²` term is genuinely there, and on `H¹(Ω)` it cannot be removed —
on a domain of finite measure a nonzero constant lies in `H¹(Ω)` and has zero gradient, so no
lower bound by a positive multiple of `‖u‖²_{H¹}` can hold there.

A **Poincaré inequality** `‖u‖_{L²} ≤ P‖∇u‖_{L²}` closes the gap, and
`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_slab` supplies one on `H¹₀(Ω)` for a
domain trapped in a slab. The resulting bound

`a(u, u) ≥ (λ² - β²P²)/(2λ(P² + 1)) · ‖u‖²_{H¹}`

holds outright (`TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_poincare`), and
it *is* coercivity exactly when its constant is positive, which by
`TauCeti.PDE.coercivity_constant_pos` is the smallness condition `βP < λ` relating the drift to
the ellipticity and the domain; with no drift there is no smallness condition at all. The
condition is what this estimate needs, not a proof that coercivity fails without it; when
coercivity is genuinely unavailable, the Fredholm alternative (Lane D, item 18) takes the place
of Lax--Milgram.

Boundedness is the other half of the pair the energy method needs, and it comes from the
pointwise operator-norm bound `Λ + β + γ` on the energy integrand together with Cauchy--Schwarz
(`TauCeti.PDE.UniformlyEllipticOn.norm_energyFormH1_le`).

Everything is stated with explicit constants `λ, Λ, β, γ, P`, as the roadmap's standing
hypotheses require, and coefficient bounds are inline hypotheses `∀ x ∈ Ω, ‖b x‖ ≤ β` rather
than a bespoke predicate. No boundary regularity of `Ω` is used anywhere: the Poincaré
hypothesis is carried explicitly, and the interior estimates do not see the boundary.

## Main declarations

* `TauCeti.PDE.jetField`: the value-gradient jet field of a Sobolev function.
* `TauCeti.PDE.energyFormH1`: the divergence-form energy form on `H¹(Ω) = W^{1,2}(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.integrable_energyIntegrand_jetField`: the energy density of
  two Sobolev functions is integrable.
* `TauCeti.PDE.UniformlyEllipticOn.norm_energyFormH1_le`: boundedness of the energy form, with
  explicit constant `Λ + β + γ`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self`: Gårding's inequality on `H¹(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_poincare`: the lower bound by
  `‖u‖²_{H¹}` obtained from a Poincaré inequality, and `TauCeti.PDE.coercivity_constant_pos`,
  the smallness condition `βP < λ` under which it is coercivity.
* `TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_zero_drift`: coercivity with
  no smallness condition when the drift vanishes.
* `TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_subset_slab` and
  `TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_subset_ball`: coercivity on
  `H¹₀(Ω)` for a domain trapped in a slab, or in a ball.

## References

Lane D, item 16 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential
Equations*, Section 6.2 (energy estimates and Gårding's inequality); D. Gilbarg and
N. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma P : ℝ}

/-! ### The jet field of a Sobolev function -/

/-- The **value-gradient jet field** `x ↦ (u x, ∇u x)` of a first-order Sobolev function.

This is the raw jet field that `TauCeti.PDE.energyFormIntegral` expects; the two components
are the `L²` classes `TauCeti.W1p.value` and `TauCeti.W1p.gradient`, so the jet field is only
determined almost everywhere on `Ω`, which is all an integrated energy form sees.

It is `@[expose]`d because its two components are exactly the value and the gradient, and
downstream statements read the jet componentwise. -/
@[expose]
def jetField (u : W1p mu Omega 2) : EuclideanSpace ℝ ι → ℝ × EuclideanSpace ℝ ι :=
  fun x => (W1p.value u x, W1p.gradient u x)

@[simp]
theorem jetField_apply (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) :
    jetField u x = (W1p.value u x, W1p.gradient u x) :=
  rfl

/-- The jet field of a Sobolev function is square integrable on `Ω`: both of its components
are, by construction of `W^{1,2}(Ω)`. -/
theorem memLp_jetField (u : W1p mu Omega 2) : MemLp (jetField u) 2 (mu.restrict Omega) :=
  MemLp.of_fst_snd ⟨Lp.memLp (W1p.value u), Lp.memLp (W1p.gradient u)⟩

/-- The `L²` norm of a square-integrable function is the integral of its squared pointwise
norm. -/
private theorem integral_norm_sq_eq_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : Lp F 2 m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = ‖f‖ ^ 2 := by
  refine Eq.symm ?_
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x))

/-- The gradient part of the energy of a Sobolev function is its squared `L²` gradient norm. -/
theorem integral_norm_jetField_snd_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖(jetField u x).2‖ ^ 2 ∂mu = ‖W1p.gradient u‖ ^ 2 :=
  integral_norm_sq_eq_norm_sq (W1p.gradient u)

/-- The value part of the energy of a Sobolev function is its squared `L²` norm. -/
theorem integral_jetField_fst_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, (jetField u x).1 ^ 2 ∂mu = ‖W1p.value u‖ ^ 2 := by
  rw [← integral_norm_sq_eq_norm_sq (W1p.value u)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [Real.norm_eq_abs, sq_abs])

/-- The `L²` norm of the jet field of a Sobolev function is at most its `W^{1,2}` norm: the jet
fibre `ℝ × EuclideanSpace ℝ ι` of the energy integrand carries the product sup norm, which is
dominated by the Hilbert graph norm of `W^{1,2}(Ω)`. -/
theorem integral_norm_jetField_sq_le (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu ≤ ‖u‖ ^ 2 := by
  have hgrad : Integrable (fun x => ‖(jetField u x).2‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm ((memLp_jetField u).aestronglyMeasurable.snd)).1
      (memLp_jetField u).snd
  have hval : Integrable (fun x => (jetField u x).1 ^ 2) (mu.restrict Omega) :=
    (memLp_jetField u).fst.integrable_sq
  have hjet : Integrable (fun x => ‖jetField u x‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm (memLp_jetField u).aestronglyMeasurable).1
      (memLp_jetField u)
  have hpoint : ∀ x, ‖jetField u x‖ ^ 2
      ≤ (jetField u x).1 ^ 2 + ‖(jetField u x).2‖ ^ 2 := fun x => by
    rw [Prod.norm_def, ← sq_abs (jetField u x).1, ← Real.norm_eq_abs]
    rcases le_total ‖(jetField u x).1‖ ‖(jetField u x).2‖ with hle | hle
    · rw [max_eq_right hle]
      nlinarith [sq_nonneg ‖(jetField u x).1‖]
    · rw [max_eq_left hle]
      nlinarith [sq_nonneg ‖(jetField u x).2‖]
  calc ∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu
      ≤ ∫ x in Omega, ((jetField u x).1 ^ 2 + ‖(jetField u x).2‖ ^ 2) ∂mu :=
        integral_mono hjet (hval.add hgrad) hpoint
    _ = ‖W1p.value u‖ ^ 2 + ‖W1p.gradient u‖ ^ 2 := by
        rw [integral_add hval hgrad, integral_jetField_fst_sq, integral_norm_jetField_snd_sq]
    _ = ‖u‖ ^ 2 := (W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u).symm

/-- The jet norm of a Sobolev function, viewed in `L²(Ω)`, has norm at most the `W^{1,2}` norm
of the function. -/
private theorem norm_toLp_norm_jetField_le (u : W1p mu Omega 2) :
    ‖(memLp_jetField u).norm.toLp fun x => ‖jetField u x‖‖ ≤ ‖u‖ := by
  have hsq : ‖(memLp_jetField u).norm.toLp fun x => ‖jetField u x‖‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (integral_norm_jetField_sq_le u)
    rw [← integral_norm_sq_eq_norm_sq ((memLp_jetField u).norm.toLp _)]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_jetField u).norm.coeFn_toLp] with x hx
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  nlinarith [norm_nonneg ((memLp_jetField u).norm.toLp fun x => ‖jetField u x‖), norm_nonneg u]

/-- **Cauchy--Schwarz for jet fields.** The integral of the product of the jet norms of two
Sobolev functions is at most the product of their `W^{1,2}` norms. This is the estimate that
turns the pointwise operator-norm bound on the energy integrand into boundedness of the energy
form. -/
theorem integral_norm_jetField_mul_le (u v : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu ≤ ‖u‖ * ‖v‖ := by
  have hinner : ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu
      = inner ℝ ((memLp_jetField u).norm.toLp fun x => ‖jetField u x‖)
        ((memLp_jetField v).norm.toLp fun x => ‖jetField v x‖) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_jetField u).norm.coeFn_toLp,
      (memLp_jetField v).norm.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hinner]
  exact (real_inner_le_norm _ _).trans (mul_le_mul (norm_toLp_norm_jetField_le u)
    (norm_toLp_norm_jetField_le v) (norm_nonneg _) (norm_nonneg u))

/-! ### The energy form on `H¹(Ω)` -/

/-- The **divergence-form energy form on `H¹(Ω) = W^{1,2}(Ω)`**,

`a(u, v) = ∫_Ω aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v`,

obtained by integrating the pointwise jet form `TauCeti.PDE.energyIntegrand` against the jet
fields of two Sobolev functions. The coefficients stay separate, explicit data: no
boundedness, ellipticity or measurability is assumed here, and each estimate below names the
hypotheses it needs. -/
def energyFormH1 (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u v : W1p mu Omega 2) : ℝ :=
  energyFormIntegral (mu.restrict Omega) a b c (jetField u) (jetField v)

/-- The energy form on `H¹(Ω)` is the integral of the pointwise energy density over `Ω`. -/
theorem energyFormH1_def (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c u v =
      ∫ x in Omega, energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x) ∂mu :=
  energyFormIntegral_def _ _ _ _ _ _

/-- The coercivity constant of
`TauCeti.PDE.UniformlyEllipticOn.coercive_energyFormH1_self_of_poincare` is positive exactly
under the smallness condition `βP < λ` relating the drift bound, the Poincaré constant and the
ellipticity, so that estimate is coercivity precisely there. -/
theorem coercivity_constant_pos (hlam : 0 < lam) (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hsmall : beta * P < lam) :
    0 < (lam ^ 2 - beta ^ 2 * P ^ 2) / (2 * lam * (P ^ 2 + 1)) := by
  have hD : 0 < 2 * lam * (P ^ 2 + 1) := by positivity
  refine div_pos ?_ hD
  nlinarith [mul_nonneg hbeta hP]

variable [DecidableEq ι]

namespace UniformlyEllipticOn

/-- Uniform ellipticity does not depend on the decidable equality chosen for the coordinate
index: it is a subsingleton, so this transports the ambient hypothesis to the classical choice
fixed by the pointwise and integrated energy-form files. -/
private theorem withClassicalDecEq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) :
    @UniformlyEllipticOn (EuclideanSpace ℝ ι) ι _ (Classical.decEq ι)
      (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam := by
  rwa [Subsingleton.elim (Classical.decEq ι) ‹DecidableEq ι›]

/-- The energy density of two Sobolev functions is integrable on `Ω`, for uniformly elliptic
principal coefficients with bounded measurable lower-order terms. Both jets are `L²`, so the
product of their norms, which dominates the density, is integrable by Cauchy--Schwarz. -/
theorem integrable_energyIntegrand_jetField
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x))
      (mu.restrict Omega) :=
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) := ae_restrict_mem Omega.isOpen.measurableSet
  integrable_energyIntegrand_apply₂_of_memLp_two_on h.withClassicalDecEq hmem ha hb hc
    (memLp_jetField u) (memLp_jetField v) (hmem.mono hb_bound) (hmem.mono hc_bound)

/-- **Boundedness of the energy form on `H¹(Ω)`.** For a uniformly elliptic principal
coefficient with upper constant `Λ`, a drift bounded by `β` and a mass coefficient bounded by
`γ`,

`|a(u, v)| ≤ (Λ + β + γ) ‖u‖_{H¹} ‖v‖_{H¹}`.

The constant is the sum of the three coefficient bounds, exactly the pointwise operator norm of
the energy integrand; the passage from the pointwise bound to the integrated one is
Cauchy--Schwarz. Together with `garding_energyFormH1_self` this is the pair of estimates the
energy method needs. -/
theorem norm_energyFormH1_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    ‖energyFormH1 a b c u v‖ ≤ (Lam + beta + gamma) * (‖u‖ * ‖v‖) := by
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) := ae_restrict_mem Omega.isOpen.measurableSet
  have hconst : 0 ≤ Lam + beta + gamma := by
    have := h.upper_nonneg
    linarith
  have hmul : Integrable (fun x => ‖jetField u x‖ * ‖jetField v x‖) (mu.restrict Omega) :=
    (memLp_jetField u).norm.integrable_mul (memLp_jetField v).norm
  have key := norm_energyFormIntegral_le_on (μ := mu.restrict Omega) h.withClassicalDecEq hmem
    (hmem.mono hb_bound) (hmem.mono hc_bound) (hmul.const_mul (Lam + beta + gamma))
  refine key.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_norm_jetField_mul_le u v) hconst

/-- **Gårding's inequality on `H¹(Ω)`.** For a uniformly elliptic principal coefficient with
lower constant `λ`, a drift bounded by `β` and a nonnegative mass coefficient,

`(λ/2)‖∇u‖²_{L²} - (β²/2λ)‖u‖²_{L²} ≤ a(u, u)`

for every `u ∈ H¹(Ω)`. The drift is absorbed by Young's inequality at the cost of half of the
ellipticity floor, which is where the negative `L²` term comes from; it cannot be dropped on
`H¹(Ω)`, and removing it is exactly what a Poincaré inequality on `H¹₀(Ω)` does. -/
theorem garding_energyFormH1_self
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam / 2 * ‖W1p.gradient u‖ ^ 2 - beta ^ 2 / (2 * lam) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) := ae_restrict_mem Omega.isOpen.measurableSet
  have hgrad : Integrable (fun x => ‖(jetField u x).2‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm ((memLp_jetField u).aestronglyMeasurable.snd)).1
      (memLp_jetField u).snd
  have hval : Integrable (fun x => (jetField u x).1 ^ 2) (mu.restrict Omega) :=
    (memLp_jetField u).fst.integrable_sq
  have hlower : Integrable (fun x => lam / 2 * ‖(jetField u x).2‖ ^ 2
      - beta ^ 2 / (2 * lam) * (jetField u x).1 ^ 2) (mu.restrict Omega) :=
    (hgrad.const_mul _).sub (hval.const_mul _)
  have key := garding_energyFormIntegral_self_on (μ := mu.restrict Omega) h.withClassicalDecEq hmem
    (hmem.mono hb_bound)
    (hmem.mono hc_nonneg) hlower
    (integrable_energyIntegrand_jetField h ha hb hc hb_bound hc_bound u u)
  refine le_trans (le_of_eq ?_) key
  rw [integral_sub (hgrad.const_mul _) (hval.const_mul _), integral_const_mul, integral_const_mul,
    integral_norm_jetField_snd_sq, integral_jetField_fst_sq]

/-- **Coercivity of the energy form from a Poincaré inequality.** If `u ∈ H¹(Ω)` satisfies
`‖u‖_{L²} ≤ P‖∇u‖_{L²}` then

`(λ² - β²P²)/(2λ(P² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

The estimate holds for every `P` for which the Poincaré bound is available; it *is* coercivity
exactly when its constant is positive, which by
`TauCeti.PDE.UniformlyEllipticOn.coercivity_constant_pos` is the smallness condition `βP < λ`
relating the drift to the ellipticity and the domain. The Poincaré hypothesis is carried on the
single vector `u`, so a caller may supply it from membership in `W^{1,2}_0(Ω)`, as the slab and
ball corollaries below do, or from any other source. -/
theorem coercive_energyFormH1_self_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (lam ^ 2 - beta ^ 2 * P ^ 2) / (2 * lam * (P ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  have hlam : 0 < lam := h.pos
  have hD : 0 < 2 * lam * (P ^ 2 + 1) := by positivity
  have hnorm : ‖u‖ ^ 2 = ‖W1p.value u‖ ^ 2 + ‖W1p.gradient u‖ ^ 2 :=
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  have hsq : ‖W1p.value u‖ ^ 2 ≤ P ^ 2 * ‖W1p.gradient u‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg (W1p.value u)) hu
    nlinarith [this]
  refine le_trans ?_ (garding_energyFormH1_self h ha hb hc hb_bound hc_bound hc_nonneg u)
  rw [div_mul_eq_mul_div, div_le_iff₀ hD, hnorm]
  have hexpand : (lam / 2 * ‖W1p.gradient u‖ ^ 2 - beta ^ 2 / (2 * lam) * ‖W1p.value u‖ ^ 2)
      * (2 * lam * (P ^ 2 + 1))
      = (lam ^ 2 * ‖W1p.gradient u‖ ^ 2 - beta ^ 2 * ‖W1p.value u‖ ^ 2) * (P ^ 2 + 1) := by
    field_simp
  rw [hexpand]
  nlinarith [mul_nonneg (_root_.add_nonneg (sq_nonneg lam) (sq_nonneg beta))
    (sub_nonneg.2 hsq)]

/-- **Coercivity with no drift.** When the drift vanishes on `Ω` there is no smallness
condition: a Poincaré inequality alone gives

`λ/(2(P² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

This is the case of a symmetric divergence-form operator `-∂ⱼ(aⁱʲ ∂ᵢu) + c u`. -/
theorem coercive_energyFormH1_self_of_zero_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    lam / (2 * (P ^ 2 + 1)) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hlam : 0 < lam := h.pos
  have key := coercive_energyFormH1_self_of_poincare (beta := 0) (P := P) h ha hb hc
    (fun x hx => by simp [hb_zero x hx]) hc_bound hc_nonneg hu
  refine le_trans (le_of_eq ?_) key
  rw [show lam ^ 2 - 0 ^ 2 * P ^ 2 = lam * lam by ring, show 2 * lam * (P ^ 2 + 1)
    = lam * (2 * (P ^ 2 + 1)) by ring, mul_div_mul_left _ _ hlam.ne']

end UniformlyEllipticOn

end Domain

/-! ### Coercivity on `H¹₀(Ω)` for a bounded domain -/

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **Coercivity of the energy form on `H¹₀(Ω)` for a domain trapped in a slab.** If
`Ω ⊆ ℝ^{n+1}` lies between the hyperplanes `xᵢ = s` and `xᵢ = t`, then every
`u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - β²(t - s)²)/(2λ((t - s)² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`,

the Poincaré constant of the slab being its width `t - s`. The domain need not be bounded:
boundedness in one direction is enough, and no regularity of `∂Ω` is used, the homogeneous
boundary condition being carried by membership in `W^{1,2}_0(Ω)`. -/
theorem coercive_energyFormH1_self_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ} (hst : s ≤ t)
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (t - s) ^ 2) / (2 * lam * ((t - s) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  coercive_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_slab (ENNReal.ofNat_ne_top) hst hslab hu)

/-- **Coercivity of the energy form on `H¹₀(Ω)` for a domain inside a ball.** For
`Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` every `u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - 4β²R²)/(2λ(4R² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

The Poincaré constant `2R` is the diameter bound, not the sharp one, but it is explicit and
independent of the centre. This is the hypothesis that Lax--Milgram consumes for the Dirichlet
problem on a bounded domain, once the drift is small enough that the constant is positive. -/
theorem coercive_energyFormH1_self_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  coercive_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball (ENNReal.ofNat_ne_top) hball hu)

end UniformlyEllipticOn

end Euclidean

end PDE

end TauCeti
