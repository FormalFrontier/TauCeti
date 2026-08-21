/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Integrability
public import TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic
public import TauCeti.Analysis.PDE.EnergyForm.VariableLp
public import TauCeti.Analysis.Sobolev.Poincare.W1p0

/-!
# The divergence-form energy form on `H¹(Ω)`, and Gårding's inequality

Lane D, item 16 of `TauCetiRoadmap/PDE/README.md` asks for the weak energy form

`a(u, v) = ∫_Ω aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v`

of a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`, together with **Gårding's
inequality** `a(u, u) ≥ α‖u‖²_{H¹} - β‖u‖²_{L²}` and the lower bounds used to establish
coercivity on `H¹₀(Ω)` under suitable hypotheses. The pointwise and raw-jet halves of that
program are already in place: `TauCeti.PDE.energyIntegrand` is the
pointwise jet form and `TauCeti.PDE.energyFormIntegral` its integral against a measure, stated
for raw jet fields `X → ℝ × EuclideanSpace ℝ ι` because the Sobolev space was a separate
prerequisite. That prerequisite is now `TauCeti.W1p`, and this file joins the two.

## The energy form on Sobolev functions

`TauCeti.PDE.jetField u` is the raw value-gradient jet field `x ↦ (u x, ∇u x)` of a Sobolev
function, and `TauCeti.PDE.energyFormH1 a b c u v` integrates the pointwise energy density
against it. Both components of the jet are `L²` on `Ω`, so the energy density of two Sobolev
functions is integrable as soon as their pointwise bilinear form is essentially bounded
(`TauCeti.PDE.integrable_energyIntegrand_jetField`). The bounds-based wrapper
`TauCeti.PDE.UniformlyEllipticOn.integrable_energyIntegrand_jetField` constructs that hypothesis
from measurable bounded coefficients.

## Gårding, and what coercivity needs

The pointwise Gårding bound absorbs the drift by Young's inequality, paying for it out of half
of the ellipticity floor, and integrating it gives

`a(u, u) ≥ (λ/2)‖∇u‖²_{L²} - (β²/2λ)‖u‖²_{L²}`

for every `u ∈ H¹(Ω)`, with `λ` the lower ellipticity constant, `β` a bound for the drift and
`c ≥ 0` (`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self`). This is *not yet*
coercivity, and under the hypotheses assumed here the negative `L²` term cannot be dropped:
`c ≥ 0` allows `c = 0`, and then on a domain of finite measure a nonzero constant lies in
`H¹(Ω)` with zero gradient, so no lower bound by a positive multiple of `‖u‖²_{H¹}` holds. It
is the weakness of `c ≥ 0` that is responsible, not `H¹(Ω)` itself: a mass coefficient bounded
below by a constant `μ > β²/2λ` controls constants too, and the mass-floor bound
`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormIntegral_self_of_mass_lower_bound_on` then
has no negative term left to remove.

A **Poincaré inequality** `‖u‖_{L²} ≤ P‖∇u‖_{L²}` closes the gap, and
`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_slab` supplies one on `H¹₀(Ω)` for a
domain trapped in a slab. The resulting bound

`a(u, u) ≥ (λ² - β²P²)/(2λ(P² + 1)) · ‖u‖²_{H¹}`

holds outright (`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare`),
and it *is* coercivity once its constant is positive, for which
`TauCeti.PDE.energyFormH1_poincare_constant_pos`
supplies the sufficient smallness condition `βP < λ` relating the drift to the ellipticity and
the domain; with no drift there is no smallness condition at all. The
condition is what this estimate needs, not a proof that coercivity fails without it; when
coercivity is genuinely unavailable, the Fredholm alternative (Lane D, item 18) takes the place
of Lax--Milgram.

Boundedness is the other half of the pair the energy method needs, and it comes from the
pointwise operator-norm bound `Λ + β + γ` on the energy integrand together with Cauchy--Schwarz
(`TauCeti.PDE.UniformlyEllipticOn.norm_energyFormH1_le`). Bilinearity and that bound package the
form as a bundled continuous bilinear map on `H¹(Ω)`
(`TauCeti.PDE.energyFormH1L`), by restricting the existing
`TauCeti.PDE.energyFormLpVariable` along the Sobolev jet inclusion. Restricting further along the
closed-subspace inclusion gives `TauCeti.PDE.energyFormH1L0` on `H¹₀(Ω)`. These forms have the
shape required by Lax--Milgram; coercivity is a further step, and the route supplied here is the
Poincaré one: a Poincaré inequality on `H¹₀(Ω)` together with positivity of the resulting
constant, such as the sufficient condition `βP < λ`. That route is not the only one — the mass
floor `μ > β²/2λ` recorded above already gives a lower bound with no negative term, hence
coercivity on all of `H¹(Ω)` and no Poincaré inequality anywhere. Either way, this file supplies
the lower bounds and does not package an `IsCoercive` proof.

Everything is stated with explicit constants `λ, Λ, β, γ, P`, as the roadmap's standing
hypotheses require, and coefficient bounds are inline hypotheses `∀ x ∈ Ω, ‖b x‖ ≤ β` rather
than a bespoke predicate. No boundary regularity of `Ω` is used anywhere: the Poincaré
hypothesis is carried explicitly, and the interior estimates do not see the boundary.

## Main declarations

* `TauCeti.PDE.jetField`: the value-gradient jet field of a Sobolev function.
* `TauCeti.PDE.energyFormH1`: the divergence-form energy form on `H¹(Ω) = W^{1,2}(Ω)`.
* `TauCeti.PDE.energyFormH1L` and `TauCeti.PDE.energyFormH1L0`: the energy form bundled as a
  continuous bilinear map on `H¹(Ω)` and on `H¹₀(Ω)`, built from
  `TauCeti.PDE.energyFormLpVariable`.
* `TauCeti.PDE.UniformlyEllipticOn.integrable_energyIntegrand_jetField`: the energy density of
  two Sobolev functions is integrable.
* `TauCeti.PDE.UniformlyEllipticOn.norm_energyFormH1_le`: boundedness of the energy form, with
  explicit constant `Λ + β + γ`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self`: Gårding's inequality on `H¹(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_norm`: the equivalent roadmap form
  with an `H¹` norm and a negative `L²` term.
* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare`: the lower bound
  by `‖u‖²_{H¹}` obtained from a Poincaré inequality, and
  `TauCeti.PDE.energyFormH1_poincare_constant_pos`,
  the smallness condition `βP < λ` under which it is coercivity.
* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift`: the
  lower bound `λ‖∇u‖²_{L²} ≤ a(u, u)` when the drift vanishes, and
  `TauCeti.PDE.UniformlyEllipticOn.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift`: the
  corresponding `H¹`-norm lower bound for any function satisfying a Poincaré inequality.
* `TauCeti.PDE.norm_energyFormH1L_le_of_bounds`: the bundled form's operator-norm bound, stated
  from upper coefficient bounds without requiring lower ellipticity.
* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_slab` and
  `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball`: lower bounds on
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

/-! ### The jet field of a Sobolev function -/

section JetField

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The **value-gradient jet field** `x ↦ (u x, ∇u x)` of a first-order Sobolev function.

This is the raw jet field that `TauCeti.PDE.energyFormIntegral` expects; the two components
are the `Lᵖ` classes `TauCeti.W1p.value` and `TauCeti.W1p.gradient`, so the jet field is only
determined almost everywhere on `Ω`, which is all an integrated energy form sees.

Its application theorem exposes the componentwise fact needed downstream. -/
def jetField (u : W1p mu Omega p) : E → ℝ × E :=
  fun x => (W1p.value u x, W1p.gradient u x)

omit [FiniteDimensional ℝ E] in
/-- The value-gradient jet field evaluated at a point. -/
@[simp]
theorem jetField_apply (u : W1p mu Omega p) (x : E) :
    jetField u x = (W1p.value u x, W1p.gradient u x) :=
  by
    unfold jetField
    rfl

omit [FiniteDimensional ℝ E] in
private theorem jetField_zero_ae :
    jetField (0 : W1p mu Omega p) =ᵐ[mu.restrict Omega] 0 := by
  have hval : W1p.value (0 : W1p mu Omega p) = 0 := by
    rw [← W1p.valueL_apply]
    exact map_zero (W1p.valueL (mu := mu) (Omega := Omega) (p := p))
  have hgrad : W1p.gradient (0 : W1p mu Omega p) = 0 := by
    rw [← W1p.gradientL_apply]
    exact map_zero (W1p.gradientL (mu := mu) (Omega := Omega) (p := p))
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := p) (μ := mu.restrict Omega),
    Lp.coeFn_zero (E := E) (p := p) (μ := mu.restrict Omega)] with x hx hy
  rw [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

omit [FiniteDimensional ℝ E] in
private theorem jetField_add_ae (u v : W1p mu Omega p) :
    jetField (u + v) =ᵐ[mu.restrict Omega] fun x => jetField u x + jetField v x := by
  have hval : W1p.value (u + v) = W1p.value u + W1p.value v := by
    simp only [← W1p.valueL_apply, map_add]
  have hgrad : W1p.gradient (u + v) = W1p.gradient u + W1p.gradient v := by
    simp only [← W1p.gradientL_apply, map_add]
  filter_upwards [Lp.coeFn_add (W1p.value u) (W1p.value v),
    Lp.coeFn_add (W1p.gradient u) (W1p.gradient v)] with x hx hy
  simp only [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

omit [FiniteDimensional ℝ E] in
private theorem jetField_smul_ae (r : ℝ) (u : W1p mu Omega p) :
    jetField (r • u) =ᵐ[mu.restrict Omega] fun x => r • jetField u x := by
  have hval : W1p.value (r • u) = r • W1p.value u := by
    simp only [← W1p.valueL_apply, map_smul]
  have hgrad : W1p.gradient (r • u) = r • W1p.gradient u := by
    simp only [← W1p.gradientL_apply, map_smul]
  filter_upwards [Lp.coeFn_smul r (W1p.value u), Lp.coeFn_smul r (W1p.gradient u)] with x hx hy
  simp only [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

omit [FiniteDimensional ℝ E] in
/-- The jet field of a Sobolev function belongs to `Lᵖ(Ω)`: both of its components do, by the
construction of `W^{1,p}(Ω)`. -/
theorem memLp_jetField (u : W1p mu Omega p) : MemLp (jetField u) p (mu.restrict Omega) :=
  MemLp.of_fst_snd ⟨Lp.memLp (W1p.value u), Lp.memLp (W1p.gradient u)⟩

end JetField

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma P : ℝ}

omit [Fintype ι] [mu.IsAddHaarMeasure] in
private theorem ae_mem_restrict {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [OpensMeasurableSpace alpha] {mu : Measure alpha} {Omega : Opens alpha} :
    ∀ᵐ x ∂mu.restrict (Omega : Set alpha), x ∈ (Omega : Set alpha) :=
  ae_restrict_mem Omega.isOpen.measurableSet

/-- The continuous linear inclusion that forgets the `W^{1,2}` weak-derivative constraint and
views a Sobolev function as its square-integrable value-gradient jet. -/
def jetLpL : W1p mu Omega 2 →L[ℝ]
    Lp (ℝ × EuclideanSpace ℝ ι) 2 (mu.restrict Omega) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ ι)).toContinuousLinearMap.compLpL
      2 (mu.restrict Omega)).comp
    (w1pSubmodule mu Omega 2).toSubmodule.subtypeL

/-- The `L²` jet inclusion agrees almost everywhere with `jetField`. -/
theorem jetLpL_apply_ae (u : W1p mu Omega 2) :
    jetLpL u =ᵐ[mu.restrict Omega] jetField u := by
  filter_upwards [
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
      (EuclideanSpace ℝ ι)).toContinuousLinearMap.coeFn_compLpL (u : Sobolev1JetLp mu Omega 2),
    W1p.value_apply_ae u, W1p.gradient_apply_ae u] with x hjet hvalue hgradient
  rw [jetField_apply]
  -- `jetLpL` is the ambient jet inclusion followed by the `Lᵖ` action of the product
  -- identification; name that equation so the pointwise `compLpL` lemma applies.
  have hcomp : jetLpL u =
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
        (EuclideanSpace ℝ ι)).toContinuousLinearMap.compLpL 2 (mu.restrict Omega))
        (u : Sobolev1JetLp mu Omega 2) := (rfl)
  rw [hcomp, hjet]
  simpa only [WithLp.prodContinuousLinearEquiv_apply] using
    Prod.ext hvalue.symm hgradient.symm

/-- The squared gradient component of the Sobolev jet field is integrable. -/
theorem integrable_norm_jetField_snd_sq (u : W1p mu Omega 2) :
    Integrable (fun x => ‖(jetField u x).2‖ ^ 2) (mu.restrict Omega) := by
  simpa only [jetField_apply] using W1p.integrable_norm_gradient_sq u

/-- The squared value component of the Sobolev jet field is integrable. -/
theorem integrable_jetField_fst_sq (u : W1p mu Omega 2) :
    Integrable (fun x => (jetField u x).1 ^ 2) (mu.restrict Omega) := by
  simpa only [jetField_apply] using W1p.integrable_value_sq u

/-- The integral of the squared gradient component of a Sobolev jet is the squared `L²`
gradient norm. -/
theorem integral_norm_jetField_snd_sq_eq_norm_gradient_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖(jetField u x).2‖ ^ 2 ∂mu = ‖W1p.gradient u‖ ^ 2 := by
  simpa only [jetField_apply] using W1p.integral_norm_gradient_sq_eq_norm_gradient_sq u

/-- The integral of the squared value component of a Sobolev jet is the squared `L²` value
norm. -/
theorem integral_jetField_fst_sq_eq_norm_value_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, (jetField u x).1 ^ 2 ∂mu = ‖W1p.value u‖ ^ 2 := by
  simpa only [jetField_apply] using W1p.integral_value_sq_eq_norm_value_sq u

/-- The `L²` norm of the jet field of a Sobolev function is at most its `W^{1,2}` norm: the jet
fibre `ℝ × EuclideanSpace ℝ ι` of the energy integrand carries the product sup norm, which is
dominated by the Hilbert graph norm of `W^{1,2}(Ω)`. -/
theorem integral_norm_jetField_sq_le (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu ≤ ‖u‖ ^ 2 := by
  have hgrad := integrable_norm_jetField_snd_sq u
  have hval := integrable_jetField_fst_sq u
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
        rw [integral_add hval hgrad, integral_jetField_fst_sq_eq_norm_value_sq,
          integral_norm_jetField_snd_sq_eq_norm_gradient_sq]
    _ = ‖u‖ ^ 2 := (W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u).symm

/-- **Cauchy--Schwarz for jet fields.** The integral of the product of the jet norms of two
Sobolev functions is at most the product of their `W^{1,2}` norms. This is the estimate that
turns the pointwise operator-norm bound on the energy integrand into boundedness of the energy
form. -/
theorem integral_norm_jetField_mul_le (u v : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu ≤ ‖u‖ * ‖v‖ := by
  have hholder : ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu
      ≤ √(∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu) *
        √(∫ x in Omega, ‖jetField v x‖ ^ 2 ∂mu) := by
    have hu : MemLp (jetField u) (ENNReal.ofReal (2 : ℝ)) (mu.restrict Omega) := by
      simpa using memLp_jetField u
    have hv : MemLp (jetField v) (ENNReal.ofReal (2 : ℝ)) (mu.restrict Omega) := by
      simpa using memLp_jetField v
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using
      (integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        hu hv)
  refine hholder.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg u))
  · exact Real.sqrt_le_iff.mpr ⟨norm_nonneg u, integral_norm_jetField_sq_le u⟩
  · exact Real.sqrt_le_iff.mpr ⟨norm_nonneg v, integral_norm_jetField_sq_le v⟩

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

/-- The Sobolev energy form vanishes at zero in its left argument. -/
@[simp]
theorem energyFormH1_zero_left (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (v : W1p mu Omega 2) : energyFormH1 a b c 0 v = 0 := by
  calc
    energyFormH1 a b c 0 v =
        energyFormIntegral (mu.restrict Omega) a b c 0 (jetField v) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField 0) (jetField v)
        .rfl .rfl .rfl jetField_zero_ae .rfl
    _ = 0 := energyFormIntegral_zero_left _ _ _ _ _

/-- The Sobolev energy form vanishes at zero in its right argument. -/
@[simp]
theorem energyFormH1_zero_right (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u : W1p mu Omega 2) : energyFormH1 a b c u 0 = 0 := by
  calc
    energyFormH1 a b c u 0 =
        energyFormIntegral (mu.restrict Omega) a b c (jetField u) 0 :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField u) (jetField 0)
        .rfl .rfl .rfl .rfl jetField_zero_ae
    _ = 0 := energyFormIntegral_zero_right _ _ _ _ _

/-- Homogeneity of the Sobolev energy form in its left argument. -/
@[simp]
theorem energyFormH1_smul_left (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (r : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b c (r • u) v = r * energyFormH1 a b c u v := by
  calc
    energyFormH1 a b c (r • u) v =
        energyFormIntegral (mu.restrict Omega) a b c (fun x => r • jetField u x) (jetField v) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField (r • u)) (jetField v)
        .rfl .rfl .rfl (jetField_smul_ae r u) .rfl
    _ = r * energyFormH1 a b c u v := energyFormIntegral_smul_left _ _ _ _ _ _ r

/-- Homogeneity of the Sobolev energy form in its right argument. -/
@[simp]
theorem energyFormH1_smul_right (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (r : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b c u (r • v) = r * energyFormH1 a b c u v := by
  calc
    energyFormH1 a b c u (r • v) =
        energyFormIntegral (mu.restrict Omega) a b c (jetField u) (fun x => r • jetField v x) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField u) (jetField (r • v))
        .rfl .rfl .rfl .rfl (jetField_smul_ae r v)
    _ = r * energyFormH1 a b c u v := energyFormIntegral_smul_right _ _ _ _ _ _ r

/-- The coefficient in
`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare` is positive under the
smallness condition `βP < λ` relating the drift bound, the Poincaré constant and the ellipticity;
that is the sufficient condition under which the estimate is coercivity. -/
theorem energyFormH1_poincare_constant_pos (hlam : 0 < lam) (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hsmall : beta * P < lam) :
    0 < (lam ^ 2 - beta ^ 2 * P ^ 2) / (2 * lam * (P ^ 2 + 1)) := by
  have hD : 0 < 2 * lam * (P ^ 2 + 1) := by positivity
  refine div_pos ?_ hD
  nlinarith [mul_nonneg hbeta hP]

/-- Convert a gradient-minus-value lower bound into a full `H¹`-norm lower bound using a
Poincaré inequality. -/
private theorem mul_norm_sq_le_of_gradient_sub_value_bound {A B q : ℝ}
    {u : W1p mu Omega 2} (hAB : 0 ≤ A + B)
    (hlower : A * ‖W1p.gradient u‖ ^ 2 - B * ‖W1p.value u‖ ^ 2 ≤ q)
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (A - B * P ^ 2) / (P ^ 2 + 1) * ‖u‖ ^ 2 ≤ q := by
  have hP : 0 < P ^ 2 + 1 := by positivity
  have hnorm := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  have hsq : ‖W1p.value u‖ ^ 2 ≤ P ^ 2 * ‖W1p.gradient u‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg (W1p.value u)) hu
    nlinarith [this]
  refine le_trans ?_ hlower
  rw [div_mul_eq_mul_div, div_le_iff₀ hP, hnorm]
  nlinarith [mul_nonneg hAB (sub_nonneg.2 hsq)]

variable [DecidableEq ι]

/-- Shortcut seminormed group instance on `W^{1,2}(Ω)` to aid instance search for continuous
bilinear forms. -/
noncomputable local instance instSeminormedAddCommGroupW1p :
    SeminormedAddCommGroup (W1p mu Omega 2) := inferInstance

/-- Shortcut normed space instance on `W^{1,2}(Ω)` to aid instance search for continuous
bilinear forms. -/
noncomputable local instance instNormedSpaceW1p :
    NormedSpace ℝ (W1p mu Omega 2) := inferInstance

/-- Shortcut seminormed group instance on `W^{1,2}_0(Ω)` to aid instance search for continuous
bilinear forms. -/
noncomputable local instance instSeminormedAddCommGroupW1p0 :
    SeminormedAddCommGroup (W1p0 mu Omega 2) := inferInstance

/-- Shortcut normed space instance on `W^{1,2}_0(Ω)` to aid instance search for continuous
bilinear forms. -/
noncomputable local instance instNormedSpaceW1p0 :
    NormedSpace ℝ (W1p0 mu Omega 2) := inferInstance

omit [mu.IsAddHaarMeasure] [DecidableEq ι] in
/-- Bounded measurable coefficients define an essentially bounded field of pointwise energy
forms. Only the displayed upper bound on the principal part is needed; ellipticity is not. -/
theorem memLp_energyIntegrand_of_bounds
    (hLam : 0 ≤ Lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) :
    MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) := by
  refine memLp_top_of_bound (f := fun x => energyIntegrand (a x) (b x) (c x))
    (aestronglyMeasurable_energyIntegrand ha hb hc) (Lam + beta + gamma) ?_
  exact (ae_mem_restrict (mu := mu) (Omega := Omega)).mono fun x hx =>
    opNorm_energyIntegrand_le_of_bounds hLam (ha_bound x hx) (hb_bound x hx) (hc_bound x hx)

omit [DecidableEq ι] in
/-- The energy density of two Sobolev functions is integrable whenever its pointwise bilinear
coefficient field is essentially bounded. -/
theorem integrable_energyIntegrand_jetField
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x))
      (mu.restrict Omega) := by
  refine (integrable_bilinear_apply_of_memLp hcoeff (jetLpL u) (jetLpL v)).congr ?_
  filter_upwards [jetLpL_apply_ae u, jetLpL_apply_ae v] with x hu hv
  rw [hu, hv]

/-- The energy form on `H¹(Ω)` as a continuous bilinear form, obtained by restricting the
existing variable-coefficient `L²` energy form along the continuous Sobolev jet inclusion. -/
def energyFormH1L
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    W1p mu Omega 2 →L[ℝ] W1p mu Omega 2 →L[ℝ] ℝ :=
  (energyFormLpVariable (mu.restrict Omega) a b c hcoeff).bilinearComp jetLpL jetLpL

omit [DecidableEq ι] in
/-- The bundled Sobolev energy form evaluates to `energyFormH1`. -/
@[simp]
theorem energyFormH1L_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    energyFormH1L hcoeff u v = energyFormH1 a b c u v := by
  rw [energyFormH1L, ContinuousLinearMap.bilinearComp_apply, energyFormLpVariable_apply,
    energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [jetLpL_apply_ae u, jetLpL_apply_ae v] with x hu hv
  rw [hu, hv]

omit [DecidableEq ι] in
/-- Additivity of the Sobolev energy form in its left argument. -/
theorem energyFormH1_add_left
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v w : W1p mu Omega 2) :
    energyFormH1 a b c (u + w) v = energyFormH1 a b c u v + energyFormH1 a b c w v := by
  rw [← energyFormH1L_apply hcoeff]
  simp only [map_add, add_apply, energyFormH1L_apply]

omit [DecidableEq ι] in
/-- Additivity of the Sobolev energy form in its right argument. -/
theorem energyFormH1_add_right
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v w : W1p mu Omega 2) :
    energyFormH1 a b c u (v + w) = energyFormH1 a b c u v + energyFormH1 a b c u w := by
  rw [← energyFormH1L_apply hcoeff, map_add]
  simp only [energyFormH1L_apply]

omit [DecidableEq ι] in
/-- Boundedness of the Sobolev energy form from upper bounds alone. No lower ellipticity
hypothesis is needed. -/
theorem norm_energyFormH1_le_of_bounds
    (hLam : 0 ≤ Lam)
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    ‖energyFormH1 a b c u v‖ ≤ (Lam + beta + gamma) * (‖u‖ * ‖v‖) := by
  have hmem := ae_mem_restrict (mu := mu) (Omega := Omega)
  have hconst : 0 ≤ Lam + beta + gamma := by linarith
  have hmul : Integrable (fun x => ‖jetField u x‖ * ‖jetField v x‖) (mu.restrict Omega) :=
    (memLp_jetField u).norm.integrable_mul (memLp_jetField v).norm
  have key := norm_energyFormIntegral_le_of_bounds (μ := mu.restrict Omega)
    (a := a) (b := b) (c := c) (U := jetField u) (V := jetField v)
    hLam (hmem.mono fun x hx => ha_bound x hx) (hmem.mono hb_bound) (hmem.mono hc_bound)
      (hmul.const_mul (Lam + beta + gamma))
  refine key.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_norm_jetField_mul_le u v) hconst

omit [DecidableEq ι] in
/-- The operator norm of the bundled Sobolev energy form is controlled by the coefficient
upper bounds. -/
theorem norm_energyFormH1L_le_of_bounds
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hLam : 0 ≤ Lam)
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) :
    ‖energyFormH1L hcoeff‖ ≤ Lam + beta + gamma := by
  refine (energyFormH1L hcoeff).opNorm_le_bound₂ (by linarith) ?_
  intro u v
  rw [energyFormH1L_apply, mul_assoc]
  exact norm_energyFormH1_le_of_bounds hLam ha_bound hbeta hgamma hb_bound hc_bound u v

/-- The energy form on `H¹₀(Ω)` as a continuous bilinear form, obtained by restricting
`energyFormH1L` along the closed-subspace inclusion. -/
def energyFormH1L0
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2 →L[ℝ] ℝ :=
  (energyFormH1L hcoeff).bilinearComp
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL

omit [DecidableEq ι] in
/-- The bundled `H¹₀` energy form evaluates to `energyFormH1` on the underlying Sobolev
functions. -/
@[simp]
theorem energyFormH1L0_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p0 mu Omega 2) :
    energyFormH1L0 hcoeff u v =
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  rw [energyFormH1L0, ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply]
  simp only [Submodule.subtypeL_apply]

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
  PDE.integrable_energyIntegrand_jetField
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound) u v

/-- **Boundedness of the energy form on `H¹(Ω)`.** For a uniformly elliptic principal
coefficient with upper constant `Λ`, a drift bounded by `β` and a mass coefficient bounded by
`γ`,

`|a(u, v)| ≤ (Λ + β + γ) ‖u‖_{H¹} ‖v‖_{H¹}`.

The constant is the sum of the three coefficient bounds, an explicit pointwise operator-norm
bound for the energy integrand; the passage from the pointwise bound to the integrated one is
Cauchy--Schwarz. Together with `garding_energyFormH1_self` this is the pair of estimates the
energy method needs. -/
theorem norm_energyFormH1_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    ‖energyFormH1 a b c u v‖ ≤ (Lam + beta + gamma) * (‖u‖ * ‖v‖) :=
  norm_energyFormH1_le_of_bounds h.upper_nonneg (fun _x hx eta xi => h.upper_bound hx eta xi)
    hbeta hgamma
    hb_bound hc_bound u v

/-- **Gårding's inequality on `H¹(Ω)`.** For a uniformly elliptic principal coefficient with
lower constant `λ`, a drift bounded by `β` and a nonnegative mass coefficient,

`(λ/2)‖∇u‖²_{L²} - (β²/2λ)‖u‖²_{L²} ≤ a(u, u)`

for every `u ∈ H¹(Ω)`. The drift is absorbed by Young's inequality at the cost of half of the
ellipticity floor, which is where the negative `L²` term comes from. Under the stated general
assumption `c ≥ 0`, either a Poincaré inequality or a sufficiently positive mass lower bound is
needed to eliminate that term. -/
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
    integral_norm_jetField_snd_sq_eq_norm_gradient_sq,
    integral_jetField_fst_sq_eq_norm_value_sq]

/-- **Gårding's inequality in the roadmap's `H¹`-norm form.** This is the equivalent
restatement

`(λ/2)‖u‖²_{H¹} - (λ/2 + β²/2λ)‖u‖²_{L²} ≤ a(u,u)`.
-/
theorem garding_energyFormH1_self_norm
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam / 2 * ‖u‖ ^ 2 - (lam / 2 + beta ^ 2 / (2 * lam)) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  convert garding_energyFormH1_self h ha hb hc hb_bound hc_bound hc_nonneg u using 1
  ring

/-- **An energy-form lower bound from a Poincaré inequality.** If `u ∈ H¹(Ω)` satisfies
`‖u‖_{L²} ≤ P‖∇u‖_{L²}` then

`(λ² - β²P²)/(2λ(P² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

The estimate holds for every `P` for which the Poincaré bound is available; it *is* coercivity
once its constant is positive, for which `TauCeti.PDE.energyFormH1_poincare_constant_pos` supplies
the
sufficient smallness condition `βP < λ` relating the drift to the ellipticity and the domain.
The Poincaré hypothesis is carried on the single vector `u`, so a caller may supply it from
membership in `W^{1,2}_0(Ω)`, as the slab and ball corollaries below do, or from any other
source. -/
theorem mul_norm_sq_le_energyFormH1_self_of_poincare
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
  have hAB : 0 ≤ lam / 2 + beta ^ 2 / (2 * lam) := by positivity
  have key := mul_norm_sq_le_of_gradient_sub_value_bound (P := P) hAB
    (garding_energyFormH1_self h ha hb hc hb_bound hc_bound hc_nonneg u) hu
  convert key using 1
  field_simp

/-- **The drift-free energy dominates the Dirichlet energy.** When the drift vanishes on `Ω`
and the mass coefficient is nonnegative, uniform ellipticity integrates to

`λ‖∇u‖²_{L²} ≤ a(u, u)`

for every `u ∈ H¹(Ω)`. With no drift there is nothing for Young's inequality to absorb, so this
keeps the full ellipticity constant where `garding_energyFormH1_self` is left with `λ/2`. -/
theorem mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam * ‖W1p.gradient u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hmem := ae_mem_restrict (mu := mu) (Omega := Omega)
  have hb_zero_ae : b =ᵐ[mu.restrict Omega] fun _ => 0 := hmem.mono hb_zero
  have henergy_zero := integrable_energyIntegrand_jetField (b := fun _ => 0) (beta := 0)
    h ha aestronglyMeasurable_const hc (by simp) hc_bound u u
  have key := integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
    (μ := mu.restrict Omega) (a := a) (c := c) (U := jetField u)
    (hmem.mono fun x hx xi => by
      simpa [toQuadraticForm'_eq_dotProduct] using h.lower_bound hx xi)
    (hmem.mono hc_nonneg) ((integrable_norm_jetField_snd_sq u).const_mul lam) henergy_zero
  rw [← integral_norm_jetField_snd_sq_eq_norm_gradient_sq u, ← integral_const_mul,
    energyFormH1_def]
  exact key.trans_eq ((energyFormIntegral_congr_ae (μ := mu.restrict Omega)
    (a := a) (b := fun _ => 0) (c := c) (U := jetField u) (V := jetField u)
    Filter.EventuallyEq.rfl hb_zero_ae.symm Filter.EventuallyEq.rfl
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).trans
        (energyFormIntegral_def _ _ _ _ _ _))

/-- **An `H¹`-norm lower bound with no drift.** When the drift vanishes on `Ω` there is no
condition: a Poincaré inequality alone gives

`λ/(P² + 1) · ‖u‖²_{H¹} ≤ a(u, u)`.

This is the case of a divergence-form operator `-∂ⱼ(aⁱʲ ∂ᵢu) + c u`. The constant is the one
the ellipticity floor gives directly, without the factor `2` that Young's inequality costs when
a drift has to be absorbed. -/
theorem div_mul_norm_sq_le_energyFormH1_self_of_zero_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    lam / (P ^ 2 + 1) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have key := mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift h ha hc hb_zero
    hc_bound hc_nonneg u
  simpa using mul_norm_sq_le_of_gradient_sub_value_bound (P := P) (by simpa using h.pos.le)
    (A := lam) (B := 0) (by simpa using key) hu

end UniformlyEllipticOn

end Domain

/-! ### Energy-form lower bounds on slab- or ball-contained domains -/

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **An energy-form lower bound on `H¹₀(Ω)` for a domain trapped in a slab.** If
`Ω ⊆ ℝ^{n+1}` lies between the hyperplanes `xᵢ = s` and `xᵢ = t`, then every
`u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - β²(t - s)²)/(2λ((t - s)² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`,

the Poincaré constant of the slab being its width `t - s`. The domain need not be bounded:
boundedness in one direction is enough, and no regularity of `∂Ω` is used, the homogeneous
boundary condition being carried by membership in `W^{1,2}_0(Ω)`. -/
theorem mul_norm_sq_le_energyFormH1_self_of_subset_slab
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
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_slab (ENNReal.ofNat_ne_top) hst hslab hu)

/-- **An energy-form lower bound on `H¹₀(Ω)` for a domain inside a ball.** For
`Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` every `u ∈ W^{1,2}_0(Ω)` satisfies

`(λ² - 4β²R²)/(2λ(4R² + 1)) · ‖u‖²_{H¹} ≤ a(u, u)`.

The Poincaré constant `2R` is the diameter bound, not the sharp one, but it is explicit and
independent of the centre. Together with positivity of the displayed constant, this is the
diagonal estimate used to prove coercivity for a Lax--Milgram application. -/
theorem mul_norm_sq_le_energyFormH1_self_of_subset_ball
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
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball (ENNReal.ofNat_ne_top) hball hu)

end UniformlyEllipticOn

end Euclidean

end PDE

end TauCeti
