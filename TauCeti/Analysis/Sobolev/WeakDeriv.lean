/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- This import is public: `TestFunction` supplies `𝓓(Ω, ℝ)`, `Opens`, `lineDeriv`,
-- `LocallyIntegrableOn` and the Bochner integral `∫ … ∂μ` appearing in every statement below.
public import Mathlib.Analysis.Distribution.TestFunction
-- The next two imports are private: integration by parts is used only to prove that a classical
-- derivative is a weak one, and the fundamental lemma of the calculus of variations only to prove
-- uniqueness, so downstream importers pay for neither.
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
-- This import is public: `Gradient` supplies the `∇` of the weak derivative of a test function
-- below, together with the Riesz correspondence `innerSL` in which that statement is phrased.
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Weak derivatives on an open set

Lane A of the PDE roadmap builds the Sobolev spaces `W^{k,p}(Ω)` of a domain out of *weak*
derivatives, rather than out of Mathlib's whole-space Bessel-potential scale. This file supplies
the underlying differentiation notion: for an open set `Ω` in a real normed space `E`, a measure
`μ` on `E`, functions `u, u' : E → F` and a direction `v : E`,

`TauCeti.HasWeakLineDerivOn μ Ω u u' v`

says that the codomain `F` is complete, that `u` and `u'` are locally integrable on `Ω`, and that

`∫ (∂_v φ) • u ∂μ = - ∫ φ • u' ∂μ`

for every test function `φ ∈ 𝓓(Ω, ℝ)`; for the intended `μ`, an additive Haar measure, this says
that `u'` represents the distributional derivative `∂_v u` on `Ω` (see *The measure* below). The
bundled test-function type `TestFunction` of `Mathlib/Analysis/Distribution/TestFunction.lean` is
the class of admissible `φ`, so the test objects are exactly the distributional ones;
`TauCeti.hasWeakLineDerivOn_iff` restates the identity in terms of unbundled smooth compactly
supported functions when that is more convenient.

Assembling the directions gives `TauCeti.HasWeakFDerivOn μ Ω u U` for a candidate weak derivative
`U : E → E →L[ℝ] F`, the object whose `Lᵖ` integrability cuts out `W^{1,p}(Ω)`.

Two facts make the notion usable, and both are proved here.

* **Uniqueness.** Two weak derivatives of the same function in the same direction agree almost
  everywhere on `Ω` (`TauCeti.HasWeakLineDerivOn.ae_eq` and `TauCeti.HasWeakFDerivOn.ae_eq`). This
  is the fundamental lemma of the calculus of variations, consumed from Mathlib in the form
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
* **Consistency.** For a Haar measure `μ`, a classical derivative that is locally integrable on
  `Ω` is a weak derivative (`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`,
  `TauCeti.hasWeakFDerivOn_of_differentiableOn`), by integration by parts. Differentiability alone
  is not enough: local integrability of `u` and of its derivative is part of what it means to have
  a weak derivative, so both are hypotheses of these theorems and of the comparison theorems
  `TauCeti.HasWeakLineDerivOn.ae_eq_lineDeriv` and `TauCeti.HasWeakFDerivOn.ae_eq_fderiv`.
  Together with uniqueness this pins the notion down: on a `C¹` function whose derivative is
  locally integrable on `Ω`, the weak derivative is the classical one almost everywhere.

Nothing here assumes that `Ω` is bounded or that its boundary is regular: the weak derivative is a
purely interior notion, and boundary hypotheses enter only with traces and extensions.

## Local integrability

`LocallyIntegrableOn u Ω μ` and `LocallyIntegrableOn u' Ω μ` are part of the definition rather
than side hypotheses on the theorems. That is the textbook statement — a weak derivative is a
relation between two members of `L¹_loc(Ω)` — and in Lean it is also what makes the predicate say
what it claims: `MeasureTheory.integral` is `0` on a function that is not integrable, so the bare
integration-by-parts identity is satisfied spuriously by junk-valued pairs, for instance by any
`u` with a non-integrable singularity inside `Ω` together with `u' = 0`. Mathlib guards the same
corner in `TestFunction.integralAgainstBilinCLM`, which pairs against a function only when it is
locally integrable on `Ω` and is the zero map otherwise.

The components are projected out by `TauCeti.HasWeakLineDerivOn.completeSpace`,
`TauCeti.HasWeakLineDerivOn.locallyIntegrableOn`,
`TauCeti.HasWeakLineDerivOn.locallyIntegrableOn_deriv` and
`TauCeti.HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul`, so a proof never has to
unfold the definition.

## The codomain

`CompleteSpace F` is a component of the definition, for the same reason local integrability is.
`MeasureTheory.integral` is *defined* to be `0` on an incomplete codomain, so for an incomplete
`F` the identity above would read `0 = -0` and the predicate would degenerate into local
integrability of `u` and `u'`, making every locally integrable function a weak derivative of every
other. Carrying completeness makes the predicate say what its name claims for every `F`, and
`TauCeti.HasWeakLineDerivOn.completeSpace` recovers the instance — usually as
`have := h.completeSpace` — so the results that consume it, such as the fundamental lemma of the
calculus of variations behind `TauCeti.HasWeakLineDerivOn.ae_eq`, get it from the hypothesis.

## The measure

The defining identity is *not* the distributional derivative for an arbitrary `μ`, and is not
advertised as one. Integrating against `μ` produces the adjoint of `∂_v` relative to `μ`: for a
weighted `μ = volume.withDensity w`, the identity reads `∂_v (w • u) = w • u'` in the sense of
distributions, a condition on `u` and `u'` in which the weight cannot be cancelled: it constrains
`w • u'`, not `u'`, so a constant `u` need not have weak derivative `0`. Exactly when `μ` is
translation invariant — an additive Haar measure, hence a positive multiple of Lebesgue measure
on a finite-dimensional `E` — does the identity say that `u'` represents `∂_v u` as a
distribution on `Ω`, and that is the `μ` out of which `W^{k,p}(Ω)` will be built.

Accordingly `[μ.IsAddHaarMeasure]` is a hypothesis of every result below that ties the notion to
the classical derivative: `TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`,
`TauCeti.hasWeakLineDerivOn_const`, `TauCeti.hasWeakFDerivOn_of_differentiableOn`,
`TauCeti.HasWeakLineDerivOn.ae_eq_lineDeriv` and `TauCeti.HasWeakFDerivOn.ae_eq_fderiv`. It is
carried by those results rather than built into the definition, following Mathlib's own treatment
of `MeasureTheory.convolution`, whose definition takes a bare `μ` and whose group-invariance
hypotheses sit on the lemmas that need them: locality, linearity and almost-everywhere uniqueness
are true of the adjoint relation for every `μ`, and stating them for a Haar measure only would
weaken them for no gain.

## Main declarations

* `TauCeti.HasWeakLineDerivOn`: `u'` is a weak derivative of `u` in the direction `v` on `Ω`,
  relative to `μ`.
* `TauCeti.HasWeakFDerivOn`: `U` is a weak (Fréchet) derivative of `u` on `Ω`.
* `TauCeti.HasWeakLineDerivOn.completeSpace`, `TauCeti.HasWeakLineDerivOn.locallyIntegrableOn`,
  `TauCeti.HasWeakLineDerivOn.locallyIntegrableOn_deriv` and
  `TauCeti.HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul`: the components of the
  definition.
* `TauCeti.hasWeakLineDerivOn_iff`: the unbundled restatement of the defining identity.
* `TauCeti.integrable_smul_of_locallyIntegrableOn` and
  `TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn`: the two integrability facts that
  make the defining integrals honest.
* `TauCeti.setIntegral_smul_eq_integral_smul` and
  `TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul`: a test function on `Ω` and its
  directional derivative vanish off `Ω`, so the defining integrals may equivalently be taken over
  `Ω`.
* `TauCeti.HasWeakLineDerivOn.mono` and `TauCeti.HasWeakFDerivOn.mono`: a weak derivative on `Ω`
  is one on every smaller open set.
* `TauCeti.HasWeakLineDerivOn.congr_ae` and `.congr_ae_deriv`, together with their
  `TauCeti.HasWeakFDerivOn` counterparts: the notion only sees the function and its weak
  derivative up to almost-everywhere equality on `Ω`.
* `TauCeti.hasWeakLineDerivOn_zero` and `TauCeti.hasWeakFDerivOn_zero`: the zero function has
  weak derivative `0`.
* `TauCeti.HasWeakLineDerivOn.add`, `.neg`, `.sub`, `.const_smul` and their
  `TauCeti.HasWeakFDerivOn` counterparts: linearity in the function.
* `TauCeti.HasWeakLineDerivOn.add_direction` and `.smul_direction`: linearity in the direction,
  which is what makes the `TauCeti.HasWeakFDerivOn` packaging the right one.
* `TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt` and
  `TauCeti.hasWeakFDerivOn_of_differentiableOn`: classical derivatives that are locally integrable
  on `Ω` are weak derivatives.
* `TauCeti.hasWeakLineDerivOn_const`: against a Haar measure, a constant has weak derivative `0`.
* `TauCeti.hasWeakFDerivOn_testFunction`: a test function has weak derivative the linear
  functional represented by its gradient.
* `TauCeti.HasWeakLineDerivOn.ae_eq` and `TauCeti.HasWeakFDerivOn.ae_eq`: uniqueness almost
  everywhere on `Ω`.
* `TauCeti.HasWeakLineDerivOn.ae_eq_lineDeriv` and `TauCeti.HasWeakFDerivOn.ae_eq_fderiv`: where
  the classical derivative exists and is locally integrable on `Ω`, the weak one agrees with it
  almost everywhere.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E}

/-! ### Derivatives of test functions -/

/-- Outside its support, the directional derivative of a test function vanishes. -/
theorem lineDeriv_eq_zero_of_notMem_tsupport (φ : 𝓓(Ω, ℝ)) {x : E}
    (hx : x ∉ tsupport (φ : E → ℝ)) (v : E) : lineDeriv ℝ (φ : E → ℝ) x v = 0 := by
  have hd : DifferentiableAt ℝ (φ : E → ℝ) x :=
    (φ.contDiff.differentiable (by simp)) x
  rw [hd.lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hx]
  simp

/-! ### The definitions -/

section Defs

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- `HasWeakLineDerivOn μ Ω u u' v` says that `u'` is a **weak derivative** of `u` in the
direction `v` on the open set `Ω`, relative to the measure `μ`: the codomain `F` is complete, both
functions are locally integrable on `Ω`, and the integration-by-parts identity

`∫ (∂_v φ) • u ∂μ = - ∫ φ • u' ∂μ`

holds for every test function `φ : 𝓓(Ω, ℝ)`, that is, for every smooth `φ : E → ℝ` whose support
is compact and contained in `Ω`.

Local integrability and completeness of `F` are part of the definition because without them the
identity is a statement about junk-valued integrals — `MeasureTheory.integral` is `0` on a
non-integrable function, and `0` outright on an incomplete codomain — and would be satisfied by
pairs that are not weakly differentiable at all; see the module docstring. They are recovered by
`TauCeti.HasWeakLineDerivOn.locallyIntegrableOn`, `.locallyIntegrableOn_deriv` and
`.completeSpace`, the last of which is how a proof gets the `CompleteSpace F` instance.

For the intended `μ`, an additive Haar measure, this says exactly that `u'` represents the
distributional derivative `∂_v u` on `Ω`, and `[μ.IsAddHaarMeasure]` is the hypothesis of every
result identifying the two (`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt` and
`TauCeti.hasWeakLineDerivOn_const` among them). For a `μ` that is not translation invariant the
identity is instead the adjoint of `∂_v` relative to `μ` — with a weight `w` it describes
`∂_v (w • u)`, so a constant need not have weak derivative `0`; see the module docstring. -/
def HasWeakLineDerivOn (μ : Measure E) (Ω : Opens E) (u u' : E → F) (v : E) : Prop :=
  CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn u' Ω μ ∧
    ∀ φ : 𝓓(Ω, ℝ), ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ = -∫ x, (φ : E → ℝ) x • u' x ∂μ

/-- The constructor-and-eliminator form of `HasWeakLineDerivOn`, using bundled test functions.
The definition is sealed by the module system, so downstream modules use this theorem rather than
unfolding it. -/
theorem hasWeakLineDerivOn_iff_testFunction :
    HasWeakLineDerivOn μ Ω u u' v ↔
      CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn u' Ω μ ∧
        ∀ φ : 𝓓(Ω, ℝ),
          ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ =
            -∫ x, (φ : E → ℝ) x • u' x ∂μ :=
  Iff.rfl

/-- The codomain of a weak derivative is complete; use as `have := h.completeSpace`. -/
theorem HasWeakLineDerivOn.completeSpace (h : HasWeakLineDerivOn μ Ω u u' v) :
    CompleteSpace F := h.1

/-- A function that has a weak derivative on `Ω` is locally integrable on `Ω`. -/
theorem HasWeakLineDerivOn.locallyIntegrableOn (h : HasWeakLineDerivOn μ Ω u u' v) :
    LocallyIntegrableOn u Ω μ := h.2.1

/-- A weak derivative on `Ω` is locally integrable on `Ω`. -/
theorem HasWeakLineDerivOn.locallyIntegrableOn_deriv (h : HasWeakLineDerivOn μ Ω u u' v) :
    LocallyIntegrableOn u' Ω μ := h.2.2.1

/-- The integration-by-parts identity defining a weak derivative. -/
theorem HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (h : HasWeakLineDerivOn μ Ω u u' v) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ = -∫ x, (φ : E → ℝ) x • u' x ∂μ := h.2.2.2 φ

/-- `HasWeakFDerivOn μ Ω u U` says that `U : E → E →L[ℝ] F` is a **weak (Fréchet) derivative** of
`u` on the open set `Ω`: for every direction `v`, the function `x ↦ U x v` is a weak derivative of
`u` in the direction `v`. In particular `F` is complete and `u` and each `x ↦ U x v` are locally
integrable on `Ω`.

Requiring `u` and `U` to be `Lᵖ` on `Ω` is what cuts out the first-order Sobolev space
`W^{1,p}(Ω)`. -/
def HasWeakFDerivOn (μ : Measure E) (Ω : Opens E) (u : E → F) (U : E → E →L[ℝ] F) : Prop :=
  ∀ v : E, HasWeakLineDerivOn μ Ω u (fun x => U x v) v

/-- A weak Fréchet derivative is equivalently a weak directional derivative in every direction.
This is the constructor-and-eliminator form of `HasWeakFDerivOn`; its sealed definition cannot be
unfolded from a downstream module. -/
theorem hasWeakFDerivOn_iff {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔
      ∀ v : E, HasWeakLineDerivOn μ Ω u (fun x => U x v) v :=
  Iff.rfl

/-- The codomain of a weak Fréchet derivative is complete; use as `have := h.completeSpace`. -/
theorem HasWeakFDerivOn.completeSpace {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    CompleteSpace F := (h 0).completeSpace

/-- A function that has a weak Fréchet derivative on `Ω` is locally integrable on `Ω`. -/
theorem HasWeakFDerivOn.locallyIntegrableOn {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    LocallyIntegrableOn u Ω μ := (h 0).locallyIntegrableOn

/-- The defining identity of a weak derivative, stated for unbundled test functions: for a complete
`F` and locally integrable `u` and `u'`, weak differentiability is exactly the
integration-by-parts identity against every smooth compactly supported function with support
inside `Ω`. -/
theorem hasWeakLineDerivOn_iff [CompleteSpace F] (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, lineDeriv ℝ φ x v • u x ∂μ = -∫ x, φ x • u' x ∂μ :=
  ⟨fun h φ hφ hφc hφs => h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩,
    fun h =>
      ⟨‹CompleteSpace F›, hu, hu', fun φ => h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset⟩⟩

/-- A weak derivative on `Ω` is a weak derivative on every smaller open set: weak
differentiability is a local notion. -/
theorem HasWeakLineDerivOn.mono {Ω' : Opens E} (h : HasWeakLineDerivOn μ Ω u u' v) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDerivOn μ Ω' u u' v :=
  ⟨h.completeSpace, h.locallyIntegrableOn.mono_set hΩ, h.locallyIntegrableOn_deriv.mono_set hΩ,
    fun φ => h.integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩⟩

/-- A weak Fréchet derivative on `Ω` is one on every smaller open set. -/
theorem HasWeakFDerivOn.mono {U : E → E →L[ℝ] F} {Ω' : Opens E} (h : HasWeakFDerivOn μ Ω u U)
    (hΩ : Ω' ≤ Ω) : HasWeakFDerivOn μ Ω' u U := fun v => (h v).mono hΩ

/-- Every direction of a weak Fréchet derivative is a weak directional derivative. -/
theorem HasWeakFDerivOn.hasWeakLineDerivOn {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (v : E) : HasWeakLineDerivOn μ Ω u (fun x => U x v) v := h v

/-- The zero function has weak derivative `0` in every direction, for every `μ`: no translation
invariance is needed, since both sides of the defining identity vanish. Completeness of `F` is
assumed because it is part of `TauCeti.HasWeakLineDerivOn`. This is the zero of the vector space
structure that `TauCeti.HasWeakLineDerivOn.add`, `.neg` and `.const_smul` supply. -/
@[simp]
theorem hasWeakLineDerivOn_zero [CompleteSpace F] :
    HasWeakLineDerivOn μ Ω (0 : E → F) (0 : E → F) v :=
  ⟨‹CompleteSpace F›, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ => by simp⟩

/-- The zero function has weak Fréchet derivative `0`, for every `μ`. -/
@[simp]
theorem hasWeakFDerivOn_zero [CompleteSpace F] : HasWeakFDerivOn μ Ω (0 : E → F) 0 :=
  fun _ => ⟨‹CompleteSpace F›, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ => by simp⟩

/-- Weak differentiation commutes with negation. -/
theorem HasWeakLineDerivOn.neg (h : HasWeakLineDerivOn μ Ω u u' v) :
    HasWeakLineDerivOn μ Ω (-u) (-u') v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.neg, h.locallyIntegrableOn_deriv.neg, fun φ => ?_⟩
  simp only [Pi.neg_apply, smul_neg, integral_neg,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_neg]

/-- Weak Fréchet differentiation commutes with negation. -/
theorem HasWeakFDerivOn.neg {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    HasWeakFDerivOn μ Ω (-u) (-U) := fun v => (h v).neg

/-- Weak differentiation commutes with multiplication by a real scalar. -/
theorem HasWeakLineDerivOn.const_smul (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω (c • u) (c • u') v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.smul c, h.locallyIntegrableOn_deriv.smul c,
    fun φ => ?_⟩
  simp only [Pi.smul_apply, smul_comm _ c, integral_smul,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

/-- Weak Fréchet differentiation commutes with multiplication by a real scalar. -/
theorem HasWeakFDerivOn.const_smul {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) (c : ℝ) :
    HasWeakFDerivOn μ Ω (c • u) (c • U) := fun v => (h v).const_smul c

end Defs

/-! ### Integrability of the defining integrands -/

section Integrability

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- A test function on `Ω` scales a function locally integrable on `Ω` to a globally integrable
one: this is `TestFunction.integrable_bilin` for scalar multiplication. -/
theorem integrable_smul_of_locallyIntegrableOn {w : E → F} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => (φ : E → ℝ) x • w x) μ := by
  simpa using TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hw φ

/-- The direction-`v` derivative of a test function on `Ω` is again a test function on `Ω`, so it
too scales a function locally integrable on `Ω` to a globally integrable one. -/
theorem integrable_lineDeriv_smul_of_locallyIntegrableOn {w : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x => lineDeriv ℝ (φ : E → ℝ) x v • w x) μ := by
  have hcoe : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  simpa [hcoe] using
    integrable_smul_of_locallyIntegrableOn hw (TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ))

omit [OpensMeasurableSpace E] in
/-- A test function on `Ω` vanishes off `Ω`, so integrating `φ • w` over `Ω` is the same as
integrating it over the whole space. -/
theorem setIntegral_smul_eq_integral_smul {w : E → F} (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), (φ : E → ℝ) x • w x ∂μ = ∫ x, (φ : E → ℝ) x • w x ∂μ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]
  simp

omit [OpensMeasurableSpace E] in
/-- The direction-`v` derivative of a test function on `Ω` vanishes off `Ω` too, so the same
truncation holds for `(∂_v φ) • w`. -/
theorem setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul {w : E → F} (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x in (Ω : Set E), lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ =
      ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [lineDeriv_eq_zero_of_notMem_tsupport φ (fun hmem => hx (φ.tsupport_subset hmem)) v]
  simp

/-- Replacing `u` by a function agreeing with it almost everywhere on `Ω` preserves the weak
derivative: only the restriction of `u` to `Ω` is seen. -/
theorem HasWeakLineDerivOn.congr_ae {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω w u' v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.congr hw, h.locallyIntegrableOn_deriv,
    fun φ => ?_⟩
  rw [← h.integral_lineDeriv_smul_eq_neg_integral_smul φ]
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [lineDeriv_eq_zero_of_notMem_tsupport φ (fun h' => hxΩ (φ.tsupport_subset h')) v]
    simp

/-- Replacing `u'` by a function agreeing with it almost everywhere on `Ω` preserves the weak
derivative. -/
theorem HasWeakLineDerivOn.congr_ae_deriv {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u' =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω u w v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.congr hw,
    fun φ => ?_⟩
  rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => hxΩ (φ.tsupport_subset h'))]
    simp

/-- Replacing `u` by a function agreeing with it almost everywhere on `Ω` preserves the weak
Fréchet derivative. -/
theorem HasWeakFDerivOn.congr_ae {U : E → E →L[ℝ] F} {w : E → F} (h : HasWeakFDerivOn μ Ω u U)
    (hw : u =ᵐ[μ.restrict Ω] w) : HasWeakFDerivOn μ Ω w U := fun v => (h v).congr_ae hw

/-- Replacing `U` by a map agreeing with it almost everywhere on `Ω` preserves the weak Fréchet
derivative. -/
theorem HasWeakFDerivOn.congr_ae_deriv {U W : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hW : U =ᵐ[μ.restrict Ω] W) : HasWeakFDerivOn μ Ω u W := fun v =>
  (h v).congr_ae_deriv (hW.mono fun _ hx => congrArg (· v) hx)

end Integrability

/-! ### Linearity -/

section Linearity

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- Weak differentiation is additive. -/
theorem HasWeakLineDerivOn.add {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) :
    HasWeakLineDerivOn μ Ω (u₁ + u₂) (u₁' + u₂') v := by
  refine ⟨h₁.completeSpace, h₁.locallyIntegrableOn.add h₂.locallyIntegrableOn,
    h₁.locallyIntegrableOn_deriv.add h₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • (u₁ + u₂) x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₁ x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₂ x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn φ v)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn_deriv φ)
      (integrable_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn_deriv φ)
  rw [hleft, hright, h₁.integral_lineDeriv_smul_eq_neg_integral_smul φ,
    h₂.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_add]

/-- Weak differentiation is compatible with subtraction. -/
theorem HasWeakLineDerivOn.sub {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) :
    HasWeakLineDerivOn μ Ω (u₁ - u₂) (u₁' - u₂') v := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Weak Fréchet differentiation is additive. -/
theorem HasWeakFDerivOn.add {u₁ u₂ : E → F} {U₁ U₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn μ Ω u₁ U₁) (h₂ : HasWeakFDerivOn μ Ω u₂ U₂) :
    HasWeakFDerivOn μ Ω (u₁ + u₂) (U₁ + U₂) := fun v => (h₁ v).add (h₂ v)

/-- Weak Fréchet differentiation is compatible with subtraction. -/
theorem HasWeakFDerivOn.sub {u₁ u₂ : E → F} {U₁ U₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn μ Ω u₁ U₁) (h₂ : HasWeakFDerivOn μ Ω u₂ U₂) :
    HasWeakFDerivOn μ Ω (u₁ - u₂) (U₁ - U₂) := fun v => (h₁ v).sub (h₂ v)

/-- The weak derivative is additive in the direction of differentiation. Together with
`TauCeti.HasWeakLineDerivOn.smul_direction` this is what makes packaging the directional weak
derivatives into a single continuous linear map, as `TauCeti.HasWeakFDerivOn` does, the right
move. -/
theorem HasWeakLineDerivOn.add_direction {u u₁' u₂' : E → F} {v₁ v₂ : E}
    (h₁ : HasWeakLineDerivOn μ Ω u u₁' v₁) (h₂ : HasWeakLineDerivOn μ Ω u u₂' v₂) :
    HasWeakLineDerivOn μ Ω u (u₁' + u₂') (v₁ + v₂) := by
  refine ⟨h₁.completeSpace, h₁.locallyIntegrableOn,
    h₁.locallyIntegrableOn_deriv.add h₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
  -- Additivity in the direction is Mathlib's `TestFunction.lineDerivCLM_add`, read off pointwise.
  have hsplit : ∀ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) =
      lineDeriv ℝ (φ : E → ℝ) x v₁ + lineDeriv ℝ (φ : E → ℝ) x v₂ := fun x => by
    have h := congrArg (fun T : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) => ((T φ : 𝓓(Ω, ℝ)) : E → ℝ) x)
      (TestFunction.lineDerivCLM_add (𝕜 := ℝ) (v₁ := v₁) (v₂ := v₂))
    simpa [TestFunction.lineDerivCLM_apply_of_le le_top] using h
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) • u x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v₁ • u x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v₂ • u x ∂μ := by
    simp only [hsplit, add_smul]
    exact integral_add
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v₁)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v₂)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn_deriv φ)
      (integrable_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn_deriv φ)
  rw [hleft, hright, h₁.integral_lineDeriv_smul_eq_neg_integral_smul φ,
    h₂.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_add]

end Linearity

/-! ### Scaling the direction -/

section SmulDirection

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- The weak derivative is homogeneous in the direction of differentiation. -/
theorem HasWeakLineDerivOn.smul_direction (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω u (c • u') (c • v) := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.smul c,
    fun φ => ?_⟩
  simp only [lineDeriv_smul, smul_eq_mul, mul_smul, integral_smul,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, Pi.smul_apply, smul_comm _ c, smul_neg]

end SmulDirection

/-! ### Classical derivatives are weak derivatives

This is where the measure has to be an additive Haar measure: integration by parts is available
only for a translation-invariant `μ`, and it is what makes the weak derivative of this section
the classical one. -/

section Classical

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u u' : E → F}

/-- **A classical derivative is a weak derivative.** If `u` has line derivative `u' x` in the
direction `v` at every point of the open set `Ω`, and both `u` and `u'` are locally integrable
on `Ω`, then `u'` is a weak derivative of `u` in the direction `v` on `Ω`. Completeness of `F` is
assumed because it is part of `TauCeti.HasWeakLineDerivOn`.

The proof is Mathlib's integration by parts applied to `u` against a test function; the boundary
term is absent because the test function has compact support inside `Ω`. -/
theorem hasWeakLineDerivOn_of_hasLineDerivAt (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) (h : ∀ x ∈ (Ω : Set E), HasLineDerivAt ℝ u (u' x) x v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨‹CompleteSpace F›, hu, hu', fun φ => ?_⟩
  have hφd := φ.contDiff.differentiable (by simp)
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (f := u) (f' := u') (g := (φ : E → ℝ))
    (g' := fun x => lineDeriv ℝ (φ : E → ℝ) x v) (v := v)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu' φ)
    (by simpa using integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu φ)
    (fun x hx => h x (φ.tsupport_subset hx))
    (fun x _ => (hφd x).lineDifferentiableAt.hasLineDerivAt)
  simpa using key

/-- A constant function has weak derivative `0` in every direction, for `μ` an additive Haar
measure: the first sanity check that `TauCeti.HasWeakLineDerivOn` is not vacuous. Translation
invariance of `μ` is needed — against a weighted measure a constant pairs with `∂_v` of the
weight. -/
theorem hasWeakLineDerivOn_const (c : F) :
    HasWeakLineDerivOn μ Ω (fun _ => c) (fun _ => 0) v :=
  hasWeakLineDerivOn_of_hasLineDerivAt (locallyIntegrableOn_const c) locallyIntegrableOn_zero
    fun x _ => (hasFDerivAt_const c x).hasLineDerivAt v

/-- **A classical Fréchet derivative is a weak one.** If `u` is differentiable at every point of
the open set `Ω`, and both `u` and `fderiv ℝ u` are locally integrable on `Ω`, then `fderiv ℝ u`
is a weak derivative of `u` on `Ω`. -/
theorem hasWeakFDerivOn_of_differentiableOn (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (h : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    HasWeakFDerivOn μ Ω u (fderiv ℝ u) := fun v =>
  hasWeakLineDerivOn_of_hasLineDerivAt hu
    (by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hu')
    fun x hx => (h x hx).hasFDerivAt.hasLineDerivAt v

end Classical

/-! ### Test functions are weakly differentiable

A test function is the basic example: it is smooth, so its classical derivative is also a weak
one. On an inner product space the derivative is recorded through its Riesz representative, the
gradient, which is the form in which the Sobolev spaces consume it. -/

section TestFunction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

open scoped Gradient InnerProductSpace

/-- **A test function is weakly differentiable**, with weak derivative the continuous linear
functional represented by its gradient. -/
theorem hasWeakFDerivOn_testFunction (φ : 𝓓(Ω, ℝ)) :
    HasWeakFDerivOn μ Ω (φ : E → ℝ) fun x => innerSL ℝ (∇ (φ : E → ℝ) x) := by
  have hcoe : (fun x => innerSL ℝ (∇ (φ : E → ℝ) x)) = fderiv ℝ (φ : E → ℝ) := by
    funext x
    ext y
    simp [inner_gradient_left (𝕜 := ℝ) (f := (φ : E → ℝ)) (x := x) (y := y)]
  rw [hcoe]
  refine hasWeakFDerivOn_of_differentiableOn ?_ ?_ fun x _ =>
    (φ.contDiff.differentiable (by simp)) x
  · exact φ.continuous.locallyIntegrable.locallyIntegrableOn _
  · exact (φ.contDiff.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _

end TestFunction

/-! ### Uniqueness -/

section Uniqueness

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} {u : E → F}

/-- **A weak derivative is unique almost everywhere.** Two weak derivatives of `u` in the same
direction on `Ω` agree almost everywhere on `Ω`.

This is the fundamental lemma of the calculus of variations: their difference integrates to zero
against every test function supported in `Ω`, and both are locally integrable on `Ω` because that
is part of `TauCeti.HasWeakLineDerivOn`. Completeness of `F`, which that lemma needs, comes from
`h₁` for the same reason. -/
theorem HasWeakLineDerivOn.ae_eq {u₁' u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u u₂' v) : u₁' =ᵐ[μ.restrict Ω] u₂' := by
  have := h₁.completeSpace
  have hu₁ := h₁.locallyIntegrableOn_deriv
  have hu₂ := h₂.locallyIntegrableOn_deriv
  have key : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ (Ω : Set E) →
      ∫ x, φ x • (u₁' - u₂') x ∂μ = 0 := by
    intro φ hφ hφc hφs
    have hi₁ : Integrable (fun x => φ x • u₁' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₁ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hi₂ : Integrable (fun x => φ x • u₂' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₂ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hsame : ∫ x, φ x • u₁' x ∂μ = ∫ x, φ x • u₂' x ∂μ := by
      have hneg := (h₁.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩).symm.trans
        (h₂.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩)
      simpa using neg_injective hneg
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi₁ hi₂, hsame, sub_self]
  have hzero := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hu₁.sub hu₂) key
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hzero] with x hx hxΩ
  simpa [sub_eq_zero] using hx hxΩ

/-- **A weak Fréchet derivative is unique almost everywhere.** Two weak derivatives of `u` on `Ω`
agree almost everywhere on `Ω`.

The directional statement `TauCeti.HasWeakLineDerivOn.ae_eq` is applied along the finitely many
vectors of a basis of `E`, and the resulting almost-everywhere statements are intersected. -/
theorem HasWeakFDerivOn.ae_eq {U₁ U₂ : E → E →L[ℝ] F} (h₁ : HasWeakFDerivOn μ Ω u U₁)
    (h₂ : HasWeakFDerivOn μ Ω u U₂) : U₁ =ᵐ[μ.restrict Ω] U₂ := by
  set b := Module.finBasis ℝ E with hb
  have hcoord : ∀ i, (fun x => U₁ x (b i)) =ᵐ[μ.restrict Ω] fun x => U₂ x (b i) :=
    fun i => (h₁ (b i)).ae_eq (h₂ (b i))
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  exact ContinuousLinearMap.coe_injective (b.ext fun i => hx i)

end Uniqueness

/-! ### The weak derivative of a classically differentiable function -/

section Comparison

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {u u' : E → F}

/-- **The weak derivative of a classically differentiable function is the classical one.** If `u`
has a line derivative in the direction `v` at every point of `Ω`, and that line derivative is
locally integrable on `Ω`, then any weak derivative of `u` in that direction agrees with it almost
everywhere on `Ω`. Local integrability of `u` itself and completeness of `F` are not hypotheses
here: they are already part of `h`.

Combined with `TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`, this says that the weak derivative
extends the classical one without changing it where the classical one exists. -/
theorem HasWeakLineDerivOn.ae_eq_lineDeriv (h : HasWeakLineDerivOn μ Ω u u' v)
    (hd : LocallyIntegrableOn (fun x => lineDeriv ℝ u x v) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), LineDifferentiableAt ℝ u x v) :
    u' =ᵐ[μ.restrict Ω] fun x => lineDeriv ℝ u x v :=
  have := h.completeSpace
  h.ae_eq (hasWeakLineDerivOn_of_hasLineDerivAt h.locallyIntegrableOn hd
    fun x hx => (hdiff x hx).hasLineDerivAt)

/-- **The weak Fréchet derivative of a differentiable function is `fderiv`.** If `u` is
differentiable at every point of `Ω` and `fderiv ℝ u` is locally integrable on `Ω`, then any weak
Fréchet derivative of `u` agrees with `fderiv ℝ u` almost everywhere on `Ω`. Local integrability
of `u` itself and completeness of `F` are not hypotheses here: they are already part of `h`. -/
theorem HasWeakFDerivOn.ae_eq_fderiv {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hd : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    U =ᵐ[μ.restrict Ω] fderiv ℝ u :=
  have := h.completeSpace
  h.ae_eq (hasWeakFDerivOn_of_differentiableOn h.locallyIntegrableOn hd hdiff)

end Comparison

end TauCeti
