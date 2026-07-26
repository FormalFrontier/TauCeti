/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
-- Public: `Measure.infinitePi` appears in the infinite-product statement.
public import Mathlib.Probability.ProductMeasure

/-!
# Finite product probability-measure kernels

This file provides the basic theory of the finite product of probability measures over a finite
index type, phrased directly over Mathlib's `ProbabilityMeasure.pi`: measurability of the product
kernel, and `Measure.bind`-evaluation of the mixture it induces.

Measurability:
* `measurable_probabilityMeasure_pi` — the product combinator
  `ProbabilityMeasure.pi : (Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`
  is measurable.
* `measurable_probabilityMeasure_pi_toMeasure` — the measure-valued random product
  `ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable, for measurable coordinate
  kernels `ν i`.
* `aemeasurable_probabilityMeasure_pi_toMeasure` — the same map is `AEMeasurable` from
  a.e.-measurable coordinate kernels (`∀ i, AEMeasurable (ν i) μ`); the `_of_measurable` corollary
  is the measurable-input form.
* the constant-coordinate (`fun _ : Fin m => ν ω`) specializations
  `measurable_probabilityMeasure_pi_const_toMeasure` and
  `aemeasurable_probabilityMeasure_pi_const_toMeasure`.
* `measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure` — the **joint** kernel
  `ω ↦ δ_{ν ω} ⊗ (ν ω)^{⊗ Fin m}`, pairing the block kernel with a Dirac mass at the mixing
  measure. This is the joint-space input a conditional (joint-law) reading of the mixture
  identity needs, as opposed to the block kernel alone.

Bind-evaluation of the mixture `μ.bind fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure`:
* `bind_probabilityMeasure_pi_apply` — evaluation on a measurable set as the integral of the product
  kernel, from a.e.-measurable coordinate kernels.
* `bind_probabilityMeasure_pi_pi` — evaluation on a measurable rectangle as the integral of the
  product of coordinate measures, with `Fin m` constant-coordinate forms
  `bind_probabilityMeasure_pi_const_apply` and `bind_probabilityMeasure_pi_const_pi`.

This file does not introduce a new product-kernel structure; the lemmas live directly over Mathlib's
`ProbabilityMeasure.pi`. It advances `TauCetiRoadmap/Exchangeability`, Layer 1 (product kernels and
mixtures), and is motivated by the product-kernel layer of
`cameronfreer/exchangeability` (`MeasureKernels.lean` and the `bind_pi_apply` of
`DeFinetti/CommonEnding.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`), implemented using
Mathlib's `ProbabilityMeasure.pi`, `Measure.bind_apply`, and Giry measurability API; the combinator
generalizes Mathlib's binary `ProbabilityMeasure.measurable_fun_prod` to finite index types.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : Measure Ω}

/-- The finite product combinator `ProbabilityMeasure.pi` is a measurable map
`(Π i, ProbabilityMeasure (α i)) → ProbabilityMeasure (Π i, α i)`. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi :
    Measurable (ProbabilityMeasure.pi : (∀ i, ProbabilityMeasure (α i)) → ProbabilityMeasure
      (∀ i, α i)) := by
  have hcore : Measurable fun p : ∀ i, ProbabilityMeasure (α i) =>
      (ProbabilityMeasure.pi p).toMeasure := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi univ '' Set.pi univ fun i => {s : Set (α i) | MeasurableSet s})
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨B, hB, rfl⟩
    have hBmeas : ∀ i, MeasurableSet (B i) := fun i => hB i (mem_univ i)
    simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.measurable_prod Finset.univ fun i _ =>
      (Measure.measurable_coe (hBmeas i)).comp (measurable_subtype_coe.comp (measurable_pi_apply i))
  exact hcore.subtype_mk

/-- A finite product of measurable probability-measure kernels is a measurable measure-valued map:
if each `ν i : Ω → ProbabilityMeasure (α i)` is measurable, then
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` is measurable. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_toMeasure
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    Measurable fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure :=
  (measurable_subtype_coe.comp measurable_probabilityMeasure_pi).comp (measurable_pi_lambda _ hν)

/-- A finite product of a.e.-measurable probability-measure kernels is an a.e.-measurable
measure-valued map: if each `ν i : Ω → ProbabilityMeasure (α i)` is `AEMeasurable`, then so is
`ω ↦ (ProbabilityMeasure.pi fun i => ν i ω).toMeasure`. -/
@[fun_prop]
theorem aemeasurable_probabilityMeasure_pi_toMeasure
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, AEMeasurable (ν i) μ) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) μ :=
  (measurable_subtype_coe.comp measurable_probabilityMeasure_pi).comp_aemeasurable
    (aemeasurable_pi_lambda _ hν)

/-- Measurable-input corollary of `aemeasurable_probabilityMeasure_pi_toMeasure`. -/
theorem aemeasurable_probabilityMeasure_pi_toMeasure_of_measurable
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, Measurable (ν i)) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) μ :=
  aemeasurable_probabilityMeasure_pi_toMeasure ν fun i => (hν i).aemeasurable

/-- Constant-coordinate specialization of `measurable_probabilityMeasure_pi_toMeasure`: the random
product `ω ↦ (ν ω)^{⊗ Fin m}` is measurable. -/
@[fun_prop]
theorem measurable_probabilityMeasure_pi_const_toMeasure {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    Measurable fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  measurable_probabilityMeasure_pi_toMeasure (fun _ => ν) (fun _ => hν)

/-- Constant-coordinate specialization of `aemeasurable_probabilityMeasure_pi_toMeasure`: the random
product `ω ↦ (ν ω)^{⊗ Fin m}` is `AEMeasurable` from an a.e.-measurable kernel `ν`. -/
@[fun_prop]
theorem aemeasurable_probabilityMeasure_pi_const_toMeasure {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : AEMeasurable ν μ) :
    AEMeasurable (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
  aemeasurable_probabilityMeasure_pi_toMeasure (fun _ => ν) (fun _ => hν)

/-- **Joint-kernel measurability.** The random measure
`ω ↦ δ_{ν ω} ⊗ (ν ω)^{⊗ Fin m}` on `ProbabilityMeasure α × (Fin m → α)` is measurable.

This is the joint-space companion of `measurable_probabilityMeasure_pi_const_toMeasure`: where that
one gives the block kernel alone, this one pairs it with a Dirac mass at the mixing measure itself,
which is what a conditional (joint-law) reading of the de Finetti mixture identity has to speak
about. It supplies the `Measure.bind_apply` and measure-extensionality inputs on the joint space
(`TauCetiRoadmap/Exchangeability/README.md`, Layer 1). No hypotheses beyond measurability of `ν`. -/
-- The product step is Mathlib's `ProbabilityMeasure.measurable_fun_prod`; all this adds is that
-- both components are measurable in `ω`. Applying it needs both presented as
-- `ProbabilityMeasure`-valued, hence the `subtype_mk` bundling of the Dirac side.
@[fun_prop]
theorem measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure {α : Type*}
    [MeasurableSpace α] {m : ℕ} (ν : Ω → ProbabilityMeasure α) (hν : Measurable ν) :
    Measurable fun ω =>
      (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure := by
  have hdirac : Measurable fun ω =>
      (⟨Measure.dirac (ν ω), inferInstance⟩ : ProbabilityMeasure (ProbabilityMeasure α)) :=
    (Measure.measurable_dirac.comp hν).subtype_mk
  have hpi : Measurable fun ω => ProbabilityMeasure.pi fun _ : Fin m => ν ω :=
    measurable_probabilityMeasure_pi.comp (measurable_pi_lambda _ fun _ => hν)
  exact ProbabilityMeasure.measurable_fun_prod.comp (hdirac.prodMk hpi)

/-- **Infinite-product measurability.** The countable product `p ↦ p^{⊗ℕ}` is a measurable map
`ProbabilityMeasure α → Measure (ℕ → α)`.

This is the countable-index companion of `measurable_probabilityMeasure_pi_const_toMeasure`. It is
what lets `Measure.infinitePi` appear under a `Measure.bind`, i.e. lets a mixture of infinite
product laws be formed — the shape the de Finetti mixture representation takes. Mathlib supplies
`Measure.infinitePi` and its projective-limit API but not its measurability in the measure
argument. -/
@[fun_prop]
theorem measurable_infinitePi_const {α : Type*} [MeasurableSpace α] :
    Measurable fun p : ProbabilityMeasure α =>
      Measure.infinitePi (fun _ : ℕ => (p : Measure α)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := measurableCylinders (fun _ : ℕ => α)) generateFrom_measurableCylinders.symm
    isSetRing_measurableCylinders.isSetSemiring.isPiSystem ?_
  intro t ht
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
  have hval : ∀ p : ProbabilityMeasure α,
      Measure.infinitePi (fun _ : ℕ => (p : Measure α)) (cylinder s S)
        = Measure.pi (fun _ : s => (p : Measure α)) S :=
    fun p => Measure.infinitePi_cylinder _ hS
  simp_rw [hval]
  exact (Measure.measurable_coe hS).comp
    (measurable_probabilityMeasure_pi_toMeasure (fun _ : s => (id : ProbabilityMeasure α → _))
      fun _ => measurable_id)

/-- **Bind-evaluation.** Evaluating the mixture
`μ.bind fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure` on a measurable set `s` gives
`∫⁻ ω, … s ∂μ`, requiring only a.e.-measurability of each coordinate kernel `ν i`. -/
theorem bind_probabilityMeasure_pi_apply
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, AEMeasurable (ν i) μ)
    {s : Set (∀ i, α i)} (hs : MeasurableSet s) :
    (μ.bind fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) s
      = ∫⁻ ω, (ProbabilityMeasure.pi fun i => ν i ω).toMeasure s ∂μ :=
  Measure.bind_apply hs (aemeasurable_probabilityMeasure_pi_toMeasure ν hν)

-- Not `@[simp]`: `simp` unfolds `(ProbabilityMeasure.pi …).toMeasure` via `toMeasure_pi`, so the
-- `.toMeasure`-shaped (`MixedIIDWith`-shaped) LHS here is not simp-normal and a `@[simp]`
-- tag never fires; this is an explicit `rw` lemma in the shape later de Finetti code rewrites with.
/-- **Bind-evaluation on a rectangle.** On a rectangle `Set.univ.pi B`, the mixture equals
`∫⁻ ω, ∏ i, (ν i ω) (B i) ∂μ`. -/
theorem bind_probabilityMeasure_pi_pi
    (ν : ∀ i, Ω → ProbabilityMeasure (α i)) (hν : ∀ i, AEMeasurable (ν i) μ)
    (B : ∀ i, Set (α i)) (hB : ∀ i, MeasurableSet (B i)) :
    (μ.bind fun ω => (ProbabilityMeasure.pi fun i => ν i ω).toMeasure) (Set.univ.pi B)
      = ∫⁻ ω, ∏ i, (ν i ω : Measure (α i)) (B i) ∂μ := by
  rw [bind_probabilityMeasure_pi_apply ν hν (MeasurableSet.univ_pi hB)]
  simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]

/-- Constant-coordinate `Fin m` specialization of `bind_probabilityMeasure_pi_apply`. -/
theorem bind_probabilityMeasure_pi_const_apply {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : AEMeasurable ν μ)
    {s : Set (Fin m → α)} (hs : MeasurableSet s) :
    (μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) s
      = ∫⁻ ω, (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure s ∂μ :=
  bind_probabilityMeasure_pi_apply (fun _ => ν) (fun _ => hν) hs

/-- Constant-coordinate `Fin m` specialization of `bind_probabilityMeasure_pi_pi`: the
finite-block mixture identity the de Finetti common ending consumes. -/
theorem bind_probabilityMeasure_pi_const_pi {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : Ω → ProbabilityMeasure α) (hν : AEMeasurable ν μ)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    (μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) (Set.univ.pi B)
      = ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ :=
  bind_probabilityMeasure_pi_pi (fun _ => ν) (fun _ => hν) B hB

end MeasureTheory

end TauCeti
