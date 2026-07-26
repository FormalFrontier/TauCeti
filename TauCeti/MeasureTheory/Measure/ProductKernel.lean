/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
-- Public: `Measure.infinitePi` appears in the infinite-product statement.
public import Mathlib.Probability.ProductMeasure

/-!
# Product probability-measure kernels

This file provides the basic theory of products of probability measures, phrased directly over
Mathlib's `ProbabilityMeasure.pi` and `Measure.infinitePi`: measurability of the product kernel —
finite and countable — and `Measure.bind`-evaluation of the mixture the finite product induces.

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
* `measurable_infinitePi` — the product `p ↦ ⊗ᵢ p i` over an **arbitrary** index type, of a
  dependent family of probability measures, is measurable in the measure argument;
  `measurable_infinitePi_const` is the `ℕ`-constant-power specialization `p ↦ p^{⊗ℕ}`. Mathlib
  supplies `Measure.infinitePi` and its projective-limit API but not this measurability, which is
  what a mixture of such products needs for `Measure.bind_apply` and the expected evaluation of
  the mixture as an integral.
* `map_prefix_infinitePi_const` — the finite-prefix marginal of a countable power, `p^{⊗ℕ}`
  restricted to its first `n` coordinates being `p^{⊗ Fin n}`. Mathlib's
  `Measure.infinitePi_map_restrict` gives the marginal indexed by a coerced `Finset`; this is the
  `Fin n`-prefix form that prefix-marginal arguments on `ℕ → α` use.

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

/-- **Product measurability in the measure argument.** For an arbitrary index type and a dependent
family of measurable spaces, `p ↦ ⊗ᵢ p i` is a measurable map
`(∀ i, ProbabilityMeasure (β i)) → Measure (∀ i, β i)`.

This is the arbitrary-index companion of `measurable_probabilityMeasure_pi_toMeasure`, which covers
the finite case through `ProbabilityMeasure.pi`. Mathlib supplies `Measure.infinitePi` and its
projective-limit API but not this measurability, which is what a mixture of such products needs for
`Measure.bind_apply` and for evaluating the mixture as an integral — the shape the de Finetti
mixture representation takes. -/
@[fun_prop]
theorem measurable_infinitePi {ι' : Type*} {β : ι' → Type*} [∀ i, MeasurableSpace (β i)] :
    Measurable fun p : ∀ i, ProbabilityMeasure (β i) =>
      Measure.infinitePi fun i => (p i : Measure (β i)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := measurableCylinders β) generateFrom_measurableCylinders.symm
    isSetRing_measurableCylinders.isSetSemiring.isPiSystem ?_
  intro t ht
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
  have hval : ∀ p : ∀ i, ProbabilityMeasure (β i),
      Measure.infinitePi (fun i => (p i : Measure (β i))) (cylinder s S)
        = Measure.pi (fun i : s => (p i : Measure (β i))) S :=
    fun p => Measure.infinitePi_cylinder _ hS
  simp_rw [hval]
  simpa only [ProbabilityMeasure.toMeasure_pi, Function.comp_def] using
    (Measure.measurable_coe hS).comp
      (measurable_probabilityMeasure_pi_toMeasure
        (fun i : s => fun p : ∀ j, ProbabilityMeasure (β j) => p i.1)
        fun i => measurable_pi_apply i.1)

/-- Constant-coordinate `ℕ` specialization of `measurable_infinitePi`: the countable power
`p ↦ p^{⊗ℕ}` is measurable. -/
@[fun_prop]
theorem measurable_infinitePi_const {α : Type*} [MeasurableSpace α] :
    Measurable fun p : ProbabilityMeasure α =>
      Measure.infinitePi (fun _ : ℕ => (p : Measure α)) :=
  measurable_infinitePi.comp (measurable_pi_lambda _ fun _ => measurable_id)

/-- **Finite-prefix marginal of a countable product.** Restricting `p^{⊗ℕ}` to its first `n`
coordinates gives the finite product `p^{⊗ Fin n}`.

Mathlib's `Measure.infinitePi_map_restrict` gives the marginal along a `Finset.restrict`, indexed by
the coerced finite set; this is the `Fin n`-prefix form, which is what prefix-marginal arguments on
`ℕ → α` actually use. Stated with the bare prefix map rather than any particular prefix
abbreviation, so it stays independent of downstream conventions. -/
theorem map_prefix_infinitePi_const {α : Type*} [MeasurableSpace α] (p : ProbabilityMeasure α)
    (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (p : Measure α))).map (fun x : ℕ → α => fun i : Fin n => x i)
      = Measure.pi (fun _ : Fin n => (p : Measure α)) := by
  have hmeas : Measurable (fun x : ℕ → α => fun i : Fin n => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  refine (Measure.pi_eq fun t ht => ?_).symm
  classical
  have hpre : (fun x : ℕ → α => fun i : Fin n => x i) ⁻¹' Set.univ.pi t
      = Set.pi ↑(Finset.range n) (fun j => if h : j < n then t ⟨j, h⟩ else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Finset.coe_range,
      Set.mem_Iio]
    constructor
    · intro hx j hj
      simpa [hj] using hx ⟨j, hj⟩
    · intro hx i
      simpa [i.2] using hx i.1 i.2
  have hmt : ∀ j ∈ Finset.range n,
      MeasurableSet (if h : j < n then t ⟨j, h⟩ else (Set.univ : Set α)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simpa [hj] using ht ⟨j, hj⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht), hpre,
    Measure.infinitePi_pi (μ := fun _ : ℕ => (p : Measure α)) hmt]
  rw [Finset.prod_range fun j => (p : Measure α) (if h : j < n then t ⟨j, h⟩ else Set.univ)]
  exact Finset.prod_congr rfl fun i _ => by simp [i.2]

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
