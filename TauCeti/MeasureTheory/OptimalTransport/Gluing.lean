/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Gluing transport plans

Two transport plans that share an intermediate marginal can be realised simultaneously: if `π` is a
measure on `X × Y` whose second marginal agrees with the first marginal of a measure `σ` on
`Y × Z`, then there is a measure `γ` on `X × Y × Z` whose `(X, Y)`-marginal is `π` and whose
`(Y, Z)`-marginal is `σ`. This is the gluing lemma, and it is what lets transport costs be composed
— it is the measure-theoretic input to the triangle inequality for Wasserstein distances and to
the composition of couplings.

The construction is a composition-product against a conditional kernel, so it needs a
disintegration of one of the two plans, hence a standard Borel hypothesis on one of the two outer
spaces. The middle space `Y` carries no hypothesis at all.

## Main definitions

* `TauCeti.Measure.glue π κ` — the measure on `X × Y × Z` obtained by extending a measure
  `π : Measure (X × Y)` along a kernel `κ : Kernel Y Z` acting on the middle coordinate. It is the
  associated right-nested form of `π ⊗ₘ Kernel.prodMkLeft X κ`.

## Main statements

* `TauCeti.Measure.map_prodMap_id_fst_glue` — the `(X, Y)`-marginal of `glue π κ` is `π`;
* `TauCeti.Measure.snd_glue` — its `(Y, Z)`-marginal is `π.snd ⊗ₘ κ`;
* `TauCeti.Measure.lintegral_glue` — the iterated-integral formula against `glue π κ`;
* `TauCeti.Measure.glue_deterministic` — gluing against a deterministic kernel is a pushforward,
  so a graph plan glues without adding randomness;
* `TauCeti.Measure.exists_glue_of_standardBorel_right` and
  `TauCeti.Measure.exists_glue_of_standardBorel_left` — **the gluing lemma**, in the two regimes
  obtained by disintegrating `σ` over `Y` (which needs `Z` standard Borel) and by disintegrating
  `π` over `Y` (which needs `X` standard Borel);
* `TauCeti.Measure.exists_comp_of_exists_glue` — the composition of plans read off a glued measure,
  with `TauCeti.Measure.exists_comp_of_standardBorel_right` and
  `TauCeti.Measure.exists_comp_of_standardBorel_left` its two concrete forms;
* `TauCeti.Measure.lintegral_map_prodMap_id_snd_le` — the composition estimate: a cost on `X × Z`
  dominated by the sum of a cost on `X × Y` and a cost on `Y × Z` integrates against the composed
  plan to at most the sum of the two integrals. This is the mechanism behind the triangle
  inequality for transport costs.

## Implementation notes

Marginals of a measure on `X × Y × Z` are written as pushforwards along `Prod.map id Prod.fst`
(the `(X, Y)`-marginal), `Prod.map id Prod.snd` (the `(X, Z)`-marginal) and `Prod.snd` (the
`(Y, Z)`-marginal, which is `MeasureTheory.Measure.snd`).

The hypothesis relating the two plans is stated as `π.snd = σ.fst` rather than through a coupling
predicate: gluing needs neither of the two outer marginals, only the agreement of the middle one,
and stating it this way keeps the theorems usable by any packaging of couplings built on
`MeasureTheory.Measure.fst`/`MeasureTheory.Measure.snd`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Measure

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The gluing of a measure `π` on `X × Y` with a kernel `κ : Kernel Y Z` along the middle
coordinate: the measure on `X × Y × Z` which draws `(x, y)` from `π` and then `z` from `κ y`.

Its `(X, Y)`-marginal is `π` (`TauCeti.Measure.map_prodMap_id_fst_glue`) and its `(Y, Z)`-marginal
is `π.snd ⊗ₘ κ` (`TauCeti.Measure.snd_glue`), so choosing `κ` to be a conditional kernel of a
second plan `σ` glues `π` and `σ`. -/
def glue (π : Measure (X × Y)) (κ : Kernel Y Z) : Measure (X × Y × Z) :=
  (π ⊗ₘ Kernel.prodMkLeft X κ).map MeasurableEquiv.prodAssoc

variable (π : Measure (X × Y)) (κ : Kernel Y Z)

/-- The measure a gluing assigns to a measurable set: integrate the kernel mass of the fibre
against the plan being extended. -/
theorem glue_apply [SFinite π] [IsSFiniteKernel κ] {s : Set (X × Y × Z)} (hs : MeasurableSet s) :
    glue π κ s = ∫⁻ w, κ w.2 {z | (w.1, w.2, z) ∈ s} ∂π := by
  rw [glue, MeasureTheory.Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs,
    MeasureTheory.Measure.compProd_apply (hs.preimage MeasurableEquiv.prodAssoc.measurable)]
  rfl

/-- Integration against a gluing is the iterated integral: first over the fibre of the kernel,
then over the plan being extended. -/
theorem lintegral_glue [SFinite π] [IsSFiniteKernel κ] {f : X × Y × Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(glue π κ) = ∫⁻ w, ∫⁻ z, f (w.1, w.2, z) ∂(κ w.2) ∂π := by
  rw [glue, lintegral_map hf MeasurableEquiv.prodAssoc.measurable]
  exact MeasureTheory.Measure.lintegral_compProd (hf.comp MeasurableEquiv.prodAssoc.measurable)

instance instIsFiniteMeasureGlue [IsFiniteMeasure π] [IsFiniteKernel κ] :
    IsFiniteMeasure (glue π κ) := by
  rw [glue]; infer_instance

instance instIsProbabilityMeasureGlue [IsProbabilityMeasure π] [IsMarkovKernel κ] :
    IsProbabilityMeasure (glue π κ) := by
  rw [glue]
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    MeasurableEquiv.prodAssoc.measurable.aemeasurable

/-- The `(X, Y)`-marginal of a gluing is the plan it extends. -/
@[simp]
theorem map_prodMap_id_fst_glue [SFinite π] [IsMarkovKernel κ] :
    (glue π κ).map (Prod.map id Prod.fst) = π := by
  have h : (Prod.map (id : X → X) (Prod.fst : Y × Z → Y)) ∘
      ⇑(MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)) = Prod.fst := rfl
  rw [glue, MeasureTheory.Measure.map_map (measurable_id.prodMap measurable_fst)
    MeasurableEquiv.prodAssoc.measurable, h]
  exact MeasureTheory.Measure.fst_compProd π _

/-- The `(Y, Z)`-marginal of a gluing is the composition-product of the middle marginal with the
kernel. -/
@[simp]
theorem snd_glue [SFinite π] [IsSFiniteKernel κ] : (glue π κ).snd = π.snd ⊗ₘ κ := by
  have h : (Prod.snd : X × Y × Z → Y × Z) ∘
      ⇑(MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z))
      = Prod.map (Prod.snd : X × Y → Y) (id : Z → Z) := rfl
  -- `Kernel.prodMkLeft X κ` is `Kernel.comap κ Prod.snd measurable_snd`, so the kernel factors
  -- through the middle coordinate and `map_prodMap_compProd_comap` applies.
  calc (glue π κ).snd
      = (π ⊗ₘ Kernel.comap κ (Prod.snd : X × Y → Y) measurable_snd).map
          (Prod.map Prod.snd id) := by
        rw [glue, MeasureTheory.Measure.snd, MeasureTheory.Measure.map_map measurable_snd
          MeasurableEquiv.prodAssoc.measurable, h]
        rfl
    _ = π.snd ⊗ₘ κ := map_prodMap_compProd_comap π κ measurable_snd

/-- The `X`-marginal of a gluing is the `X`-marginal of the plan it extends. -/
@[simp]
theorem fst_glue [SFinite π] [IsMarkovKernel κ] : (glue π κ).fst = π.fst := by
  have h : (Prod.fst : X × Y → X) ∘ Prod.map (id : X → X) (Prod.fst : Y × Z → Y)
      = Prod.fst := rfl
  conv_rhs => rw [← map_prodMap_id_fst_glue π κ]
  rw [MeasureTheory.Measure.fst, MeasureTheory.Measure.fst,
    MeasureTheory.Measure.map_map measurable_fst (measurable_id.prodMap measurable_fst), h]

/-- The middle marginal of a gluing is the middle marginal of the plan it extends: gluing does not
disturb the coordinate the kernel is indexed by. -/
theorem fst_snd_glue [SFinite π] [IsMarkovKernel κ] : (glue π κ).snd.fst = π.snd := by
  rw [snd_glue, MeasureTheory.Measure.fst_compProd]

/-- Gluing against a deterministic kernel is a pushforward: the third coordinate is the image of
the second. This is the graph-plan case, in which the glued measure carries no new randomness. -/
@[simp]
theorem glue_deterministic [SFinite π] {T : Y → Z} (hT : Measurable T) :
    glue π (Kernel.deterministic T hT) = π.map fun w ↦ (w.1, w.2, T w.2) := by
  have h : Kernel.prodMkLeft X (Kernel.deterministic T hT)
      = Kernel.deterministic (fun w : X × Y ↦ T w.2) (hT.comp measurable_snd) := rfl
  rw [glue, h, MeasureTheory.Measure.compProd_deterministic,
    MeasureTheory.Measure.map_map MeasurableEquiv.prodAssoc.measurable
      (measurable_id.prod (hT.comp measurable_snd))]
  rfl

section Gluing

variable (σ : Measure (Y × Z))

/-- Gluing `π` against a conditional kernel of `σ` recovers `σ` as the `(Y, Z)`-marginal, as soon
as the two plans share their middle marginal. -/
theorem snd_glue_condKernel [StandardBorelSpace Z] [Nonempty Z] [SFinite π] [IsFiniteMeasure σ]
    (hπσ : π.snd = σ.fst) : (glue π σ.condKernel).snd = σ := by
  rw [snd_glue, hπσ, MeasureTheory.Measure.disintegrate]

/-- **The gluing lemma**, obtained by disintegrating the second plan over the middle space.

Two plans sharing a middle marginal, `π.snd = σ.fst`, admit a joint law on `X × Y × Z` with `π` and
`σ` as its two consecutive two-coordinate marginals. Only the last space is assumed standard Borel;
the middle space `Y` carries no hypothesis.

When `Z` is nonempty, the explicit witness is `glue π σ.condKernel`; use it instead of this
statement when the probability-measure or finiteness instances of the glued measure are needed. -/
theorem exists_glue_of_standardBorel_right [StandardBorelSpace Z] [IsFiniteMeasure σ]
    (hπσ : π.snd = σ.fst) :
    ∃ γ : Measure (X × Y × Z), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ := by
  let _ : IsFiniteMeasure π := ⟨by
    rw [← MeasureTheory.Measure.snd_univ, hπσ]
    exact measure_lt_top _ _⟩
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · let _ := hZ
    have hσ : σ = 0 := MeasureTheory.Measure.eq_zero_of_isEmpty σ
    have hπ : π = 0 := by
      rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← MeasureTheory.Measure.snd_univ,
        hπσ, hσ]
      simp
    exact ⟨0, by simp [hπ], by simp [hσ]⟩
  · let _ := hZ
    exact ⟨glue π σ.condKernel, map_prodMap_id_fst_glue π _, snd_glue_condKernel π σ hπσ⟩

/-- **The gluing lemma**, obtained by disintegrating the first plan over the middle space.

This is the mirror image of `TauCeti.Measure.exists_glue_of_standardBorel_right`: it assumes the
*first* space standard Borel instead of the last one. Neither version implies the other, and the
middle space `Y` again carries no hypothesis. -/
theorem exists_glue_of_standardBorel_left [StandardBorelSpace X] [IsFiniteMeasure π]
    (hπσ : π.snd = σ.fst) :
    ∃ γ : Measure (X × Y × Z), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ := by
  let _ : IsFiniteMeasure σ := ⟨by
    rw [← MeasureTheory.Measure.fst_univ, ← hπσ]
    exact measure_lt_top _ _⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · let _ := hX
    have hπ : π = 0 := MeasureTheory.Measure.eq_zero_of_isEmpty π
    have hσ : σ = 0 := by
      rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← MeasureTheory.Measure.fst_univ,
        ← hπσ, hπ]
      simp
    exact ⟨0, by simp [hπ], by simp [hσ]⟩
  let _ := hX
  -- Glue the swapped second plan `σ.map Prod.swap : Measure (Z × Y)` against a conditional kernel
  -- of the swapped first plan `π.map Prod.swap : Measure (Y × X)`, whose disintegration is the one
  -- `X` standard Borel provides, then permute the three coordinates back.
  set τ : Measure (Z × Y) := σ.map Prod.swap with hτ
  set ϖ : Measure (Y × X) := π.map Prod.swap with hϖ
  have hϖfst : ϖ.fst = σ.fst := by rw [hϖ, MeasureTheory.Measure.fst_map_swap, hπσ]
  have hτsnd : τ.snd = σ.fst := by rw [hτ, MeasureTheory.Measure.snd_map_swap]
  have hswapπ : ϖ.map Prod.swap = π := by
    rw [hϖ, MeasureTheory.Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq,
      MeasureTheory.Measure.map_id]
  have hswapσ : τ.map Prod.swap = σ := by
    rw [hτ, MeasureTheory.Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq,
      MeasureTheory.Measure.map_id]
  refine ⟨(glue τ ϖ.condKernel).map fun q ↦ (q.2.2, q.2.1, q.1), ?_, ?_⟩
  · have h : (Prod.map (id : X → X) (Prod.fst : Y × Z → Y)) ∘
        (fun q : Z × Y × X ↦ (q.2.2, q.2.1, q.1)) = Prod.swap ∘ Prod.snd := rfl
    rw [MeasureTheory.Measure.map_map (measurable_id.prodMap measurable_fst) (by fun_prop), h,
      ← MeasureTheory.Measure.map_map measurable_swap measurable_snd,
      ← MeasureTheory.Measure.snd, snd_glue, hτsnd, ← hϖfst,
      MeasureTheory.Measure.disintegrate, hswapπ]
  · have h : (Prod.snd : X × Y × Z → Y × Z) ∘ (fun q : Z × Y × X ↦ (q.2.2, q.2.1, q.1))
        = Prod.swap ∘ Prod.map id Prod.fst := rfl
    rw [MeasureTheory.Measure.snd,
      MeasureTheory.Measure.map_map measurable_snd (by fun_prop), h,
      ← MeasureTheory.Measure.map_map measurable_swap (measurable_id.prodMap measurable_fst),
      map_prodMap_id_fst_glue, hswapσ]

end Gluing

section Comp

variable {π : Measure (X × Y)} {σ : Measure (Y × Z)} {γ : Measure (X × Y × Z)}

/-- The composition of two plans is the `(X, Z)`-marginal of a glued measure. Its first marginal is
the first marginal of the first plan. -/
theorem fst_map_prodMap_id_snd (hγπ : γ.map (Prod.map id Prod.fst) = π) :
    (γ.map (Prod.map id Prod.snd)).fst = π.fst := by
  have h : (Prod.fst : X × Z → X) ∘ Prod.map (id : X → X) (Prod.snd : Y × Z → Z)
      = Prod.fst ∘ Prod.map (id : X → X) (Prod.fst : Y × Z → Y) := rfl
  rw [← hγπ, MeasureTheory.Measure.fst, MeasureTheory.Measure.fst,
    MeasureTheory.Measure.map_map measurable_fst (measurable_id.prodMap measurable_snd),
    MeasureTheory.Measure.map_map measurable_fst (measurable_id.prodMap measurable_fst), h]

/-- The second marginal of the composition of two plans is the second marginal of the second
plan. -/
theorem snd_map_prodMap_id_snd (hγσ : γ.snd = σ) :
    (γ.map (Prod.map id Prod.snd)).snd = σ.snd := by
  have h : (Prod.snd : X × Z → Z) ∘ Prod.map (id : X → X) (Prod.snd : Y × Z → Z)
      = Prod.snd ∘ (Prod.snd : X × Y × Z → Y × Z) := rfl
  rw [← hγσ, MeasureTheory.Measure.snd, MeasureTheory.Measure.snd,
    MeasureTheory.Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd),
    MeasureTheory.Measure.snd, MeasureTheory.Measure.map_map measurable_snd measurable_snd, h]

/-- The composition estimate. If a cost on `X × Z` is dominated pointwise by the sum of a cost on
`X × Y` and a cost on `Y × Z`, then the composition of two glued plans costs at most the sum of
their two costs.

This is the mechanism behind the triangle inequality for transport costs: taking `c`, `c₁` and `c₂`
to be a ground distance recovers `d (x, z) ≤ d (x, y) + d (y, z)`, and the glued measure is what
lets the three integrals be compared on a common space. -/
theorem lintegral_map_prodMap_id_snd_le (hγπ : γ.map (Prod.map id Prod.fst) = π)
    (hγσ : γ.snd = σ) {c : X × Z → ℝ≥0∞} {c₁ : X × Y → ℝ≥0∞} {c₂ : Y × Z → ℝ≥0∞}
    (hc : Measurable c) (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (hle : ∀ x y z, c (x, z) ≤ c₁ (x, y) + c₂ (y, z)) :
    ∫⁻ q, c q ∂(γ.map (Prod.map id Prod.snd)) ≤ (∫⁻ w, c₁ w ∂π) + ∫⁻ v, c₂ v ∂σ := by
  rw [lintegral_map hc (measurable_id.prodMap measurable_snd)]
  calc ∫⁻ p, c (Prod.map id Prod.snd p) ∂γ
      ≤ ∫⁻ p, (c₁ (Prod.map id Prod.fst p) + c₂ p.2) ∂γ :=
        lintegral_mono fun p ↦ hle p.1 p.2.1 p.2.2
    _ = (∫⁻ p, c₁ (Prod.map id Prod.fst p) ∂γ) + ∫⁻ p, c₂ p.2 ∂γ :=
        lintegral_add_left (hc₁.comp (measurable_id.prodMap measurable_fst)) _
    _ = (∫⁻ w, c₁ w ∂π) + ∫⁻ v, c₂ v ∂σ := by
        rw [← hγπ, ← hγσ, lintegral_map hc₁ (measurable_id.prodMap measurable_fst),
          MeasureTheory.Measure.snd, lintegral_map hc₂ measurable_snd]

/-- The composition of two plans, read off a glued measure: the `(X, Z)`-marginal of a gluing of
`π` and `σ` has the outer marginals of `π` and `σ`. -/
theorem exists_comp_of_exists_glue
    (h : ∃ γ : Measure (X × Y × Z), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    ∃ ζ : Measure (X × Z), ζ.fst = π.fst ∧ ζ.snd = σ.snd :=
  let ⟨γ, hγπ, hγσ⟩ := h
  ⟨γ.map (Prod.map id Prod.snd), fst_map_prodMap_id_snd hγπ, snd_map_prodMap_id_snd hγσ⟩

/-- The composed plan of `TauCeti.Measure.exists_comp_of_exists_glue`, together with the cost
estimate of `TauCeti.Measure.lintegral_map_prodMap_id_snd_le`. -/
theorem exists_comp_lintegral_le_of_exists_glue
    (h : ∃ γ : Measure (X × Y × Z), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ)
    {c : X × Z → ℝ≥0∞} {c₁ : X × Y → ℝ≥0∞} {c₂ : Y × Z → ℝ≥0∞}
    (hc : Measurable c) (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (hle : ∀ x y z, c (x, z) ≤ c₁ (x, y) + c₂ (y, z)) :
    ∃ ζ : Measure (X × Z), ζ.fst = π.fst ∧ ζ.snd = σ.snd ∧
      ∫⁻ q, c q ∂ζ ≤ (∫⁻ w, c₁ w ∂π) + ∫⁻ v, c₂ v ∂σ :=
  let ⟨γ, hγπ, hγσ⟩ := h
  ⟨γ.map (Prod.map id Prod.snd), fst_map_prodMap_id_snd hγπ, snd_map_prodMap_id_snd hγσ,
    lintegral_map_prodMap_id_snd_le hγπ hγσ hc hc₁ hc₂ hle⟩

/-- Two plans sharing a middle marginal compose to a plan with the two outer marginals, when the
last space is standard Borel. -/
theorem exists_comp_of_standardBorel_right [StandardBorelSpace Z] [IsFiniteMeasure σ]
    (hπσ : π.snd = σ.fst) :
    ∃ ζ : Measure (X × Z), ζ.fst = π.fst ∧ ζ.snd = σ.snd :=
  exists_comp_of_exists_glue (exists_glue_of_standardBorel_right π σ hπσ)

/-- Two plans sharing a middle marginal compose to a plan with the two outer marginals, when the
first space is standard Borel. -/
theorem exists_comp_of_standardBorel_left [StandardBorelSpace X] [IsFiniteMeasure π]
    (hπσ : π.snd = σ.fst) :
    ∃ ζ : Measure (X × Z), ζ.fst = π.fst ∧ ζ.snd = σ.snd :=
  exists_comp_of_exists_glue (exists_glue_of_standardBorel_left π σ hπσ)

end Comp

end Measure

end TauCeti
