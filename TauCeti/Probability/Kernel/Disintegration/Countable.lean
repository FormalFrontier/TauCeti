/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Disintegrating a measure over a countable coordinate

A measure `σ` on a product `Y × Z` disintegrates over `Y` when it is the composition-product
`σ.fst ⊗ₘ κ` of its first marginal with a Markov kernel `κ : Kernel Y Z`. Mathlib supplies such a
kernel when the *second* factor `Z` is standard Borel
(`MeasureTheory.Measure.condKernel`). For a finite `σ`, this file supplies one in the complementary
regime: when the *first* factor `Y` is countable with measurable singletons, and `Z` is any
nonempty measurable space.

On a countable `Y` no analytic input is needed — the disintegration is the elementary formula
`κ y s = (σ.fst {y})⁻¹ * σ ({y} ×ˢ s)`, conditioning on the atom `{y}`. The one point that needs
care is the atoms of zero mass, where that formula reads `∞ * 0` and carries no information: they
are given a default value, and the disintegration still holds there because such an atom carries
no `σ`-mass to begin with (`measure_singleton_prod_eq_zero_of_fst_eq_zero`).

## Main definitions

* `TauCeti.MeasureTheory.countableCondKernel` — the conditional kernel of a finite measure on
  `Y × Z` over a countable `Y`.

## Main results

* `TauCeti.MeasureTheory.measure_singleton_prod_eq_zero_of_fst_eq_zero` — an atom of zero
  first-marginal
  mass carries no mass at all: the fact that makes the default value at such an atom harmless;
* `TauCeti.MeasureTheory.countableCondKernel_apply`,
  `TauCeti.MeasureTheory.countableCondKernel_apply_of_ne_zero` and
  `TauCeti.MeasureTheory.countableCondKernel_apply_of_eq_zero` — the eliminator and the two
  branches of the construction, made explicit;
* `TauCeti.MeasureTheory.compProd_countableCondKernel` — **the disintegration**,
  `σ.fst ⊗ₘ countableCondKernel σ = σ`, registered as a
  `MeasureTheory.Measure.IsCondKernel` instance;
* `TauCeti.MeasureTheory.eq_countableCondKernel_of_ne_zero` — every conditional kernel of `σ`
  agrees with this one at every atom of positive mass;

The file also contains two private regression examples showing that the contract cannot be
strengthened and that its finiteness hypothesis cannot be dropped.

## Implementation notes

The kernel is built with `ProbabilityTheory.Kernel.ofFunOfCountable`, which upgrades an arbitrary
function on a countable space with measurable singletons to a kernel; the measurability of the
disintegration, the only nontrivial requirement in the standard Borel setting, is free here.

The value at an atom of zero mass is a Dirac measure at `Classical.arbitrary Z`, hence the
`[Nonempty Z]` hypothesis. Some choice is forced: a Markov kernel must return a probability
measure at every point of `Y`, `σ` prescribes none at a null atom, and on an empty `Z` no Markov
kernel exists at all, by `ProbabilityTheory.Kernel.eq_zero_of_isEmpty_right` together with
`ProbabilityTheory.Kernel.not_isMarkovKernel_zero`. The choice is deliberately *not* hidden —
`countableCondKernel_apply_of_eq_zero` names it. A private regression below exhibits two
conditional kernels of one measure that differ at a null atom, so no strengthening of
`eq_countableCondKernel_of_ne_zero` to all atoms is available.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, the design-validation milestone preceding
  the arbitrary-carrier triangle inequality of Layer 1 — "finite coupling gluing with zero-mass
  middle atoms explicit". This file is the disintegration half of that gluing; the gluing itself
  is `TauCeti.MeasureTheory.exists_glue_of_countable_middle`.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5 and its finite reduction.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

section Slices

variable [MeasurableSingletonClass Y]

/-- An atom of `Y` whose first-marginal mass vanishes carries no mass in any slice.

This is the fact that makes the default value of `countableCondKernel` at a null atom harmless:
such an atom contributes nothing to the disintegration, whatever the kernel does there. -/
theorem measure_singleton_prod_eq_zero_of_fst_eq_zero (σ : Measure (Y × Z)) {y : Y}
    (hy : σ.fst {y} = 0) (s : Set Z) : σ ({y} ×ˢ s) = 0 := by
  have huniv : σ (({y} : Set Y) ×ˢ (Set.univ : Set Z)) = 0 := by
    rw [Set.prod_univ, ← Measure.fst_apply (measurableSet_singleton y)]
    exact hy
  exact measure_mono_null (Set.prod_mono subset_rfl (Set.subset_univ s)) huniv

end Slices

section CondKernel

variable [Countable Y] [MeasurableSingletonClass Y] [Nonempty Z]

/-- The **countable-coordinate kernel construction** for a measure `σ` on `Y × Z`. When `σ` is
finite, this is its conditional kernel over the first coordinate.

At an atom `y` of positive first-marginal mass this is the normalised slice
`s ↦ (σ.fst {y})⁻¹ * σ ({y} ×ˢ s)`; at a null atom, where `σ` prescribes nothing, it is a Dirac
measure. Unlike `MeasureTheory.Measure.condKernel`, this needs no standard-Borel or other
regularity hypothesis on the nonempty second factor `Z`. -/
def countableCondKernel (σ : Measure (Y × Z)) : Kernel Y Z :=
  Kernel.ofFunOfCountable fun y =>
    if σ.fst {y} = 0 then Measure.dirac (Classical.arbitrary Z)
    else ((σ.fst {y})⁻¹ • σ).comap (Prod.mk y)

/-- The two branches of `countableCondKernel`, before either is evaluated. The pair of branch
lemmas below is the interface to prefer; neither of those mentions the `if`. -/
theorem countableCondKernel_apply (σ : Measure (Y × Z)) (y : Y) :
    countableCondKernel σ y =
      if σ.fst {y} = 0 then Measure.dirac (Classical.arbitrary Z)
      else ((σ.fst {y})⁻¹ • σ).comap (Prod.mk y) := (rfl)

/-- At a null atom the conditional kernel takes its default value. It is a genuine choice, not a
quantity read off `σ`; see the private uniqueness regression below. -/
@[simp] theorem countableCondKernel_apply_of_eq_zero {σ : Measure (Y × Z)} {y : Y}
    (hy : σ.fst {y} = 0) : countableCondKernel σ y = Measure.dirac (Classical.arbitrary Z) := by
  simp [countableCondKernel_apply, hy]

/-- At an atom of positive mass the conditional kernel is the normalised slice. -/
@[simp] theorem countableCondKernel_apply_of_ne_zero {σ : Measure (Y × Z)} {y : Y}
    (hy : σ.fst {y} ≠ 0) (s : Set Z) :
    countableCondKernel σ y s = (σ.fst {y})⁻¹ * σ ({y} ×ˢ s) := by
  rw [countableCondKernel_apply, ite_eq_right_of_eq_false _ _ (eq_false hy),
    (measurableEmbedding_prodMk_left y).comap_apply, Measure.smul_apply, Set.singleton_prod,
    smul_eq_mul]

instance instIsMarkovKernelCountableCondKernel (σ : Measure (Y × Z)) [IsFiniteMeasure σ] :
    IsMarkovKernel (countableCondKernel σ) := by
  refine ⟨fun y => ?_⟩
  by_cases hy : σ.fst {y} = 0
  · rw [countableCondKernel_apply_of_eq_zero hy]
    infer_instance
  · refine ⟨?_⟩
    rw [countableCondKernel_apply_of_ne_zero hy, Set.prod_univ,
      ← Measure.fst_apply (measurableSet_singleton y),
      ENNReal.inv_mul_cancel hy (measure_ne_top _ _)]

/-- **The disintegration of a measure over a countable coordinate.** -/
@[simp] theorem compProd_countableCondKernel (σ : Measure (Y × Z)) [IsFiniteMeasure σ] :
    σ.fst ⊗ₘ countableCondKernel σ = σ := by
  ext s hs
  -- The atomic decomposition `σ s = ∑' y, σ ({y} ×ˢ (Prod.mk y ⁻¹' s))` is the fibre sum of
  -- `σ.restrict s` along `Prod.fst`.
  have hslice : ∀ y : Y,
      σ.restrict s (Prod.fst ⁻¹' {y}) = σ (({y} : Set Y) ×ˢ (Prod.mk y ⁻¹' s)) := fun y => by
    rw [Measure.restrict_apply (measurable_fst (measurableSet_singleton y))]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
    constructor
    · rintro ⟨rfl, hp⟩
      exact ⟨rfl, hp⟩
    · rintro ⟨rfl, hp⟩
      exact ⟨rfl, hp⟩
  have hdecomp : σ s = ∑' y : Y, σ (({y} : Set Y) ×ˢ (Prod.mk y ⁻¹' s)) := by
    have h := _root_.MeasureTheory.tsum_measure_preimage_singleton (μ := σ.restrict s)
      (Set.countable_univ (α := Y)) (f := Prod.fst)
      fun y _ => measurable_fst (measurableSet_singleton y)
    rw [tsum_subtype Set.univ fun y => σ.restrict s (Prod.fst ⁻¹' {y}), Set.indicator_univ,
      Set.preimage_univ, Measure.restrict_apply_univ] at h
    rw [← h]
    exact tsum_congr hslice
  rw [Measure.compProd_apply hs, lintegral_countable', hdecomp]
  refine tsum_congr fun y => ?_
  by_cases hy : σ.fst {y} = 0
  · rw [hy, mul_zero, measure_singleton_prod_eq_zero_of_fst_eq_zero σ hy]
  · rw [countableCondKernel_apply_of_ne_zero hy, mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel hy (measure_ne_top _ _), one_mul]

instance instIsCondKernelCountableCondKernel (σ : Measure (Y × Z)) [IsFiniteMeasure σ] :
    σ.IsCondKernel (countableCondKernel σ) where
  disintegrate := compProd_countableCondKernel σ

/-- Any conditional kernel of `σ` agrees with `countableCondKernel σ` at every atom of positive
mass. The restriction to such atoms is sharp, as shown by the first private regression below;
global finiteness is necessary at infinite-mass atoms, as shown by the second. -/
theorem eq_countableCondKernel_of_ne_zero (σ : Measure (Y × Z)) [IsFiniteMeasure σ]
    (κ : Kernel Y Z) [σ.IsCondKernel κ] {y : Y} (hy : σ.fst {y} ≠ 0) :
    κ y = countableCondKernel σ y :=
  Measure.ext fun s _ => by
    rw [Measure.IsCondKernel.apply_of_ne_zero σ κ hy s, countableCondKernel_apply_of_ne_zero hy]

end CondKernel

section Regressions

/-! ### Regressions

Two examples that break the contract of `countableCondKernel` if it is read more strongly than it
is stated. The first shows the conclusion of `eq_countableCondKernel_of_ne_zero` cannot be
extended to null atoms; the second shows that `IsFiniteMeasure σ` cannot be dropped. (That
`Nonempty Z` cannot be dropped either is immediate from Mathlib:
`ProbabilityTheory.Kernel.eq_zero_of_isEmpty_right` and
`ProbabilityTheory.Kernel.not_isMarkovKernel_zero` leave no Markov kernel at all on an empty
target.) -/

/-- **Uniqueness genuinely fails at a null atom.** The Dirac measure at `(true, true)` on
`Bool × Bool` gives the atom `false` no mass, and the two kernels below both disintegrate it while
differing there. Thus a conditional kernel is always pinned down on atoms of positive mass, while
uniqueness can fail at null atoms; the default value `countableCondKernel` uses there is a choice,
not a derived quantity. -/
private theorem exists_isCondKernel_pair_ne :
    ∃ κ₁ κ₂ : Kernel Bool Bool,
      (Measure.dirac ((true, true) : Bool × Bool)).IsCondKernel κ₁ ∧
      (Measure.dirac ((true, true) : Bool × Bool)).IsCondKernel κ₂ ∧ κ₁ ≠ κ₂ := by
  have hfst : (Measure.dirac ((true, true) : Bool × Bool)).fst = Measure.dirac true := by
    rw [Measure.fst, Measure.map_dirac' measurable_fst]
  -- Only the atom `true` carries mass, so any Markov kernel taking the value `dirac true` there
  -- disintegrates the measure, whatever it does at `false`.
  have key : ∀ κ : Kernel Bool Bool, IsMarkovKernel κ → κ true = Measure.dirac true →
      (Measure.dirac ((true, true) : Bool × Bool)).fst ⊗ₘ κ
        = Measure.dirac ((true, true) : Bool × Bool) := by
    intro κ _ hκ
    ext s hs
    rw [hfst, Measure.dirac_compProd_apply hs, hκ,
      Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left),
      Measure.dirac_apply' _ hs]
    rfl
  refine ⟨Kernel.const Bool (Measure.dirac true), Kernel.deterministic id measurable_id,
    ⟨key _ inferInstance (Kernel.const_apply _ _)⟩,
    ⟨key _ inferInstance (Kernel.deterministic_apply measurable_id true)⟩, ?_⟩
  intro h
  have hfalse := congrArg (fun κ : Kernel Bool Bool => κ false {true}) h
  simp [Kernel.const_apply, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton true)] at hfalse

/-- **`IsFiniteMeasure σ` cannot be dropped.** At an atom of infinite mass the normalising factor
`(σ.fst {y})⁻¹` is `0`, so the conditional kernel collapses to the zero measure and the
composition-product loses all the mass it was meant to recover. -/
private theorem exists_compProd_countableCondKernel_ne :
    ∃ σ : Measure (Unit × Unit), σ.fst ⊗ₘ countableCondKernel σ ≠ σ := by
  refine ⟨(⊤ : ℝ≥0∞) • Measure.dirac ((), ()), ?_⟩
  set σ : Measure (Unit × Unit) := (⊤ : ℝ≥0∞) • Measure.dirac ((), ()) with hσ
  have hfst : σ.fst {()} = ⊤ := by
    rw [hσ, Measure.fst, Measure.map_smul, Measure.map_dirac' measurable_fst]
    simp
  have hzero : countableCondKernel σ = 0 := by
    ext y s
    rw [countableCondKernel_apply_of_ne_zero (by rw [Subsingleton.elim y (), hfst]; simp)]
    rw [Subsingleton.elim y (), hfst]
    simp
  have hne : σ ≠ 0 := by
    intro h
    rw [h] at hfst
    simp at hfst
  rw [hzero]
  simpa using fun h => hne h.symm

end Regressions

end MeasureTheory

end TauCeti
