/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- Public: `ConditionallyIID` and `Contractable` appear in the exported statement.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
-- Non-public: the prefix factorization and directing measure, the joint-rectangle common ending,
-- the path-law transfer, and the machinery the symmetry transport runs on.
-- Public: `directingProbabilityMeasure` names the witness in the exported statement.
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
import TauCeti.Probability.DeFinetti.BlockFactorization
import TauCeti.Probability.DeFinetti.ConditionalCommonEnding
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Sigma
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import TauCeti.Probability.Exchangeability.MixedIID.Implications
-- Non-public: supplies `MeasurableSingletonClass (ProbabilityMeasure α)`, which the
-- exchangeable-σ-algebra fixed-function lemma needs to apply to the directing measure.
import TauCeti.MeasureTheory.Measure.FiniteMeasure

/-!
# The conditional summit from contractability

A contractable process valued in a nonempty standard Borel space is **conditionally i.i.d.**: there
is a directing measure given which every finite distinct block is i.i.d., as a joint-law
disintegration.

## Main results

* `conditionallyIIDWith_of_contractable_pathSpace` — the summit on path space, at the canonical
  directing measure. `DeFinetti/Theorem.lean` derives the sample-space form from it.

## Implementation

The predicate `ConditionallyIIDWith` asks for a joint-law identity, so the block identities of the
mixture route are not enough: the directing measure must survive alongside the block. Three layers
supply that, all private.

**The set-integral identity.** The mass on the tail event `ν ⁻¹' S` meeting a *prefix* block
cylinder is the integral of the directing-measure product over that event. Since `ν` is
`tailProcess`-measurable, `ν ⁻¹' S` is a tail event, so `setIntegral_condExp` may be tested against
it and the prefix factorization replaces the conditional expectation. All real/`ℝ≥0∞` conversion is
confined here.

**Symmetry transport.** A finitely supported permutation realising an injective selection on the
initial segment carries the prefix identity to that selection. It fixes `ν`, because tail events lie
in the exchangeable σ-algebra, and it preserves the measure, because contractability gives
exchangeability — so the directing-measure event rides along untouched. This needs no sorting of the
selection: the permutation realises arbitrary injective selections directly.

**Path space.** Both of the above run on `ℕ → α`, which is standard Borel whenever `α` is. That is
what keeps `[StandardBorelSpace Ω]` out of the exported statement:
`conditionallyIID_of_conditionallyIID_pathLaw` carries the conclusion back to an arbitrary sample
space.

The joint rectangles are then fed to `conditionallyIID_of_jointRectangles`.

This advances `TauCetiRoadmap/Exchangeability/README.md`, **Layer 6** — the conditional summit.

## Sources

The mathematical theorem is Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005),
Theorem 1.1, in its conditional form.

The joint-law upgrade formalized here is **new to this development**. `cameronfreer/exchangeability`
proves a `conditionallyIID_bind_of_contractable`, but under that repository's legacy naming
`ConditionallyIID` denotes the *mixture* identity — what TauCeti calls `MixedIID` — so it
establishes a strictly weaker statement, already available here as `mixedIID_of_contractable`. The
directing-measure joint-rectangle factorization and its symmetry transport were built from TauCeti's
own tail-factorization and exchangeable-σ-algebra API; no material is adapted.
-/
public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Core set-integral identity.** The mass on the tail event `ν ⁻¹' S` intersected with a prefix
block cylinder is the integral of the directing-measure product over that event.

All real/`ℝ≥0∞` conversion for the joint-rectangle argument is confined here: the tail event is
`tailProcess X`-measurable, so `setIntegral_condExp` may be tested against it, and the prefix
factorization then replaces the conditional expectation. -/
private theorem measure_inter_blockCylinder_eq_setLIntegral
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    μ ((directingProbabilityMeasure μ X ⁻¹' S)
        ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B)
      = ∫⁻ ω in directingProbabilityMeasure μ X ⁻¹' S,
          ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  classical
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  haveI : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set A : Set Ω := directingProbabilityMeasure μ X ⁻¹' S with hA_def
  have hA_tail : MeasurableSet[tailProcess X] A :=
    measurable_tailProcess_directingProbabilityMeasure hS
  have hA : MeasurableSet A := hTail _ hA_tail
  set g : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (B i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hB i)).ennreal_toReal
  have hg_nonneg : ∀ ω, 0 ≤ g ω := fun ω =>
    Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  have hg_bound : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_of_nonneg (hg_nonneg ω)]
    refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hg_int : Integrable g μ :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ hg_bound)
  have hind_int : Integrable (blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B) μ :=
    integrable_blockIndicatorProd (fun i => (hX_meas _).aemeasurable) hB
  -- the conditional factorization, tested against the tail event `A`
  have hchain : ∫ ω in A, blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B ω ∂μ
      = ∫ ω in A, g ω ∂μ := by
    rw [← setIntegral_condExp hTail hind_int hA_tail]
    refine setIntegral_congr_ae hA ?_
    filter_upwards
      [condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure hX hX_meas hB] with ω hω _
    exact hω
  -- the left side is the real mass of the intersection
  have hleft : ∫ ω in A, blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B ω ∂μ
      = μ.real (A ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B) := by
    rw [blockIndicatorProd_eq_indicator,
      setIntegral_indicator (measurableSet_blockCylinder
        (fun i => hX_meas _) hB), setIntegral_const, Set.inter_comm]
    simp [measureReal_def]
  have hne : μ (A ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B) ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, ← hleft, hchain,
    ofReal_integral_eq_lintegral_ofReal (hg_int.restrict) (ae_of_all _ hg_nonneg)]
  refine setLIntegral_congr_fun hA (fun ω _ => ?_)
  simp only [hg, measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **Symmetry transport.** On path space the core identity holds for every *injective* selection,
not just the prefix.

A finitely supported permutation realising `k` on the initial segment pulls the prefix
cylinder back to the `k`-cylinder. The directing measure is `pathTail`-measurable, hence
measurable for the exchangeable σ-algebra, hence fixed by that reindexing, so the
directing-measure event is pulled back to itself. Contractability gives exchangeability,
under which the reindexing preserves the measure, and the prefix case applies. -/
private theorem measure_inter_blockCylinder_eq_setLIntegral_of_injective
    [StandardBorelSpace α] [Nonempty α] {μ : Measure (ℕ → α)} [IsFiniteMeasure μ]
    (hX : Contractable μ fun j (x : ℕ → α) => x j)
    {m : ℕ} {k : Fin m → ℕ} (hk : Function.Injective k)
    {B : Fin m → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    μ ((directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = ∫⁻ ω in directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S,
          ∏ i, directingMeasure μ (fun j (x : ℕ → α) => x j) ω (B i) ∂μ := by
  classical
  have hY_meas : ∀ j, Measurable (fun x : ℕ → α => x j) := fun j => measurable_pi_apply j
  obtain ⟨π, hπfin, hπval⟩ := Equiv.Perm.exists_finite_compl_fixedBy_apply_eq
    (⟨Fin.val, Fin.val_injective⟩ : Fin m ↪ ℕ) ⟨k, hk⟩
  simp only [Function.Embedding.coeFn_mk] at hπval
  have hνex : Measurable[exchangeableSigma α]
      (directingProbabilityMeasure μ fun j (x : ℕ → α) => x j) :=
    measurable_tailProcess_directingProbabilityMeasure.mono tail_le_exchangeableSigma le_rfl
  have hνfix : (directingProbabilityMeasure μ fun j (x : ℕ → α) => x j) ∘ permReindex π
      = directingProbabilityMeasure μ fun j (x : ℕ → α) => x j :=
    comp_permReindex_eq_of_measurable_exchangeableSigma hνex hπfin
  have hSfix : permReindex π ⁻¹'
      (directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
      = directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S := by
    rw [← Set.preimage_comp, hνfix]
  have hcyl : blockCylinder (fun j (x : ℕ → α) => x j) k B
      = permReindex π ⁻¹' blockCylinder (fun j (x : ℕ → α) => x j)
          (fun i : Fin m => (i : ℕ)) B := by
    ext x
    simp only [Set.mem_preimage, mem_blockCylinder, permReindex]
    exact forall_congr' fun i => by rw [hπval i]
  have hexch : ExchangeableLaw μ := by
    have hpl : pathLaw μ (fun j (x : ℕ → α) => x j) = μ := by
      rw [pathLaw_def]; exact Measure.map_id
    have hE : Exchangeable μ fun j (x : ℕ → α) => x j :=
      (mixedIID_of_contractable hX hY_meas).exchangeable
    exact hpl ▸ (exchangeable_iff_exchangeableLaw_pathLaw
      (fun j => (hY_meas j).aemeasurable)).1 hE
  have hmp : MeasurePreserving (permReindex (α := α) π) μ μ :=
    hexch.measurePreserving_permReindex π
  have hmeas : MeasurableSet
      ((directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin m => (i : ℕ)) B) :=
    (measurable_directingProbabilityMeasure (μ := μ)
        (tailProcess_le_ambient 0 fun j _ => hY_meas j) hS).inter
      (measurableSet_blockCylinder (fun i => hY_meas _) hB)
  calc μ ((directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = μ (permReindex π ⁻¹'
          ((directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
            ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin m => (i : ℕ)) B)) := by
        rw [Set.preimage_inter, hSfix, ← hcyl]
    _ = μ ((directingProbabilityMeasure μ (fun j (x : ℕ → α) => x j) ⁻¹' S)
          ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin m => (i : ℕ)) B) :=
        hmp.measure_preimage hmeas.nullMeasurableSet
    _ = _ := measure_inter_blockCylinder_eq_setLIntegral hX hY_meas hB hS

/-- **Joint-rectangle reduction.** Given the core set-integral identity for a selection `k`, the
joint law of the directing measure with that block agrees with the disintegration on rectangles
`S ×ˢ ∏ i, B i`.

The reduction is independent of `k`: the disintegration side never mentions it. -/
private theorem jointRectangle_of_measure_inter
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {k : Fin r → ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S)
    (hcore : μ ((directingProbabilityMeasure μ X ⁻¹' S) ∩ blockCylinder X k B)
      = ∫⁻ ω in directingProbabilityMeasure μ X ⁻¹' S,
          ∏ i, directingMeasure μ X ω (B i) ∂μ) :
    (μ.map fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X (k i) ω))
        (S ×ˢ Set.univ.pi B)
      = (μ.bind fun ω =>
          (Measure.dirac (directingProbabilityMeasure μ X ω)).prod
            (ProbabilityMeasure.pi fun _ : Fin r =>
              directingProbabilityMeasure μ X ω).toMeasure)
        (S ×ˢ Set.univ.pi B) := by
  classical
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  have hν : Measurable (directingProbabilityMeasure μ X) :=
    measurable_directingProbabilityMeasure hTail
  have hjoint : Measurable fun ω =>
      (directingProbabilityMeasure μ X ω, fun i : Fin r => X (k i) ω) :=
    hν.prodMk (measurable_pi_lambda _ fun i => hX_meas _)
  have hker : Measurable fun ω =>
      (Measure.dirac (directingProbabilityMeasure μ X ω)).prod
        (ProbabilityMeasure.pi fun _ : Fin r => directingProbabilityMeasure μ X ω).toMeasure :=
    TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure _ hν
  have hrect : MeasurableSet (S ×ˢ Set.univ.pi B) :=
    hS.prod (MeasurableSet.univ_pi hB)
  -- the joint law's mass is the mass of the tail event meeting the block cylinder
  have hpre : (fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X (k i) ω))
        ⁻¹' (S ×ˢ Set.univ.pi B)
      = (directingProbabilityMeasure μ X ⁻¹' S) ∩ blockCylinder X k B := by
    ext ω
    simp [Set.mem_prod, mem_blockCylinder, Set.mem_pi]
  rw [Measure.map_apply hjoint hrect, hpre, hcore,
    Measure.bind_apply hrect hker.aemeasurable]
  -- the mixture side splits as a Dirac indicator times the product measure
  rw [← lintegral_indicator (hν hS)]
  refine lintegral_congr fun ω => ?_
  have hprod : (ProbabilityMeasure.pi fun _ : Fin r => directingProbabilityMeasure μ X ω).toMeasure
      (Set.univ.pi B) = ∏ i, directingMeasure μ X ω (B i) := by
    rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => by rw [directingProbabilityMeasure_toMeasure]
  rw [Measure.prod_prod, Measure.dirac_apply' _ hS, hprod]
  by_cases hω : directingProbabilityMeasure μ X ω ∈ S
  · simp [Set.indicator_of_mem, hω, Set.mem_preimage]
  · simp [Set.indicator_of_notMem, hω, Set.mem_preimage]

/-- **The conditional summit on path space, at the canonical directing measure.** A contractable
coordinate process on a standard Borel state space is conditionally i.i.d. **with** witness the tail
conditional law `directingProbabilityMeasure`.

Stated at the named witness rather than existentially: the directing measure is the object the
conditional predicate is about, so discarding it would lose the identity downstream users need. -/
theorem conditionallyIIDWith_of_contractable_pathSpace
    [StandardBorelSpace α] [Nonempty α] {μ : Measure (ℕ → α)} [IsFiniteMeasure μ]
    (hX : Contractable μ fun j (x : ℕ → α) => x j) :
    ConditionallyIIDWith μ (fun j (x : ℕ → α) => x j)
      (directingProbabilityMeasure μ fun j (x : ℕ → α) => x j) := by
  have hY_meas : ∀ j, Measurable (fun x : ℕ → α => x j) := fun j => measurable_pi_apply j
  refine conditionallyIID_of_jointRectangles
    (measurable_directingProbabilityMeasure (μ := μ)
      (tailProcess_le_ambient 0 fun j _ => hY_meas j))
    fun m sel hsel S hS B hB => ?_
  exact jointRectangle_of_measure_inter hY_meas hB hS
    (measure_inter_blockCylinder_eq_setLIntegral_of_injective hX hsel hB hS)

end Probability

end TauCeti
