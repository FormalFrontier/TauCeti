/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.DirectingMeasure.Coord
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.MixedIID.Basic
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
-- Non-public: used only inside proofs — the tail factorization
-- `condExp_blockIndicatorProd_tailProcess_ae_eq_prod`, the path-law transfer and contractability
-- bridges, and `Tuple.sort` (the injective-selection reduction).
import TauCeti.Probability.DeFinetti.TailFactorization
import TauCeti.Probability.Exchangeability.MixedIID.Map
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Block-product factorisation and the de Finetti summit

The block-product factorisation of the conditional expectation, and — built directly on it — the
de Finetti summit for the reverse-martingale route.

Given that the selected coordinates of a contractable process are conditionally independent over the
tail σ-algebra, the conditional expectation of a block-indicator product factors as a product of the
directing measure on the coordinate sets:
```
μ[blockIndicatorProd X k C | tailProcess X] =ᵐ fun ω => ∏ i, (directingMeasure μ X ω).real (C i).
```
This chains Mathlib's `iCondIndepFun_iff_condExp_inter_preimage_eq_mul` (conditional independence ⟺
product of indicator conditional expectations) with
`Contractable.directingMeasure_ae_eq_condExp_coord` (each coordinate's conditional law is the
directing measure). The tail factorization
`condExp_blockIndicatorProd_tailProcess_ae_eq_prod` (from `TailFactorization`) then discharges the
finite-block rectangle identity for `directingProbabilityMeasure μ X`, exactly what
`mixedIIDWith_of_forall_rectangles` consumes — so the whole chain assembles here.

## Main results

* `condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure` — the prefix block factorization
  at the directing measure, the base case rectangle identities over a contractable process reduce
  to.
* `mixedIIDWith_of_contractable` — a contractable process on a standard Borel sample space
  is mixed i.i.d., with `directingProbabilityMeasure μ X` (the tail conditional law) as the
  witness. That witness is the canonical *directing measure*, not merely a mixing representative;
  what this file proves about it is the mixture identity. The sharper conditional statement at the
  same witness is `conditionallyIIDWith_of_contractable_pathSpace` in
  `TauCeti.Probability.DeFinetti.JointRectangle`.
* `mixedIID_of_contractable` — the existential form, for a contractable process on an
  arbitrary measurable sample space (state space still standard Borel).
* `mixedIID_of_exchangeable` — the exchangeable form (via `contractable_of_exchangeable`).

The `..._of_iCondIndepFun_tailProcess` theorems expose the intermediate reduction (de Finetti given
tail conditional independence of the coordinates). All of the rectangle-mixture staging lemmas and
the standard-Borel-`Ω` existential are `private` (proof staging).

The reverse-martingale ("third") proof follows Kallenberg, *Probabilistic Symmetries and Invariance
Principles*, Theorem 1.1 (pp. 26–28). Adapted from `cameronfreer/exchangeability`
(`DeFinetti/ViaMartingale/CommonEnding.lean` and `DeFinetti/TheoremViaMartingale.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`); here the factorisation is obtained by reuse of
Mathlib's `iCondIndepFun` characterisation rather than a hand-rolled π-system.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- **Block-product factorisation of the conditional expectation** (given tail conditional
independence). If the selected coordinates `fun i => X (k i)` are conditionally independent given
the tail, then the conditional expectation of the block-indicator product factors as
`∏ i, (directingMeasure μ X ·).real (C i)`. -/
theorem condExp_blockIndicatorProd_ae_eq_prod_of_iCondIndepFun_tailProcess
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hCI : iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
      (tailProcess X) (tailProcess_le_ambient 0 fun j _ => hX_meas j) (fun i => X (k i)) μ) :
    μ[blockIndicatorProd X k C | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (directingMeasure μ X ω).real (C i) := by
  -- The CI factorisation on the full selection `S = univ`, sets `C`.
  have hfac := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (fun _ : Fin m => (inferInstance : MeasurableSpace α)) (fun i => X (k i))
    (fun i => hX_meas (k i))).1 hCI Finset.univ (sets := C) (fun i _ => hC i)
  -- The intersection over the selection is the block cylinder.
  have hcyl : ⋂ i ∈ (Finset.univ : Finset (Fin m)), X (k i) ⁻¹' C i = blockCylinder X k C := by
    ext ω; simp [mem_blockCylinder, Set.mem_iInter, Set.mem_preimage]
  rw [hcyl] at hfac
  -- Goal LHS = `μ⟦blockCylinder X k C | tail⟧`, the block-indicator conditional expectation.
  rw [blockIndicatorProd_eq_indicator]
  refine hfac.trans ?_
  -- Each factor is the directing measure on `C i`, by the per-coordinate conditional law (brick A).
  have hfactor : ∀ i, (μ⟦X (k i) ⁻¹' C i | tailProcess X⟧)
      =ᵐ[μ] fun ω => (directingMeasure μ X ω).real (C i) := by
    intro i
    have hind : (X (k i) ⁻¹' C i).indicator (fun ω => (1 : ℝ))
        = Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X (k i) := by
      funext ω; by_cases h : X (k i) ω ∈ C i <;> simp [Set.indicator, Set.mem_preimage, h]
    rw [hind]
    exact (hX.directingMeasure_ae_eq_condExp_coord hX_meas (k i) (hC i)).symm
  have key : ∀ᵐ ω ∂μ, ∀ i, (μ⟦X (k i) ⁻¹' C i | tailProcess X⟧) ω
      = (directingMeasure μ X ω).real (C i) := ae_all_iff.mpr hfactor
  filter_upwards [key] with ω hω
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun i _ => hω i

/-- **Block law of a rectangle as a directing-measure mixture.** If the tail conditional expectation
of the block-indicator product is a.e. the directing-measure product
`∏ i, (directingMeasure μ X ω).real (C i)`, then the block law of the rectangle `∏ᵢ C i` is the
`μ`-average `∫⁻ ∏ᵢ (directingMeasure μ X ω) (C i)` of that product. -/
private theorem blockLaw_eq_lintegral_prod_directingMeasure_of_condExp_ae_eq
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hfac : μ[blockIndicatorProd X k C | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (directingMeasure μ X ω).real (C i)) :
    blockLaw μ X k (Set.univ.pi C) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (C i) ∂μ := by
  classical
  have hTail : tailProcess X ≤ mΩ := tailProcess_le_ambient 0 fun j _ => hX_meas j
  haveI : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set g : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (C i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hC i)).ennreal_toReal
  have hg_bound : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    have hval : g ω = ∏ i, ((directingMeasure μ X ω) (C i)).toReal := by
      simp only [hg, measureReal_def]
    rw [hval, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
    refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hg_int : Integrable g μ :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ hg_bound)
  have hbl : (blockLaw μ X k (Set.univ.pi C)).toReal = ∫ ω, g ω ∂μ := by
    rw [← integral_blockIndicatorProd (fun i => (hX_meas (k i)).aemeasurable) hC,
      ← integral_condExp hTail]
    exact integral_congr_ae hfac
  have hbl_ne : blockLaw μ X k (Set.univ.pi C) ≠ ⊤ := by
    rw [blockLaw_blockCylinder X (fun i => (hX_meas (k i)).aemeasurable) hC]
    exact measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hbl_ne, hbl,
    ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ fun ω =>
      Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  simp only [hg, measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **Block law of a rectangle as a directing-measure mixture** (given tail conditional
independence). The block law of the rectangle `∏ᵢ C i` is the `μ`-average of the directing-measure
product `∏ i, directingMeasure μ X ω (C i)`. -/
theorem blockLaw_eq_lintegral_prod_directingMeasure_of_iCondIndepFun_tailProcess
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} {C : Fin m → Set α} (hC : ∀ i, MeasurableSet (C i))
    (hCI : iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
      (tailProcess X) (tailProcess_le_ambient 0 fun j _ => hX_meas j) (fun i => X (k i)) μ) :
    blockLaw μ X k (Set.univ.pi C) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (C i) ∂μ :=
  blockLaw_eq_lintegral_prod_directingMeasure_of_condExp_ae_eq hX_meas hC
    (condExp_blockIndicatorProd_ae_eq_prod_of_iCondIndepFun_tailProcess hX hX_meas hC hCI)

/-- **de Finetti reduces to conditional independence over the tail** (directing-measure form). If
every finite injective selection of coordinates of a contractable process is conditionally
independent given the tail σ-algebra, then the process is mixed i.i.d. **with directing
measure** the tail conditional law `directingProbabilityMeasure μ X`. -/
theorem mixedIIDWith_of_iCondIndepFun_tailProcess
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (hCI : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
        (tailProcess X) (tailProcess_le_ambient 0 fun j _ => hX_meas j) (fun i => X (k i)) μ) :
    MixedIIDWith μ X (directingProbabilityMeasure μ X) := by
  have hTail : tailProcess X ≤ mΩ := tailProcess_le_ambient 0 fun j _ => hX_meas j
  refine mixedIIDWith_of_forall_rectangles
    (measurable_directingProbabilityMeasure (μ := μ) hTail) ?_
  intro m k hk B hB
  rw [blockLaw_eq_lintegral_prod_directingMeasure_of_iCondIndepFun_tailProcess
    hX hX_meas hB (hCI m k hk)]
  refine lintegral_congr fun ω => ?_
  simp only [directingProbabilityMeasure_toMeasure]

/-- **de Finetti reduces to conditional independence over the tail.** The existential form of
`mixedIIDWith_of_iCondIndepFun_tailProcess`: under the same tail conditional-independence
hypothesis, a contractable process is `MixedIID`. -/
theorem mixedIID_of_iCondIndepFun_tailProcess
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (hCI : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      iCondIndepFun (m := fun _ : Fin m => (inferInstance : MeasurableSpace α))
        (tailProcess X) (tailProcess_le_ambient 0 fun j _ => hX_meas j) (fun i => X (k i)) μ) :
    MixedIID μ X :=
  MixedIID.of_mixingRepresentative
    (mixedIIDWith_of_iCondIndepFun_tailProcess hX hX_meas hCI)

/-- **Prefix block factorization at the directing measure.** For a contractable process, the
conditional expectation of the length-`r` prefix indicator product given the tail σ-algebra
`tailProcess X` is a.e. the product of directing-measure evaluations
`∏ i, (directingMeasure μ X ω).real (C i)` on the coordinate sets.

This is the base case for rectangle identities over a contractable process: a finite block of
coordinates is replaced by the directing measure under the tail σ-algebra, and identities for
arbitrary selections reduce to it. -/
theorem condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {C : Fin r → Set α} (hC : ∀ i, MeasurableSet (C i)) :
    μ[blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i : Fin r, (directingMeasure μ X ω).real (C i) := by
  have hfac := condExp_blockIndicatorProd_tailProcess_ae_eq_prod X hX hX_meas r C hC
  have key : ∀ᵐ ω ∂μ, ∀ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] ω
        = (directingMeasure μ X ω).real (C i) :=
    ae_all_iff.mpr fun i => (hX.directingMeasure_ae_eq_condExp_coord hX_meas 0 (hC i)).symm
  filter_upwards [hfac, key] with ω hf hk
  rw [hf]
  exact Finset.prod_congr rfl fun i _ => hk i

/-- **Prefix rectangle mixture (from contractability).** For a contractable process, the block law
of the length-`r` prefix rectangle `∏ᵢ B i` is the `μ`-average
`∫⁻ ∏ᵢ (directingMeasure μ X ω) (B i)` of the directing-measure product. -/
private theorem blockLaw_prefix_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X (fun i : Fin r => (i : ℕ)) (Set.univ.pi B)
      = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ :=
  blockLaw_eq_lintegral_prod_directingMeasure_of_condExp_ae_eq hX_meas hB
    (condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure hX hX_meas hB)

/-- For a contractable process and a strictly increasing selection `k`, the block law of the
rectangle `∏ᵢ B i` is the `μ`-average of the directing-measure product. -/
private theorem blockLaw_strictMono_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k)
    {B : Fin m → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  rw [hX m k hk]
  exact blockLaw_prefix_eq_lintegral_prod_directingMeasure hX hX_meas hB

/-- For a contractable process and any injective (distinct) selection `k`, the block law of the
rectangle `∏ᵢ B i` is the `μ`-average of the directing-measure product. -/
private theorem blockLaw_injective_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} (hk : Function.Injective k)
    {B : Fin m → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  classical
  set e : Equiv.Perm (Fin m) := Tuple.sort k with he
  have hsm : StrictMono (k ∘ e) :=
    (Tuple.monotone_sort k).strictMono_of_injective (hk.comp e.injective)
  have hreindex : blockLaw μ X k (Set.univ.pi B)
      = blockLaw μ X (k ∘ e) (Set.univ.pi fun i => B (e i)) := by
    rw [← map_blockLaw_reindex μ k (e : Fin m → Fin m) (fun j => (hX_meas (k j)).aemeasurable),
      Measure.map_apply (measurable_pi_lambda _ fun i => measurable_pi_apply (e i))
        (MeasurableSet.univ_pi fun i => hB (e i))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i; exact h (e i)
    · intro h j; have hj := h (e.symm j); rwa [e.apply_symm_apply] at hj
  rw [hreindex, blockLaw_strictMono_eq_lintegral_prod_directingMeasure hX hX_meas hsm
    (fun i => hB (e i))]
  refine lintegral_congr fun ω => ?_
  exact Equiv.prod_comp e fun j => directingMeasure μ X ω (B j)

/-- **de Finetti's theorem, directed form.** A contractable process on a
standard Borel space is mixed i.i.d. **with** witness the tail conditional law
`directingProbabilityMeasure μ X`. -/
theorem mixedIIDWith_of_contractable
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    MixedIIDWith μ X (directingProbabilityMeasure μ X) := by
  have hTail : tailProcess X ≤ mΩ := tailProcess_le_ambient 0 fun j _ => hX_meas j
  refine mixedIIDWith_of_forall_rectangles
    (measurable_directingProbabilityMeasure (μ := μ) hTail) ?_
  intro m k hk B hB
  rw [blockLaw_injective_eq_lintegral_prod_directingMeasure hX hX_meas hk hB]
  simp only [directingProbabilityMeasure_toMeasure]

/-- The existential form on a standard Borel sample space (the internal step through which the
general `mixedIID_of_contractable` is transferred). -/
private theorem mixedIID_of_contractable_standardBorelOmega
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    MixedIID μ X :=
  MixedIID.of_mixingRepresentative (mixedIIDWith_of_contractable hX hX_meas)

/-- **de Finetti's theorem, mixture form: contractable ⇒ mixed i.i.d.** A contractable process
valued in a standard Borel space, on an arbitrary measurable sample space, is mixed i.i.d. This is
the roadmap's `mixedIID_of_contractable`; the sharp summit `conditionallyIID_of_contractable`,
which concludes the joint-law disintegration rather than only the mixture identity, is in
`TauCeti.Probability.DeFinetti.Theorem`. -/
theorem mixedIID_of_contractable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    MixedIID μ X := by
  refine mixedIID_of_mixedIID_pathLaw hX_meas ?_
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  exact mixedIID_of_contractable_standardBorelOmega
    (hX.coordinate_pathLaw fun i => (hX_meas i).aemeasurable) measurable_pi_apply

/-- **de Finetti's theorem, mixture form: exchangeable ⇒ mixed i.i.d.** An exchangeable process
valued in a standard Borel space, on an arbitrary measurable sample space, is mixed i.i.d. -/
theorem mixedIID_of_exchangeable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    MixedIID μ X :=
  mixedIID_of_contractable
    (contractable_of_exchangeable hX fun i => (hX_meas i).aemeasurable) hX_meas

end Probability

end TauCeti
