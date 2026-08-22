/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Couplings of two measures

A *coupling*, or *transport plan*, of a measure `μ` on `X` and a measure `ν` on `Y` is a measure
`π` on `X × Y` whose two marginals are `μ` and `ν`. It is the primitive object of optimal
transport: the primal transport problem minimises a cost over the couplings of two fixed
measures, so every statement about that problem is a statement about the set defined here.

Nothing in this file needs a topology, a metric, a density, or a normalisation, and the two
factors may be different measurable spaces. The relation is therefore stated for arbitrary
measures, and the probability case is packaged separately as a subtype of
`MeasureTheory.ProbabilityMeasure (X × Y)`.

## Main definitions

* `TauCeti.IsCoupling π μ ν` — the plan-first coupling relation: `π.fst = μ` and
  `π.snd = ν`;
* `TauCeti.Coupling μ ν` — couplings of two probability measures, bundled as a subtype of
  `MeasureTheory.ProbabilityMeasure (X × Y)`;
* `TauCeti.Coupling.prod` — the independent coupling, and with it
  `TauCeti.Coupling.instNonempty`.

## Main statements

* `TauCeti.IsCoupling.measure_prod_univ` and `TauCeti.IsCoupling.measure_univ_prod` — the
  marginal formulas on measurable cylinders, with the converse
  `TauCeti.isCoupling_of_measure_prod_univ_of_measure_univ_prod`;
* `TauCeti.exists_isCoupling_iff` — a finite measure and any other measure admit a coupling
  exactly when they have the same total mass, the witness being their normalised product;
* `TauCeti.isCoupling_map_swap_iff` and `TauCeti.isCoupling_map_prodMap_iff` —
  invariance of the relation under the coordinate swap and under measurable equivalences of the
  two factors;
* `TauCeti.isCoupling_toMeasure_iff` — the coupling condition on bundled probability measures,
  as the pair of equations for the two marginal pushforwards;
* `TauCeti.IsCoupling.eq_map_prodMk` — a coupling out of a Dirac measure is the
  pushforward of its target along `y ↦ (x, y)`, so it is unique; `IsCoupling.eq_dirac`
  specialises this to a pair of Dirac measures.

## Implementation notes

The argument order `IsCoupling π μ ν` takes the plan first, so that a hypothesis
`hπ : IsCoupling π μ ν` supports dot notation such as `hπ.swap` and `hπ.map`. This convention,
and the choice to state the relation for raw measures rather than only for bundled probability
measures, follow Joseph K. Miller's Apache-2.0 `Vlasov.IsCoupling`
(<https://github.com/Hydrodynamical/Vlasov_Meanfield_Formalization>), the closest existing Lean
development of the same relation; no code is taken from it. The bundled subtype mirrors
`TauCeti.MultiCoupling`, the multi-marginal analogue already in this repository.

The declarations sit in the bare `TauCeti` namespace rather than in `TauCeti.Measure`:
`scripts/lint-dot-notation.py` rejects a new declaration under `TauCeti.<Mathlib type
namespace>` that takes an explicit argument of that type, because `π.IsCoupling μ ν` would not
elaborate there anyway. Dot notation on `hπ` works under either namespace; the bare namespace is
forced by the lint rule and matches `TauCeti.MultiCoupling`.

This is Layer 0, item 1 of the optimal-transport roadmap.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 1
  ("Couplings and changes of variables"), Definition 1.1, which is this relation for two
  probability measures. `TauCeti.IsCoupling` states it for arbitrary measures, so the
  probability case is the bundled `TauCeti.Coupling`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
  {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

/-- `IsCoupling π μ ν` says that the measure `π` on `X × Y` is a coupling, or transport plan,
of `μ` and `ν`: its first marginal is `μ` and its second marginal is `ν`. -/
structure IsCoupling (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) : Prop where
  /-- The first marginal of a coupling is the prescribed source measure. -/
  fst_eq : π.fst = μ
  /-- The second marginal of a coupling is the prescribed target measure. -/
  snd_eq : π.snd = ν

namespace IsCoupling

/-- A coupling gives the measurable cylinder `s ×ˢ univ` the source mass of `s`. -/
theorem measure_prod_univ (hπ : IsCoupling π μ ν) {s : Set X} (hs : MeasurableSet s) :
    π (s ×ˢ univ) = μ s := by
  rw [prod_univ, ← Measure.fst_apply hs, hπ.fst_eq]

/-- A coupling gives the measurable cylinder `univ ×ˢ t` the target mass of `t`. -/
theorem measure_univ_prod (hπ : IsCoupling π μ ν) {t : Set Y} (ht : MeasurableSet t) :
    π (univ ×ˢ t) = ν t := by
  rw [univ_prod, ← Measure.snd_apply ht, hπ.snd_eq]

/-- The source measure of a coupling has the total mass of the coupling. -/
theorem measure_univ_left (hπ : IsCoupling π μ ν) : μ univ = π univ := by
  rw [← hπ.fst_eq, Measure.fst_univ]

/-- The target measure of a coupling has the total mass of the coupling. -/
theorem measure_univ_right (hπ : IsCoupling π μ ν) : ν univ = π univ := by
  rw [← hπ.snd_eq, Measure.snd_univ]

/-- Coupled measures have equal total mass. Measures of different total mass are therefore not
coupled by anything. -/
theorem measure_univ_eq (hπ : IsCoupling π μ ν) : μ univ = ν univ :=
  hπ.measure_univ_left.trans hπ.measure_univ_right.symm

/-- A coupling of a finite measure is finite. -/
theorem isFiniteMeasure [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) : IsFiniteMeasure π :=
  ⟨by rw [← hπ.measure_univ_left]; exact measure_lt_top μ univ⟩

/-- A coupling of a probability measure is a probability measure. -/
theorem isProbabilityMeasure [IsProbabilityMeasure μ] (hπ : IsCoupling π μ ν) :
    IsProbabilityMeasure π :=
  ⟨by rw [← hπ.measure_univ_left, measure_univ]⟩

/-- A coupling with a finite target measure is finite. -/
theorem isFiniteMeasure_of_right [IsFiniteMeasure ν] (hπ : IsCoupling π μ ν) :
    IsFiniteMeasure π :=
  ⟨by rw [← hπ.measure_univ_right]; exact measure_lt_top ν univ⟩

/-- A coupling with a probability target measure is a probability measure. -/
theorem isProbabilityMeasure_of_right [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) :
    IsProbabilityMeasure π :=
  ⟨by rw [← hπ.measure_univ_right, measure_univ]⟩

/-- Exchanging the two coordinates of a coupling of `μ` and `ν` gives a coupling of `ν`
and `μ`. -/
protected theorem swap (hπ : IsCoupling π μ ν) : IsCoupling (π.map Prod.swap) ν μ where
  fst_eq := Measure.fst_map_swap.trans hπ.snd_eq
  snd_eq := Measure.snd_map_swap.trans hπ.fst_eq

/-- Pushing a coupling forward coordinatewise along measurable maps couples the two
pushforwards. -/
protected theorem map (hπ : IsCoupling π μ ν) {f : X → X'} {g : Y → Y'} (hf : Measurable f)
    (hg : Measurable g) : IsCoupling (π.map (Prod.map f g)) (μ.map f) (ν.map g) where
  fst_eq := by
    rw [← hπ.fst_eq]
    simp only [Measure.fst, Measure.map_map measurable_fst (hf.prodMap hg),
      Measure.map_map hf measurable_fst, Prod.map_fst']
  snd_eq := by
    rw [← hπ.snd_eq]
    simp only [Measure.snd, Measure.map_map measurable_snd (hf.prodMap hg),
      Measure.map_map hg measurable_snd, Prod.map_snd']

/-- Pushing a coupling forward along a measurable map of the source alone. -/
protected theorem map_left (hπ : IsCoupling π μ ν) {f : X → X'} (hf : Measurable f) :
    IsCoupling (π.map (Prod.map f id)) (μ.map f) ν := by
  simpa only [Measure.map_id] using hπ.map hf measurable_id

/-- Pushing a coupling forward along a measurable map of the target alone. -/
protected theorem map_right (hπ : IsCoupling π μ ν) {g : Y → Y'} (hg : Measurable g) :
    IsCoupling (π.map (Prod.map id g)) μ (ν.map g) := by
  simpa only [Measure.map_id] using hπ.map measurable_id hg

end IsCoupling

/-- The converse of `TauCeti.IsCoupling.measure_prod_univ` and
`TauCeti.IsCoupling.measure_univ_prod`: the coupling relation can be checked on measurable
cylinders, one for each factor. -/
theorem isCoupling_of_measure_prod_univ_of_measure_univ_prod
    (hs : ∀ s, MeasurableSet s → π (s ×ˢ univ) = μ s)
    (ht : ∀ t, MeasurableSet t → π (univ ×ˢ t) = ν t) : IsCoupling π μ ν where
  fst_eq := Measure.ext fun s hsm ↦ by rw [Measure.fst_apply hsm, ← prod_univ]; exact hs s hsm
  snd_eq := Measure.ext fun t htm ↦ by rw [Measure.snd_apply htm, ← univ_prod]; exact ht t htm

/-- The coupling relation is invariant under exchanging the two coordinates. -/
@[simp]
theorem isCoupling_map_swap_iff : IsCoupling (π.map Prod.swap) ν μ ↔ IsCoupling π μ ν :=
  ⟨fun h ↦ ⟨Measure.snd_map_swap.symm.trans h.snd_eq, Measure.fst_map_swap.symm.trans h.fst_eq⟩,
    IsCoupling.swap⟩

/-- The coupling relation is invariant under measurable equivalences of the two factors. -/
@[simp]
theorem isCoupling_map_prodMap_iff (e : X ≃ᵐ X') (f : Y ≃ᵐ Y') :
    IsCoupling (π.map (Prod.map e f)) (μ.map e) (ν.map f) ↔ IsCoupling π μ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map e.measurable f.measurable⟩
  simpa only [Measure.map_map (e.symm.measurable.prodMap f.symm.measurable)
      (e.measurable.prodMap f.measurable), Prod.map_comp_map, e.symm_comp_self,
    f.symm_comp_self, Prod.map_id, Measure.map_id, e.map_symm_map, f.map_symm_map] using
    h.map e.symm.measurable f.symm.measurable

/-- The product measure couples two probability measures, so probability measures always have
a coupling. -/
@[simp]
theorem isCoupling_prod (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCoupling (μ.prod ν) μ ν :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- A finite measure and a measure of equal total mass are coupled by their normalised product.
The equality makes the second measure finite. The statement includes the zero measures, where
the normalising factor is `∞` and the plan is `0`. -/
theorem isCoupling_inv_smul_prod [IsFiniteMeasure μ] (h : μ univ = ν univ) :
    IsCoupling ((μ univ)⁻¹ • μ.prod ν) μ ν := by
  let _ : IsFiniteMeasure ν := ⟨by rw [← h]; exact measure_lt_top μ univ⟩
  rcases eq_or_ne (μ univ) 0 with h0 | h0
  · have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp h0
    have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (h ▸ h0)
    subst hμ
    subst hν
    exact ⟨by simp, by simp⟩
  · have hinv : (μ univ)⁻¹ * μ univ = 1 := ENNReal.inv_mul_cancel h0 (measure_ne_top μ univ)
    refine ⟨?_, ?_⟩
    · simp only [Measure.fst, Measure.map_smul, Measure.map_fst_prod, smul_smul, ← h, hinv,
        one_smul]
    · simp only [Measure.snd, Measure.map_smul, Measure.map_snd_prod, smul_smul, hinv, one_smul]

/-- A finite measure and any measure admit a coupling exactly when they have the same total
mass. -/
theorem exists_isCoupling_iff [IsFiniteMeasure μ] :
    (∃ π : Measure (X × Y), IsCoupling π μ ν) ↔ μ univ = ν univ :=
  ⟨fun ⟨_, hπ⟩ ↦ hπ.measure_univ_eq, fun h ↦ ⟨_, isCoupling_inv_smul_prod h⟩⟩

section Dirac

/-- A Dirac measure and a probability measure are coupled by the pushforward of the latter
along `y ↦ (x, y)`. -/
@[simp]
theorem isCoupling_map_prodMk (x : X) (ν : Measure Y) [IsProbabilityMeasure ν] :
    IsCoupling (ν.map (Prod.mk x)) (Measure.dirac x) ν := by
  rw [← Measure.dirac_prod (ν := ν) x]
  exact isCoupling_prod (Measure.dirac x) ν

/-- Two Dirac measures are coupled by the Dirac measure at the pair. -/
@[simp]
theorem isCoupling_dirac_dirac (x : X) (y : Y) :
    IsCoupling (Measure.dirac (x, y)) (Measure.dirac x) (Measure.dirac y) := by
  rw [← Measure.dirac_prod_dirac]
  exact isCoupling_prod (Measure.dirac x) (Measure.dirac y)

variable {x : X} {y : Y}

/-- A plan whose source marginal is a Dirac measure is the pushforward of its target marginal
along `y ↦ (x, y)`. Together with `TauCeti.isCoupling_map_prodMk` this says that a Dirac source
has exactly one coupling with each probability target. -/
theorem IsCoupling.eq_map_prodMk (hπ : IsCoupling π (Measure.dirac x) ν) :
    π = ν.map (Prod.mk x) := by
  let _ : IsFiniteMeasure π := hπ.isFiniteMeasure
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [Measure.map_apply measurable_prodMk_left (hs.prod ht)]
    by_cases hxs : x ∈ s
    · rw [mk_preimage_prod_right hxs]
      calc
        π (s ×ˢ t) = π (univ ×ˢ t) := by
          apply measure_eq_measure_of_null_sdiff
            (Set.prod_mono (subset_univ s) Subset.rfl)
          apply measure_mono_null (t := sᶜ ×ˢ (univ : Set Y))
          · intro z hz
            exact ⟨fun hzs ↦ hz.2 ⟨hzs, hz.1.2⟩, mem_univ z.2⟩
          · rw [hπ.measure_prod_univ hs.compl, Measure.dirac_apply' x hs.compl]
            simp [hxs]
        _ = ν t := hπ.measure_univ_prod ht
    · rw [mk_preimage_prod_right_eq_empty hxs, measure_empty]
      apply measure_mono_null (Set.prod_mono Subset.rfl (subset_univ t))
      rw [hπ.measure_prod_univ hs, Measure.dirac_apply' x hs]
      simp [hxs]
  · rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ, preimage_univ,
      ← hπ.measure_univ_right]

/-- Two Dirac measures have exactly one coupling, the Dirac measure at the pair. -/
theorem IsCoupling.eq_dirac (hπ : IsCoupling π (Measure.dirac x) (Measure.dirac y)) :
    π = Measure.dirac (x, y) := by
  rw [hπ.eq_map_prodMk, Measure.map_dirac' measurable_prodMk_left]

end Dirac

/-- Being a coupling, read on bundled probability measures: the two marginal pushforwards are the
prescribed marginals. This is the form in which the coupling condition is a pair of preimages of
points under the marginal maps. -/
@[simp]
theorem isCoupling_toMeasure_iff {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    {π : ProbabilityMeasure (X × Y)} :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ↔
      π.map measurable_fst.aemeasurable = μ ∧ π.map measurable_snd.aemeasurable = ν := by
  rw [← ProbabilityMeasure.toMeasure_injective.eq_iff (a := π.map measurable_fst.aemeasurable),
    ← ProbabilityMeasure.toMeasure_injective.eq_iff (a := π.map measurable_snd.aemeasurable),
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  exact ⟨fun h ↦ ⟨h.fst_eq, h.snd_eq⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Couplings of two probability measures, bundled as a subtype of the probability measures on
the product. The unbundled relation `TauCeti.IsCoupling` is the one to use for raw
measures; this type is the domain over which the probability transport problem is optimised. -/
abbrev Coupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Type _ :=
  {π : ProbabilityMeasure (X × Y) // IsCoupling π.toMeasure μ.toMeasure ν.toMeasure}

namespace Coupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- Two bundled couplings are equal when their underlying measures are equal. -/
@[ext]
theorem ext {π σ : Coupling μ ν} (h : π.1.toMeasure = σ.1.toMeasure) : π = σ :=
  Subtype.ext (ProbabilityMeasure.toMeasure_injective h)

/-- The independent coupling of two probability measures: their product. -/
def prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Coupling μ ν :=
  ⟨μ.prod ν, by
    rw [ProbabilityMeasure.toMeasure_prod]
    exact isCoupling_prod _ _⟩

/-- The underlying probability measure of the independent coupling is the product probability
measure. -/
@[simp]
theorem coe_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (prod μ ν : ProbabilityMeasure (X × Y)) = μ.prod ν :=
  (rfl)

/-- Any two probability measures are coupled, by their product. -/
instance instNonempty : Nonempty (Coupling μ ν) :=
  ⟨prod μ ν⟩

/-- The first marginal of a bundled coupling. -/
def fst (π : Coupling μ ν) : ProbabilityMeasure X :=
  π.1.map measurable_fst.aemeasurable

/-- The second marginal of a bundled coupling. -/
def snd (π : Coupling μ ν) : ProbabilityMeasure Y :=
  π.1.map measurable_snd.aemeasurable

/-- The underlying measure of the first marginal is the pushforward along the first projection.
This is not a `simp` lemma: `simp` rewrites `π.fst` to `μ` via `fst_eq` instead. -/
theorem coe_fst (π : Coupling μ ν) :
    (π.fst).toMeasure = π.1.toMeasure.map Prod.fst :=
  (rfl)

/-- The underlying measure of the second marginal is the pushforward along the second projection.
This is not a `simp` lemma: `simp` rewrites `π.snd` to `ν` via `snd_eq` instead. -/
theorem coe_snd (π : Coupling μ ν) :
    (π.snd).toMeasure = π.1.toMeasure.map Prod.snd :=
  (rfl)

/-- The first marginal of a bundled coupling is its prescribed source. -/
@[simp]
theorem fst_eq (π : Coupling μ ν) : π.fst = μ :=
  ProbabilityMeasure.toMeasure_injective <| by
    rw [fst, ProbabilityMeasure.toMeasure_map]
    exact π.2.fst_eq

/-- The second marginal of a bundled coupling is its prescribed target. -/
@[simp]
theorem snd_eq (π : Coupling μ ν) : π.snd = ν :=
  ProbabilityMeasure.toMeasure_injective <| by
    rw [snd, ProbabilityMeasure.toMeasure_map]
    exact π.2.snd_eq

/-- Exchanging the two coordinates of a bundled coupling. -/
def swap (π : Coupling μ ν) : Coupling ν μ :=
  ⟨π.1.map measurable_swap.aemeasurable, by
    rw [ProbabilityMeasure.toMeasure_map]
    exact π.2.swap⟩

/-- The underlying probability measure of the exchanged coupling is the pushforward along the
coordinate swap. -/
@[simp]
theorem coe_swap (π : Coupling μ ν) :
    (π.swap : ProbabilityMeasure (Y × X)) = π.1.map measurable_swap.aemeasurable :=
  (rfl)

/-- Exchanging the coordinates twice is the identity. -/
@[simp]
theorem swap_swap (π : Coupling μ ν) : π.swap.swap = π := by
  apply ext
  simp only [coe_swap, ProbabilityMeasure.toMeasure_map,
    Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

/-- Exchanging the coordinates of the independent coupling gives the independent coupling of the
exchanged pair. -/
@[simp]
theorem swap_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (prod μ ν).swap = prod ν μ := by
  apply ext
  simp only [coe_swap, ProbabilityMeasure.toMeasure_map, coe_prod,
    ProbabilityMeasure.toMeasure_prod, Measure.prod_swap]

end Coupling

end TauCeti
