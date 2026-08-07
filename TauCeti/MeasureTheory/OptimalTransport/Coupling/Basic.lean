/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import TauCeti.MeasureTheory.Measure.Prod

/-!
# Couplings of measures

This file defines a coupling of two measures as a measure on their product with the prescribed
marginals. It also provides the bundled space of couplings of two probability measures.

The basic API records the marginal formulas and equality of total masses, constructs the product
coupling, and transports couplings by swapping or measurably mapping their coordinates. These are
the definition-level foundations required by Layer 0 of
`TauCetiRoadmap/OptimalTransport/README.md`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

universe u v u' v' u'' v''

namespace Measure

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measure `π` on `X × Y` is a coupling of `μ` and `ν` when its first and second
marginals are respectively `μ` and `ν`. -/
structure IsCoupling (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) : Prop where
  fst_eq : π.fst = μ
  snd_eq : π.snd = ν

namespace IsCoupling

variable {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

/-- A coupling evaluated on `s × univ` equals its first marginal evaluated on `s`. -/
@[grind =>]
theorem measure_prod_univ (hπ : IsCoupling π μ ν) {s : Set X} (hs : MeasurableSet s) :
    π (s ×ˢ univ) = μ s := by
  rw [← hπ.fst_eq, MeasureTheory.Measure.fst_apply hs]
  congr 1
  ext z
  simp

/-- A coupling evaluated on `univ × t` equals its second marginal evaluated on `t`. -/
@[grind =>]
theorem measure_univ_prod (hπ : IsCoupling π μ ν) {t : Set Y} (ht : MeasurableSet t) :
    π (univ ×ˢ t) = ν t := by
  rw [← hπ.snd_eq, MeasureTheory.Measure.snd_apply ht]
  congr 1
  ext z
  simp

/-- The two marginals of a coupling have the same total mass. -/
theorem measure_univ_eq (hπ : IsCoupling π μ ν) : μ univ = ν univ := by
  rw [← hπ.fst_eq, ← hπ.snd_eq, MeasureTheory.Measure.fst_univ,
    MeasureTheory.Measure.snd_univ]

/-- Swapping the coordinates of a coupling swaps its marginals. -/
protected theorem swap (hπ : IsCoupling π μ ν) :
    IsCoupling (π.map Prod.swap) ν μ where
  fst_eq := by simpa only [MeasureTheory.Measure.fst_map_swap] using hπ.snd_eq
  snd_eq := by simpa only [MeasureTheory.Measure.snd_map_swap] using hπ.fst_eq

/-- Mapping both coordinates of a coupling maps its two marginals. -/
protected theorem map {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (hπ : IsCoupling π μ ν) {f : X → X'} {g : Y → Y'} (hf : Measurable f)
    (hg : Measurable g) :
    IsCoupling (π.map (Prod.map f g)) (μ.map f) (ν.map g) where
  fst_eq := by rw [Measure.fst_map_prodMap π hf hg, hπ.fst_eq]
  snd_eq := by rw [Measure.snd_map_prodMap π hf hg, hπ.snd_eq]

end IsCoupling

/-- The zero measure couples the two zero measures. -/
@[simp]
theorem isCoupling_zero : IsCoupling (0 : Measure (X × Y)) 0 0 where
  fst_eq := MeasureTheory.Measure.fst_zero
  snd_eq := MeasureTheory.Measure.snd_zero

/-- The normalized product of two finite measures of equal mass couples its factors. -/
theorem isCoupling_inv_smul_prod (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) :
    IsCoupling ((μ univ)⁻¹ • μ.prod ν) μ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (hμν ▸ by simp [hμ])
    simp [hμ, hν]
  have hμuniv : μ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  constructor
  · rw [Measure.fst, Measure.map_smul, Measure.map_fst_prod, ← hμν, smul_smul,
      ENNReal.inv_mul_cancel hμuniv (measure_ne_top μ univ), one_smul]
  · rw [Measure.snd, Measure.map_smul, Measure.map_snd_prod, smul_smul,
      ENNReal.inv_mul_cancel hμuniv (measure_ne_top μ univ), one_smul]

/-- The product of two probability measures is a coupling of its factors. -/
@[simp]
theorem isCoupling_prod (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCoupling (μ.prod ν) μ ν := by
  simpa only [measure_univ, inv_one, one_smul] using
    isCoupling_inv_smul_prod μ ν (by simp)

end Measure

/-- Probability measures on `X × Y` whose marginals are `μ` and `ν`. -/
abbrev Coupling {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :=
  {π : ProbabilityMeasure (X × Y) //
    Measure.IsCoupling π.toMeasure μ.toMeasure ν.toMeasure}

namespace Coupling

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- The product probability measure, regarded as a coupling of its factors. -/
def prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Coupling μ ν :=
  ⟨μ.prod ν, Measure.isCoupling_prod μ.toMeasure ν.toMeasure⟩

/-- The type of couplings of two probability measures is nonempty. -/
instance instNonempty : Nonempty (Coupling μ ν) :=
  ⟨prod μ ν⟩

/-- The underlying probability measure of the product coupling is the product measure. -/
@[simp]
theorem coe_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (prod μ ν : ProbabilityMeasure (X × Y)) = μ.prod ν :=
  (rfl)

/-- The first marginal of a bundled coupling is its first endpoint. -/
@[simp]
theorem fst_eq (π : Coupling μ ν) : π.1.toMeasure.fst = μ.toMeasure :=
  π.2.fst_eq

/-- The second marginal of a bundled coupling is its second endpoint. -/
@[simp]
theorem snd_eq (π : Coupling μ ν) : π.1.toMeasure.snd = ν.toMeasure :=
  π.2.snd_eq

/-- Two bundled couplings are equal when their underlying measures are equal. -/
@[ext]
theorem ext {π κ : Coupling μ ν} (h : π.1.toMeasure = κ.1.toMeasure) : π = κ := by
  apply Subtype.ext
  exact ProbabilityMeasure.toMeasure_injective h

/-- Swap the coordinates and endpoints of a bundled coupling. -/
def swap (π : Coupling μ ν) : Coupling ν μ :=
  ⟨π.1.map measurable_swap.aemeasurable, by
    simpa only [ProbabilityMeasure.toMeasure_map] using π.2.swap⟩

/-- The underlying probability measure of a swapped coupling is the pushforward by
`Prod.swap`. -/
@[simp]
theorem coe_swap (π : Coupling μ ν) :
    (π.swap : ProbabilityMeasure (Y × X)) = π.1.map measurable_swap.aemeasurable :=
  (rfl)

/-- Map the two coordinates and endpoints of a bundled coupling. -/
def map {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (π : Coupling μ ν) (f : X → X') (g : Y → Y') (hf : Measurable f)
    (hg : Measurable g) :
    Coupling (μ.map hf.aemeasurable) (ν.map hg.aemeasurable) :=
  ⟨π.1.map (hf.prodMap hg).aemeasurable, by
    simpa only [ProbabilityMeasure.toMeasure_map] using π.2.map hf hg⟩

/-- The underlying probability measure of a mapped coupling is the pushforward by the product
map. -/
@[simp]
theorem coe_map {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (π : Coupling μ ν) (f : X → X') (g : Y → Y') (hf : Measurable f)
    (hg : Measurable g) :
    (π.map f g hf hg : ProbabilityMeasure (X' × Y')) =
      π.1.map (hf.prodMap hg).aemeasurable :=
  (rfl)

/-- Mapping both coordinates by the identity leaves the underlying probability measure
unchanged. -/
@[simp]
theorem coe_map_id (π : Coupling μ ν) :
    π.1.map measurable_id.aemeasurable = π.1 := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [ProbabilityMeasure.toMeasure_map] using
    (Measure.map_id (μ := π.1.toMeasure))

/-- Two successive coordinatewise maps agree on underlying probability measures with mapping by
the composites. -/
@[simp]
theorem coe_map_map {X' : Type u'} {Y' : Type v'} {X'' : Type u''} {Y'' : Type v''}
    [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace X''] [MeasurableSpace Y'']
    (π : Coupling μ ν) (f : X → X') (g : Y → Y') (f' : X' → X'') (g' : Y' → Y'')
    (hf : Measurable f) (hg : Measurable g) (hf' : Measurable f') (hg' : Measurable g') :
    (π.1.map (hf.prodMap hg).aemeasurable).map (hf'.prodMap hg').aemeasurable =
      (π.map (f' ∘ f) (g' ∘ g) (hf'.comp hf) (hg'.comp hg)).1 := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (hf'.prodMap hg') (hf.prodMap hg), Prod.map_comp_map]
  rfl

/-- Swapping after a coordinatewise map is the same as mapping the swapped coupling in the
opposite coordinate order. -/
@[simp]
theorem swap_map {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (π : Coupling μ ν) (f : X → X') (g : Y → Y') (hf : Measurable f)
    (hg : Measurable g) :
    (π.map f g hf hg).swap = π.swap.map g f hg hf := by
  apply ext
  simp only [coe_swap, coe_map, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_swap (hf.prodMap hg),
    Measure.map_map (hg.prodMap hf) measurable_swap, ← Prod.map_comp_swap]

/-- Pairs of measurable equivalences induce an equivalence between the corresponding coupling
spaces. -/
def mapEquiv {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (e : X ≃ᵐ X') (d : Y ≃ᵐ Y') :
    Coupling μ ν ≃
      Coupling (μ.map e.measurable.aemeasurable) (ν.map d.measurable.aemeasurable) where
  toFun π := π.map e d e.measurable d.measurable
  invFun π :=
    ⟨π.1.map (e.symm.measurable.prodMap d.symm.measurable).aemeasurable, by
      simpa only [ProbabilityMeasure.toMeasure_map, MeasurableEquiv.map_symm_map] using
        π.2.map e.symm.measurable d.symm.measurable⟩
  left_inv π := by
    apply ext
    simp only [Coupling.map, ProbabilityMeasure.toMeasure_map]
    convert MeasurableEquiv.map_symm_map (μ := π.1.toMeasure) (e.prodCongr d) using 1
    all_goals rfl
  right_inv π := by
    apply ext
    simp only [Coupling.map, ProbabilityMeasure.toMeasure_map]
    convert MeasurableEquiv.map_map_symm (ν := π.1.toMeasure) (e.prodCongr d) using 1
    all_goals rfl

/-- Applying the coupling equivalence maps both coordinates. -/
@[simp]
theorem mapEquiv_apply {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (e : X ≃ᵐ X') (d : Y ≃ᵐ Y') (π : Coupling μ ν) :
    mapEquiv e d π = π.map e d e.measurable d.measurable :=
  (rfl)

/-- Mapping a product coupling gives the product coupling of the mapped endpoints. -/
@[simp]
theorem map_prod {X' : Type u'} {Y' : Type v'} [MeasurableSpace X'] [MeasurableSpace Y']
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (f : X → X') (g : Y → Y')
    (hf : Measurable f) (hg : Measurable g) :
    (prod μ ν).map f g hf hg = prod (μ.map hf.aemeasurable) (ν.map hg.aemeasurable) := by
  apply Subtype.ext
  simpa only [coe_map, coe_prod] using (ProbabilityMeasure.map_prod_map μ ν hf hg).symm

/-- Swapping a product coupling gives the product coupling in the opposite order. -/
@[simp]
theorem swap_prod (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    (prod μ ν).swap = prod ν μ := by
  apply Subtype.ext
  simpa only [coe_swap, coe_prod] using ProbabilityMeasure.prod_swap μ ν

/-- Swapping a coupling twice gives the original coupling. -/
@[simp]
theorem swap_swap (π : Coupling μ ν) : π.swap.swap = π := by
  apply Coupling.ext
  simp only [swap, ProbabilityMeasure.toMeasure_map]
  convert MeasurableEquiv.map_symm_map (μ := π.1.toMeasure)
    (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X) using 1
  all_goals rfl

end Coupling

end TauCeti
