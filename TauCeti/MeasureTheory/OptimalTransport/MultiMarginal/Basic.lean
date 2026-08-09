/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Multi-marginal couplings

This file defines a multi-marginal coupling as a probability measure on a dependent product
with prescribed one-coordinate marginals. It provides coordinate and pair projections,
coordinatewise maps, reindexing, and, over a finite index type, the independent product
coupling.

These constructions form the finite multi-marginal part of Layer 0 of the optimal-transport
roadmap. The definitions allow heterogeneous coordinate spaces; repeated-coordinate projections
are also allowed, which is useful for forming diagonal marginals. Finiteness of the index type
is assumed only where the independent product measure is involved, since the marginal,
projection, reindexing and coordinatewise-map API needs nothing beyond measurable pushforwards.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

universe u v w

namespace Measure

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]

/-- A measure on a dependent product is a multi-marginal coupling of `μ` when its
pushforward by every coordinate evaluation is the corresponding measure `μ i`. -/
structure IsMultiCoupling (π : Measure (∀ i, X i)) (μ : ∀ i, Measure (X i)) : Prop where
  marginal_eq : ∀ i, π.map (Function.eval i) = μ i

namespace IsMultiCoupling

variable {π : Measure (∀ i, X i)} {μ : ∀ i, Measure (X i)}

/-- Projecting a multi-marginal coupling along a family of coordinates gives another
multi-marginal coupling. The coordinate family need not be injective. -/
protected theorem project {κ : Type w} (hπ : IsMultiCoupling π μ) (e : κ → ι) :
    IsMultiCoupling
      (π.map fun x j ↦ x (e j))
      (fun j ↦ μ (e j)) := by
  constructor
  intro j
  calc
    (π.map fun x k ↦ x (e k)).map (Function.eval j) =
        π.map (Function.eval j ∘ fun x k ↦ x (e k)) :=
      Measure.map_map (measurable_pi_apply j)
        (measurable_pi_lambda _ fun k ↦ measurable_pi_apply (e k))
    _ = π.map (Function.eval (e j)) := by congr 2
    _ = μ (e j) := hπ.marginal_eq (e j)

/-- Applying measurable maps coordinatewise to a multi-marginal coupling pushes each marginal
forward by the corresponding map. -/
protected theorem map {Y : ι → Type w} [∀ i, MeasurableSpace (Y i)]
    (hπ : IsMultiCoupling π μ) (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i)) :
    IsMultiCoupling
      (π.map fun x i ↦ f i (x i))
      (fun i ↦ (μ i).map (f i)) := by
  constructor
  intro i
  calc
    (π.map fun x j ↦ f j (x j)).map (Function.eval i) =
        π.map (Function.eval i ∘ fun x j ↦ f j (x j)) :=
      Measure.map_map (measurable_pi_apply i)
        (measurable_pi_lambda _ fun j ↦ (hf j).comp (measurable_pi_apply j))
    _ = π.map (f i ∘ Function.eval i) := by congr 2
    _ = (π.map (Function.eval i)).map (f i) :=
      (Measure.map_map (hf i) (measurable_pi_apply i)).symm
    _ = (μ i).map (f i) := congrArg (Measure.map (f i)) (hπ.marginal_eq i)

/-- The pair projection of a multi-marginal coupling has the prescribed first marginal. -/
theorem fst_map_pair (hπ : IsMultiCoupling π μ) (i j : ι) :
    (π.map fun x ↦ (x i, x j)).fst = μ i := by
  rw [Measure.fst_map_prodMk (measurable_pi_apply j)]
  exact hπ.marginal_eq i

/-- The pair projection of a multi-marginal coupling has the prescribed second marginal. -/
theorem snd_map_pair (hπ : IsMultiCoupling π μ) (i j : ι) :
    (π.map fun x ↦ (x i, x j)).snd = μ j := by
  rw [Measure.snd_map_prodMk (measurable_pi_apply i)]
  exact hπ.marginal_eq j

end IsMultiCoupling

/-- The finite product of probability measures is a multi-marginal coupling of its factors. -/
@[simp]
theorem isMultiCoupling_pi [Fintype ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsMultiCoupling (Measure.pi μ) μ where
  marginal_eq i := (measurePreserving_eval μ i).map_eq

end Measure

/-- Probability measures on a dependent product with prescribed coordinate marginals. The
index type carries no finiteness assumption: it is `MultiCoupling.pi` and
`MultiCoupling.instNonempty`, not the bundle itself, that need `ι` to be finite. -/
abbrev MultiCoupling {ι : Type u} {X : ι → Type v}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, ProbabilityMeasure (X i)) :=
  {π : ProbabilityMeasure (∀ i, X i) //
    Measure.IsMultiCoupling π.toMeasure (fun i ↦ (μ i).toMeasure)}

namespace MultiCoupling

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- The independent product probability measure, regarded as a multi-marginal coupling. -/
def pi [Fintype ι] (μ : ∀ i, ProbabilityMeasure (X i)) : MultiCoupling μ :=
  ⟨ProbabilityMeasure.pi μ, by
    simpa only [ProbabilityMeasure.toMeasure_pi] using
      Measure.isMultiCoupling_pi (fun i ↦ (μ i).toMeasure)⟩

/-- Every family of probability measures indexed by a finite type has a multi-marginal
coupling. -/
instance instNonempty [Finite ι] : Nonempty (MultiCoupling μ) := by
  have := Fintype.ofFinite ι
  exact ⟨pi μ⟩

/-- The underlying probability measure of the independent multi-coupling is the product
probability measure. -/
@[simp]
theorem coe_pi [Fintype ι] (μ : ∀ i, ProbabilityMeasure (X i)) :
    (pi μ : ProbabilityMeasure (∀ i, X i)) = ProbabilityMeasure.pi μ :=
  (rfl)

/-- The `i`th marginal of a bundled multi-marginal coupling. -/
def marginal (π : MultiCoupling μ) (i : ι) : ProbabilityMeasure (X i) :=
  π.1.map (measurable_pi_apply i).aemeasurable

/-- The underlying measure of a coordinate marginal is the corresponding pushforward. This is
not a `simp` lemma: `simp` rewrites `π.marginal i` to `μ i` via `marginal_eq` instead. -/
theorem coe_marginal (π : MultiCoupling μ) (i : ι) :
    (π.marginal i).toMeasure = π.1.toMeasure.map (Function.eval i) :=
  (rfl)

/-- Every coordinate marginal of a bundled multi-marginal coupling is its prescribed endpoint. -/
@[simp]
theorem marginal_eq (π : MultiCoupling μ) (i : ι) : π.marginal i = μ i := by
  apply ProbabilityMeasure.toMeasure_injective
  exact π.2.marginal_eq i

/-- Two bundled multi-marginal couplings are equal when their underlying measures are equal. -/
@[ext]
theorem ext {π κ : MultiCoupling μ} (h : π.1.toMeasure = κ.1.toMeasure) : π = κ := by
  apply Subtype.ext
  exact ProbabilityMeasure.toMeasure_injective h

/-- Project a coupling to a family of coordinates. The coordinate family need not be
injective. -/
def project {κ : Type w} (π : MultiCoupling μ) (e : κ → ι) :
    MultiCoupling (fun j ↦ μ (e j)) :=
  ⟨π.1.map (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)).aemeasurable, by
    simpa only [ProbabilityMeasure.toMeasure_map] using π.2.project e⟩

/-- The underlying probability measure of a coordinate projection is the corresponding
pushforward. -/
@[simp]
theorem coe_project {κ : Type w} (π : MultiCoupling μ) (e : κ → ι) :
    (π.project e : ProbabilityMeasure (∀ j, X (e j))) =
      π.1.map (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)).aemeasurable :=
  (rfl)

/-- Projecting along the identity coordinate family leaves a multi-marginal coupling
unchanged. -/
@[simp]
theorem project_id (π : MultiCoupling μ) : π.project id = π := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  simp only [project, ProbabilityMeasure.toMeasure_map]
  exact Measure.map_id'

/-- Projecting successively agrees with projecting along the composite coordinate family. -/
@[simp]
theorem project_comp {κ : Type w} {τ : Type*} (π : MultiCoupling μ) (e : κ → ι) (d : τ → κ) :
    (π.project e).project d = π.project (e ∘ d) := by
  apply ext
  simp only [project, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_pi_lambda _ fun k ↦ measurable_pi_apply (d k))
    (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j))]
  rfl

/-- Reindex a multi-marginal coupling along an equivalence of index types. -/
def reindex {κ : Type w} (π : MultiCoupling μ) (e : κ ≃ ι) :
    MultiCoupling (fun j ↦ μ (e j)) :=
  π.project e

/-- Reindexing is the pushforward by precomposition with the index equivalence. -/
@[simp]
theorem coe_reindex {κ : Type w} (π : MultiCoupling μ) (e : κ ≃ ι) :
    (π.reindex e : ProbabilityMeasure (∀ j, X (e j))) =
      π.1.map (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e j)).aemeasurable :=
  (rfl)

/-- Reindexing by the identity equivalence leaves a multi-marginal coupling unchanged. -/
@[simp]
theorem reindex_refl (π : MultiCoupling μ) : π.reindex (Equiv.refl ι) = π :=
  π.project_id

/-- Reindexing successively agrees with reindexing by the composite equivalence. -/
@[simp]
theorem reindex_trans {κ : Type w} {τ : Type*}
    (π : MultiCoupling μ) (e : κ ≃ ι) (d : τ ≃ κ) :
    (π.reindex e).reindex d = π.reindex (d.trans e) :=
  π.project_comp e d

/-- Applying measurable maps coordinatewise to a multi-marginal coupling. -/
def map {Y : ι → Type w} [∀ i, MeasurableSpace (Y i)] (π : MultiCoupling μ)
    (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i)) :
    MultiCoupling (fun i ↦ (μ i).map (hf i).aemeasurable) :=
  ⟨π.1.map (measurable_pi_lambda _ fun i ↦ (hf i).comp (measurable_pi_apply i)).aemeasurable,
    by
      simp only [ProbabilityMeasure.toMeasure_map]
      convert π.2.map f hf using 1
      all_goals rfl⟩

/-- The underlying probability measure of a coordinatewise map is the corresponding
pushforward. -/
@[simp]
theorem coe_map {Y : ι → Type w} [∀ i, MeasurableSpace (Y i)] (π : MultiCoupling μ)
    (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i)) :
    (π.map f hf : ProbabilityMeasure (∀ i, Y i)) =
      π.1.map (measurable_pi_lambda _ fun i ↦ (hf i).comp (measurable_pi_apply i)).aemeasurable :=
  (rfl)

/-- Mapping every coordinate by the identity leaves the underlying probability measure
unchanged. This is not a `simp` lemma: `simp` unfolds the left-hand side through `coe_map`. -/
theorem coe_map_id (π : MultiCoupling μ) :
    (π.map (fun _ ↦ id) (fun _ ↦ measurable_id)).1 = π.1 := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [map, ProbabilityMeasure.toMeasure_map]
  calc
    π.1.toMeasure.map (fun x i ↦ id (x i)) = π.1.toMeasure.map id := by congr 2
    _ = π.1.toMeasure := Measure.map_id

/-- Coordinatewise mapping preserves the independent product coupling. -/
@[simp]
theorem map_pi [Fintype ι] {Y : ι → Type w} [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, ProbabilityMeasure (X i)) (f : ∀ i, X i → Y i)
    (hf : ∀ i, Measurable (f i)) :
    (pi μ).map f hf = pi (fun i ↦ (μ i).map (hf i).aemeasurable) := by
  apply ext
  simp only [map, pi, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
  exact Measure.pi_map_pi (fun i ↦ (hf i).aemeasurable)

/-- The joint law of coordinates `i` and `j` of a multi-marginal coupling. -/
def projectPair (π : MultiCoupling μ) (i j : ι) : ProbabilityMeasure (X i × X j) :=
  π.1.map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable

/-- The underlying measure of a pair projection is the corresponding pushforward. This is not a
`simp` lemma: `simp` rewrites the marginals of a pair projection through `fst_projectPair` and
`snd_projectPair` instead. -/
theorem coe_projectPair (π : MultiCoupling μ) (i j : ι) :
    (π.projectPair i j).toMeasure = π.1.toMeasure.map (fun x ↦ (x i, x j)) :=
  (rfl)

/-- The first marginal of a pair projection is its first selected coordinate. -/
@[simp]
theorem fst_projectPair (π : MultiCoupling μ) (i j : ι) :
    (π.projectPair i j).toMeasure.fst = (μ i).toMeasure := by
  simpa only [projectPair, ProbabilityMeasure.toMeasure_map] using π.2.fst_map_pair i j

/-- The second marginal of a pair projection is its second selected coordinate. -/
@[simp]
theorem snd_projectPair (π : MultiCoupling μ) (i j : ι) :
    (π.projectPair i j).toMeasure.snd = (μ j).toMeasure := by
  simpa only [projectPair, ProbabilityMeasure.toMeasure_map] using π.2.snd_map_pair i j

/-- Selecting the same coordinate twice gives its diagonal law. -/
@[simp]
theorem projectPair_self (π : MultiCoupling μ) (i : ι) :
    π.projectPair i i = (μ i).map (measurable_id.prodMk measurable_id).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [projectPair, ProbabilityMeasure.toMeasure_map]
  calc
    π.1.toMeasure.map (fun x ↦ (x i, x i)) =
        π.1.toMeasure.map ((fun x ↦ (x, x)) ∘ Function.eval i) := by congr 2
    _ = (π.1.toMeasure.map (Function.eval i)).map (fun x ↦ (x, x)) :=
      (Measure.map_map (measurable_id.prodMk measurable_id) (measurable_pi_apply i)).symm
    _ = (μ i).toMeasure.map (fun x ↦ (x, x)) :=
      congrArg (Measure.map fun x ↦ (x, x)) (π.2.marginal_eq i)

end MultiCoupling

end TauCeti
