/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Projective limits on countable products

This file proves a countable version of Kolmogorov's extension theorem when every positive-indexed
coordinate is standard Borel. Mathlib defines projective measure families and proves uniqueness of
their projective limits, while its Ionescu--Tulcea construction produces a path law from a sequence
of transition kernels. Here a coherent family of finite-prefix laws is disintegrated to obtain
those kernels.

## Main result

* `TauCeti.Measure.exists_map_frestrictLe_eq` constructs a probability measure on a dependent
  sequence whose finite-prefix laws are a prescribed coherent family.
* `TauCeti.Measure.exists_isProjectiveLimit_nat` realizes a projective family indexed by finite
  subsets of `ℕ`.

This is the existence bridge between Mathlib's `MeasureTheory.IsProjectiveMeasureFamily` API and
its Ionescu--Tulcea theorem. The construction follows the standard proof of Kolmogorov extension
for countable products by successive disintegration, as prescribed by the
`TauCetiRoadmap/OptimalTransport/README.md` Layer 0, item 4 target.
-/

public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

/-- Split a trajectory through time `n + 1` into its prefix through time `n` and its last
coordinate. -/
private def prefixSuccEquiv (n : ℕ) :
    ((∀ i : Iic n, X i) × X (n + 1)) ≃ᵐ (∀ i : Iic (n + 1), X i) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n)).trans
    (MeasurableEquiv.IicProdIoc n.le_succ)

/-- The law of a prefix and its next coordinate, obtained from the next prescribed prefix law. -/
private def successorLaw (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) (n : ℕ) :
    Measure ((∀ i : Iic n, X i) × X (n + 1)) :=
  (P (n + 1)).map (prefixSuccEquiv n).symm

private instance successorLaw.instIsProbabilityMeasure
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    IsProbabilityMeasure (successorLaw P n) :=
  MeasureTheory.Measure.isProbabilityMeasure_map (prefixSuccEquiv n).symm.measurable.aemeasurable

private theorem fst_successorLaw (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i))
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ n.le_succ) = P n) (n : ℕ) :
    (successorLaw P n).fst = P n := by
  rw [successorLaw, MeasureTheory.Measure.fst,
    MeasureTheory.Measure.map_map measurable_fst (prefixSuccEquiv n).symm.measurable]
  have hfun : (Prod.fst : ((∀ i : Iic n, X i) × X (n + 1)) → (∀ i : Iic n, X i)) ∘
      (prefixSuccEquiv n).symm = frestrictLe₂ n.le_succ := by
    funext x i
    rfl
  rw [hfun, hP n]

/-- The transition kernel obtained by disintegrating the next prescribed prefix law over the
current prefix. -/
private def projectiveKernel [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X n)]
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    Kernel (∀ i : Iic n, X i) (X (n + 1)) :=
  (successorLaw P n).condKernel

private instance projectiveKernel.instIsMarkovKernel
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X n)]
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    IsMarkovKernel (projectiveKernel P n) := by
  rw [projectiveKernel]
  infer_instance

/-- The zeroth-coordinate law extracted from the first prescribed prefix law. -/
private def initialLaw (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) : Measure (X 0) :=
  (P 0).map (MeasurableEquiv.piUnique fun i : Iic 0 ↦ X i)

private instance initialLaw.instIsProbabilityMeasure
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)] :
    IsProbabilityMeasure (initialLaw P) :=
  MeasureTheory.Measure.isProbabilityMeasure_map
    (MeasurableEquiv.piUnique fun i : Iic 0 ↦ X i).measurable.aemeasurable

/-- The Ionescu--Tulcea path law built by successively disintegrating prescribed prefix laws. -/
private def prefixLimit (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, StandardBorelSpace (X (n + 1))]
    [∀ n, Nonempty (X n)] : Measure (∀ n, X n) :=
  Kernel.trajMeasure (initialLaw P) (projectiveKernel P)

private instance prefixLimit.instIsProbabilityMeasure
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X n)] :
    IsProbabilityMeasure (prefixLimit P) := by
  rw [prefixLimit]
  infer_instance

private theorem map_frestrictLe_zero_prefixLimit
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X n)] :
    (prefixLimit P).map (frestrictLe 0) = P 0 := by
  let e : (∀ i : Iic 0, X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
  have hprefix : (prefixLimit P).map (frestrictLe 0) = (initialLaw P).map e.symm := by
    rw [prefixLimit, Kernel.trajMeasure, MeasureTheory.Measure.map_comp,
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, MeasureTheory.Measure.id_comp]
    · rfl
    · fun_prop
  calc
    (prefixLimit P).map (frestrictLe 0) = (initialLaw P).map e.symm := hprefix
    _ = ((P 0).map e).map e.symm := rfl
    _ = P 0 := MeasurableEquiv.map_map_symm e.symm

private theorem map_frestrictLe_succ_prefixLimit
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X n)]
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ n.le_succ) = P n) {n : ℕ}
    (hn : (prefixLimit P).map (frestrictLe n) = P n) :
    (prefixLimit P).map (frestrictLe (n + 1)) = P (n + 1) := by
  have hcomp : (prefixLimit P).map (frestrictLe n) ⊗ₘ projectiveKernel P n =
      successorLaw P n := by
    rw [hn, ← fst_successorLaw P hP n, projectiveKernel,
      MeasureTheory.Measure.disintegrate]
  have hpair : (prefixLimit P).map (fun x ↦ (frestrictLe n x, x (n + 1))) =
      successorLaw P n := by
    calc
      _ = (prefixLimit P).map (frestrictLe n) ⊗ₘ projectiveKernel P n := by
        simpa only [prefixLimit] using
          (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
            (μ₀ := initialLaw P) (κ := projectiveKernel P) (a := n)).symm
      _ = successorLaw P n := hcomp
  have hfun : frestrictLe (n + 1) =
      prefixSuccEquiv n ∘ fun x : (∀ n, X n) ↦ (frestrictLe n x, x (n + 1)) := by
    funext x
    apply (prefixSuccEquiv n).symm.injective
    simp only [Function.comp_apply]
    rw [(prefixSuccEquiv n).symm_apply_apply]
    apply Prod.ext
    · rfl
    · rfl
  rw [hfun, ← MeasureTheory.Measure.map_map (prefixSuccEquiv n).measurable (by fun_prop),
    hpair, successorLaw]
  exact MeasurableEquiv.map_map_symm (prefixSuccEquiv n)

/-- **Countable projective-family extension for coherent prefixes.** A coherent family of
probability laws on the prefixes `∀ i : Iic n, X i` of a dependent sequence of standard Borel
spaces, except that the zeroth coordinate need only be measurable, is realized by a probability
law on the whole sequence.

The result is stated directly in terms of prefix laws because this is the interface consumed by
countable gluing constructions. Together with Mathlib's
`MeasureTheory.isProjectiveMeasureFamily_inducedFamily` and
`MeasureTheory.isProjectiveLimit_nat_iff`, it gives the usual `Finset ℕ` formulation. -/
theorem exists_map_frestrictLe_eq [∀ n, StandardBorelSpace (X (n + 1))]
    (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ n.le_succ) = P n) :
    ∃ μ : Measure (∀ n, X n), IsProbabilityMeasure μ ∧
      ∀ n, μ.map (frestrictLe n) = P n := by
  let _ : ∀ n, Nonempty (X n) := fun n =>
    (nonempty_of_isProbabilityMeasure (P n)).map fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  refine ⟨prefixLimit P, inferInstance, ?_⟩
  intro n
  induction n with
  | zero => exact map_frestrictLe_zero_prefixLimit P
  | succ n hn => exact map_frestrictLe_succ_prefixLimit P hP hn

/-- **Kolmogorov extension for a sequence with standard Borel positive coordinates.** Every
projective family of probability laws indexed by the finite subsets of `ℕ` has a projective limit,
which is again a probability measure.

Mathlib already proves that this projective limit is unique; this theorem supplies existence by
reducing to coherent prefixes and applying `TauCeti.Measure.exists_map_frestrictLe_eq`. -/
theorem exists_isProjectiveLimit_nat [∀ n, StandardBorelSpace (X (n + 1))]
    (P : ∀ I : Finset ℕ, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ n, X n), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  have hprefix : ∀ n, (P (Iic (n + 1))).map (frestrictLe₂ n.le_succ) = P (Iic n) :=
    fun n => (hP (Iic (n + 1)) (Iic n) (Iic_subset_Iic.mpr n.le_succ)).symm
  obtain ⟨μ, hμprob, hμ⟩ := exists_map_frestrictLe_eq (fun n => P (Iic n)) hprefix
  exact ⟨μ, hμprob, (isProjectiveLimit_nat_iff hP μ).mpr hμ⟩

end Measure

end TauCeti
