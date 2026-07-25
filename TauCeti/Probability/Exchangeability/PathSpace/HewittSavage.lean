/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Sigma
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import Mathlib.Probability.Independence.ZeroOne
-- Non-public: used only inside proofs.
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# The Hewitt–Savage zero-one law

Work in progress.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The finitely supported permutation of `ℕ` that swaps the block `[0, N)` with `[N, 2N)`
pointwise and fixes everything from `2 * N` on. -/
def blockSwap (N : ℕ) : Equiv.Perm ℕ :=
  Equiv.Perm.viaFintypeEmbedding
    (((finSumFinEquiv (m := N) (n := N)).symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv)
    ⟨Fin.val, Fin.val_injective⟩

theorem blockSwap_apply_of_lt {N i : ℕ} (hi : i < N) : blockSwap N i = N + i := by
  have key : ((finSumFinEquiv.symm.trans (Equiv.sumComm (Fin N) (Fin N))).trans finSumFinEquiv)
      (Fin.castAdd N ⟨i, hi⟩) = Fin.natAdd N ⟨i, hi⟩ := by
    rw [Equiv.trans_apply, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.castAdd N ⟨i, hi⟩) = i := rfl
  rw [blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, key]
  rfl

theorem blockSwap_apply_of_le {N n : ℕ} (hn : N + N ≤ n) : blockSwap N n = n := by
  refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact absurd j.isLt (not_lt.mpr hn)

/-- `blockSwap N` carries any index block inside `[0, N)` off itself: the moved copy lands in
`[N, 2N)`. This is the disjointness the independence step consumes. -/
theorem disjoint_map_blockSwap {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range N) :
    Disjoint F (F.map (Equiv.toEmbedding (blockSwap N))) := by
  rw [Finset.disjoint_left]
  intro a haF hamem
  obtain ⟨b, hbF, hb⟩ := Finset.mem_map.mp hamem
  have hbN : b < N := Finset.mem_range.mp (hF hbF)
  have haN : a < N := Finset.mem_range.mp (hF haF)
  rw [Equiv.coe_toEmbedding, blockSwap_apply_of_lt hbN] at hb
  omega

theorem blockSwap_finite_support (N : ℕ) :
    (MulAction.fixedBy ℕ (blockSwap N))ᶜ.Finite := by
  refine Set.Finite.subset (Set.finite_Iio (N + N)) ?_
  intro n hn
  by_contra hmem
  exact hn (blockSwap_apply_of_le (not_lt.mp hmem))

section Cylinder

variable {α : Type*}

/-- Read a block indexed by the moved index set `F.map π` back onto `F`, along `π`. This is the
change of variables that turns a `π`-reindexed cylinder over `F` into a cylinder over `F.map π`. -/
@[expose]
def pullMoved (π : Equiv.Perm ℕ) (F : Finset ℕ) (α : Type*)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) : ∀ _i : F, α :=
  fun i => g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩

@[simp]
theorem pullMoved_apply (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) (i : F) :
    pullMoved π F α g i = g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩ :=
  rfl

/-- Reindexing a cylinder over `F` by `π` is a cylinder over the moved index set `F.map π`: both
sides say that the coordinates `p (π i)`, for `i ∈ F`, lie in `S`. -/
theorem preimage_permReindex_cylinder (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (S : Set (∀ _i : F, α)) :
    permReindex (α := α) π ⁻¹' cylinder F S
      = cylinder (F.map (Equiv.toEmbedding π)) (pullMoved π F α ⁻¹' S) :=
  rfl

@[fun_prop]
theorem measurable_pullMoved [MeasurableSpace α] (π : Equiv.Perm ℕ) (F : Finset ℕ) :
    Measurable (pullMoved π F α) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Every measurable path-space event is approximated, in measure, by a measurable cylinder over a
finite index set. -/
theorem exists_cylinder_measure_symmDiff_lt [MeasurableSpace α] {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] {s : Set (ℕ → α)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset ℕ) (S : Set (∀ _i : F, α)),
      MeasurableSet S ∧ ρ (symmDiff (cylinder F S) s) < ε := by
  have hcov : ∃ D : Set (Set (ℕ → α)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℕ => α) ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · rintro u (rfl : u = Set.univ)
      rw [← cylinder_univ (∅ : Finset ℕ)]
      exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
    · simp
  obtain ⟨t, ht_mem, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ρ)
    isSetRing_measurableCylinders hcov generateFrom_measurableCylinders.symm hs hε
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht_mem
  exact ⟨F, S, hS, ht⟩

/-- A cylinder over a measurable base is measurable. -/
theorem measurableSet_cylinder [MeasurableSpace α] (F : Finset ℕ) {S : Set (∀ _i : F, α)}
    (hS : MeasurableSet S) : MeasurableSet (cylinder (α := fun _ : ℕ => α) F S) :=
  (measurable_pi_lambda _ fun i : F => measurable_pi_apply (i : ℕ)) hS

end Cylinder

section Independence

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Cylinders over **disjoint** index blocks are independent events under the path law of an
independent family. This is the step that turns the disjointness produced by `blockSwap` into a
product formula. -/
theorem measure_pathLaw_inter_cylinder_of_disjoint {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : ∀ n, Measurable (X n)) (h_indep : ProbabilityTheory.iIndepFun X μ)
    {F G : Finset ℕ} (hFG : Disjoint F G)
    {S : Set (∀ _i : F, α)} (hS : MeasurableSet S)
    {T : Set (∀ _j : G, α)} (hT : MeasurableSet T) :
    pathLaw μ X (cylinder F S ∩ cylinder G T)
      = pathLaw μ X (cylinder F S) * pathLaw μ X (cylinder G T) := by
  have hΦ : Measurable fun ω => (fun n => X n ω : ℕ → α) := measurable_pi_lambda _ hX
  have hSmeas : MeasurableSet (cylinder F S) := measurableSet_cylinder F hS
  have hTmeas : MeasurableSet (cylinder G T) := measurableSet_cylinder G hT
  have hfS : Measurable fun ω => (fun i : F => X (i : ℕ) ω) :=
    measurable_pi_lambda _ fun i => hX (i : ℕ)
  have hfT : Measurable fun ω => (fun j : G => X (j : ℕ) ω) :=
    measurable_pi_lambda _ fun j => hX (j : ℕ)
  have hind : ProbabilityTheory.IndepSet
      ((fun ω => (fun i : F => X (i : ℕ) ω)) ⁻¹' S)
      ((fun ω => (fun j : G => X (j : ℕ) ω)) ⁻¹' T) μ :=
    (ProbabilityTheory.indepFun_iff_indepSet_preimage hfS hfT).mp
      (h_indep.indepFun_finset F G hFG hX) S T hS hT
  rw [pathLaw_def, Measure.map_apply hΦ (hSmeas.inter hTmeas), Measure.map_apply hΦ hSmeas,
    Measure.map_apply hΦ hTmeas, Set.preimage_inter]
  exact (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul (hfS hS) (hfT hT) μ).mp hind

end Independence

section ZeroOne

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
private theorem symmDiff_inter_subset {t t' s : Set (ℕ → α)} :
    symmDiff (t ∩ t') s ⊆ symmDiff t s ∪ symmDiff t' s := by
  intro x hx
  simp only [Set.mem_union, symmDiff, Set.sup_eq_union, Set.mem_union, Set.mem_sdiff,
    Set.mem_inter_iff] at hx ⊢
  tauto

/-- **The squaring identity.** Under an exchangeable path law in which cylinders over disjoint
index blocks are independent, an exchangeable event has measure equal to its own square.

The mechanism is the classical one: approximate the event by a cylinder over `[0, N)`, move that
cylinder onto the disjoint block `[N, 2N)` by `blockSwap N` — which fixes the event, being
exchangeable, and preserves the law — and let independence factor the two copies. -/
theorem measureReal_sq_of_exchangeableSigma {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : ExchangeableLaw ρ)
    (hprod : ∀ {F G : Finset ℕ}, Disjoint F G → ∀ {S : Set (∀ _i : F, α)}, MeasurableSet S →
      ∀ {T : Set (∀ _j : G, α)}, MeasurableSet T →
      ρ (cylinder (α := fun _ : ℕ => α) F S ∩ cylinder (α := fun _ : ℕ => α) G T)
        = ρ (cylinder (α := fun _ : ℕ => α) F S) * ρ (cylinder (α := fun _ : ℕ => α) G T))
    {s : Set (ℕ → α)} (hs : MeasurableSet[exchangeableSigma α] s) :
    ρ.real s = ρ.real s * ρ.real s := by
  have hs_meas : MeasurableSet s := MeasurableSet.ambient_of_exchangeableSigma hs
  by_contra hne
  set q := ρ.real s with hq
  have hdpos : 0 < |q - q * q| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set d := |q - q * q| with hd
  have h5 : 0 < d / 5 := by linarith
  obtain ⟨F, S, hS, hFS⟩ := exists_cylinder_measure_symmDiff_lt (ρ := ρ) hs_meas
    (ε := ENNReal.ofReal (d / 5)) (ENNReal.ofReal_pos.mpr h5)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range F
  set π := blockSwap N with hπ
  set t := cylinder (α := fun _ : ℕ => α) F S with ht
  have ht_meas : MeasurableSet t := measurableSet_cylinder F hS
  set t' := permReindex (α := α) π ⁻¹' t with ht'
  have ht'_meas : MeasurableSet t' := ht_meas.preimage (measurable_reindex π)
  -- the moved copy is a cylinder over the disjoint block `F.map π`
  have ht'_cyl : t' = cylinder (α := fun _ : ℕ => α) (F.map (Equiv.toEmbedding π))
      (pullMoved π F α ⁻¹' S) := preimage_permReindex_cylinder π F S
  -- the event is fixed, and the law is preserved, so the moved cylinder approximates it too
  have hs_inv : permReindex (α := α) π ⁻¹' s = s :=
    MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma hs (blockSwap_finite_support N)
  have hpres := hexch.measurePreserving_permReindex π
  have ht'_symm : ρ (symmDiff t' s) = ρ (symmDiff t s) := by
    have : symmDiff t' s = permReindex (α := α) π ⁻¹' symmDiff t s := by
      rw [Set.preimage_symmDiff, hs_inv]
    rw [this, hpres.measure_preimage (ht_meas.symmDiff hs_meas).nullMeasurableSet]
  -- pass to real-valued measures
  have htoReal : ∀ {A : Set (ℕ → α)}, ρ A < ENNReal.ofReal (d / 5) → ρ.real A < d / 5 := by
    intro A hA
    have := (ENNReal.toReal_lt_toReal (measure_ne_top ρ A) ENNReal.ofReal_ne_top).mpr hA
    rwa [ENNReal.toReal_ofReal h5.le] at this
  have h1 : ρ.real (symmDiff t s) < d / 5 := htoReal hFS
  have h2 : ρ.real (symmDiff t' s) < d / 5 := htoReal (ht'_symm ▸ hFS)
  have hbt : |ρ.real t - q| < d / 5 :=
    lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff ht_meas.nullMeasurableSet
      hs_meas.nullMeasurableSet) h1
  have hbt' : |ρ.real t' - q| < d / 5 :=
    lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff ht'_meas.nullMeasurableSet
      hs_meas.nullMeasurableSet) h2
  -- independence factors the intersection
  have hinter : ρ.real (t ∩ t') = ρ.real t * ρ.real t' := by
    rw [Measure.real, Measure.real, Measure.real, ht'_cyl, ht,
      hprod (disjoint_map_blockSwap hN) hS (hS.preimage (measurable_pullMoved π F)),
      ENNReal.toReal_mul]
  -- and the intersection still approximates the event
  have hIS : ρ.real (symmDiff (t ∩ t') s) < 2 * (d / 5) := by
    calc ρ.real (symmDiff (t ∩ t') s)
        ≤ ρ.real (symmDiff t s ∪ symmDiff t' s) :=
          measureReal_mono symmDiff_inter_subset (by finiteness)
      _ ≤ ρ.real (symmDiff t s) + ρ.real (symmDiff t' s) := measureReal_union_le _ _
      _ < 2 * (d / 5) := by linarith
  have hbi : |ρ.real (t ∩ t') - q| < 2 * (d / 5) :=
    lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff
      (ht_meas.inter ht'_meas).nullMeasurableSet hs_meas.nullMeasurableSet) hIS
  -- bounded by one, so the product is close to `q * q`
  have hone : ∀ A : Set (ℕ → α), ρ.real A ≤ 1 := fun A => by simp
  have hq1 : q ≤ 1 := hone s
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hone_t' : ρ.real t' ≤ 1 := hone t'
  have hprodclose : |ρ.real t * ρ.real t' - q * q| < 2 * (d / 5) := by
    have e : ρ.real t * ρ.real t' - q * q
        = (ρ.real t - q) * ρ.real t' + q * (ρ.real t' - q) := by ring
    calc |ρ.real t * ρ.real t' - q * q|
        ≤ |(ρ.real t - q) * ρ.real t'| + |q * (ρ.real t' - q)| := by
          rw [e]; exact abs_add_le _ _
      _ = |ρ.real t - q| * ρ.real t' + q * |ρ.real t' - q| := by
          rw [abs_mul, abs_mul, abs_of_nonneg measureReal_nonneg, abs_of_nonneg hq0]
      _ < 2 * (d / 5) := by
          nlinarith [hone_t', abs_nonneg (ρ.real t - q), abs_nonneg (ρ.real t' - q),
            measureReal_nonneg (μ := ρ) (s := t')]
  have : d < 4 * (d / 5) := by
    calc d = |q - q * q| := hd
      _ ≤ |q - ρ.real (t ∩ t')| + |ρ.real (t ∩ t') - q * q| := by
          have : q - q * q = (q - ρ.real (t ∩ t')) + (ρ.real (t ∩ t') - q * q) := by ring
          rw [this]; exact abs_add_le _ _
      _ < 2 * (d / 5) + 2 * (d / 5) := by
          rw [hinter] at hbi ⊢
          exact add_lt_add (by rwa [abs_sub_comm]) hprodclose
      _ = 4 * (d / 5) := by ring
  linarith

end ZeroOne

end Probability

end TauCeti
