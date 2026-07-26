/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Sigma
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
public import TauCeti.Probability.Exchangeability.IID
-- Public: `cylinder` appears in the hypothesis of `measure_eq_zero_or_one_of_exchangeableSigma`.
public import Mathlib.MeasureTheory.Constructions.Cylinders
-- Non-public: used only inside proofs.
import TauCeti.Algebra.GroupAction.FiniteSupportPerm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Probability.Independence.ZeroOne

/-!
# The Hewitt–Savage zero-one law

For an i.i.d. sequence, the exchangeable (symmetric) σ-algebra on path space is trivial:
every exchangeable event has probability `0` or `1` (`hewittSavage_trivial_of_iIndep`).

Kolmogorov's tail zero-one law does not subsume this. Tail triviality needs only independence,
whereas the symmetric σ-algebra can contain events that are not tail events: for a measurable `B`
with `B ≠ ∅` and `B ≠ Set.univ`, the event `{p | ∃ n, p n ∈ B}` is invariant under every
permutation of the coordinates, yet is not a tail event — some path witnesses it only at index
`0`, and changing that one coordinate moves the path out of the event, whereas tail events are
invariant under modification of finitely many coordinates. The qualification matters: for
`B = ∅` or `B = Set.univ`, or a one-point coordinate space, the event collapses to `∅` or
`Set.univ` and is a tail event after all.

`tail_le_exchangeableSigma` records the inclusion of the two σ-algebras formally; its strictness
is not formalized here.

Identical distribution enters only as the route to exchangeability of the path law: it is what
`Exchangeable.of_iIndepFun_identDistrib` consumes, and exchangeability is what the argument below
actually uses. It is sufficient for that, not necessary for the conclusion — the abstract form
`measure_eq_zero_or_one_of_exchangeableSigma` assumes an exchangeable law and the disjoint-block
product formula directly, and mentions identical distribution nowhere. A deterministic
independent sequence with distinct constant coordinates, for instance, is not identically
distributed yet has a Dirac path law, under which every event is trivial.

## Main results

* `hewittSavage_trivial_of_iIndep` — the zero-one law, from `iIndepFun` and `IdentDistrib`.
* `measure_eq_zero_or_one_of_exchangeableSigma` — the abstract form, over an exchangeable path law
  in which cylinders over disjoint index blocks are independent.

Everything else in this file is `private` proof infrastructure: the block permutation, the
reindexed-cylinder change of variables, the cylinder approximation, the disjoint-block product
formula, and the squaring identity.

## The argument

Approximate an exchangeable event by a cylinder over `[0, N)`, then move that cylinder onto the
disjoint block `[N, 2N)`. The mover is `blockSwap N`, the half-swap of `Fin (N + N)` transported
to `ℕ`: it is finitely supported, hence admissible for `exchangeableSigma`, so it fixes the event
while preserving the law. Independence then factors the event against its own moved copy, and
letting the approximation tighten gives `q = q²`.

The independence step lives on the source space rather than on path space —
`iIndepFun.indepFun_finset` applies to the coordinate tuples of `X`, and `Measure.map_apply`
transfers the resulting identity to `pathLaw μ X`. Stating it directly for a path-space measure
would first need a lemma transferring `iIndepFun` to the coordinate projections.

This discharges the Layer 2 target `hewittSavage_trivial_of_iIndep` of
`TauCetiRoadmap/Exchangeability/README.md`, and supplies the Layer 2 input the roadmap records for
the Layer 6 extreme-point corollary (the extreme exchangeable laws are exactly the i.i.d. laws).

## References

* Edwin Hewitt and Leonard J. Savage, *Symmetric measures on Cartesian products*, Transactions of
  the American Mathematical Society **80** (1955), 470–501, <https://doi.org/10.2307/1992999> — the
  original theorem, and the source the roadmap names for this target.
* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.

No material is adapted from `cameronfreer/exchangeability`: that formalization does not carry this
theorem, and the proof here is assembled from Mathlib's cylinder, approximation, and independence
API.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The finitely supported permutation of `ℕ` that swaps the block `[0, N)` with `[N, 2N)`
pointwise and fixes everything from `2 * N` on: Mathlib's half-swap `finAddFlip` on `Fin (N + N)`,
transported to `ℕ` along the value embedding. -/
private def blockSwap (N : ℕ) : Equiv.Perm ℕ :=
  Equiv.Perm.viaFintypeEmbedding (finAddFlip (m := N) (n := N)) ⟨Fin.val, Fin.val_injective⟩

private theorem blockSwap_apply_of_lt {N i : ℕ} (hi : i < N) : blockSwap N i = N + i := by
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.castAdd N ⟨i, hi⟩) = i := rfl
  rw [blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, finAddFlip_apply_castAdd]
  rfl

private theorem blockSwap_apply_of_le {N n : ℕ} (hn : N + N ≤ n) : blockSwap N n = n := by
  refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact absurd j.isLt (not_lt.mpr hn)

/-- `blockSwap N` carries any index block inside `[0, N)` off itself: the moved copy lands in
`[N, 2N)`. This is the disjointness the independence step consumes. -/
private theorem disjoint_map_blockSwap {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range N) :
    Disjoint F (F.map (Equiv.toEmbedding (blockSwap N))) := by
  rw [Finset.disjoint_left]
  intro a haF hamem
  obtain ⟨b, hbF, hb⟩ := Finset.mem_map.mp hamem
  have hbN : b < N := Finset.mem_range.mp (hF hbF)
  have haN : a < N := Finset.mem_range.mp (hF haF)
  rw [Equiv.coe_toEmbedding, blockSwap_apply_of_lt hbN] at hb
  omega

private theorem blockSwap_finite_support (N : ℕ) :
    (MulAction.fixedBy ℕ (blockSwap N))ᶜ.Finite :=
  finite_compl_fixedBy_of_eventually_eq_self ⟨N + N, fun _ hn => blockSwap_apply_of_le hn⟩

section Cylinder

variable {α : Type*}

/-- Read a block indexed by the moved index set `F.map π` back onto `F`, along `π`. This is the
change of variables that turns a `π`-reindexed cylinder over `F` into a cylinder over `F.map π`. -/
private def pullMoved (π : Equiv.Perm ℕ) (F : Finset ℕ) (α : Type*)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) : ∀ _i : F, α :=
  fun i => g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩

@[simp]
private theorem pullMoved_apply (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) (i : F) :
    pullMoved π F α g i = g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩ :=
  rfl

/-- Reindexing a cylinder over `F` by `π` is a cylinder over the moved index set `F.map π`: both
sides say that the coordinates `p (π i)`, for `i ∈ F`, lie in `S`. -/
private theorem preimage_permReindex_cylinder (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (S : Set (∀ _i : F, α)) :
    permReindex (α := α) π ⁻¹' cylinder F S
      = cylinder (F.map (Equiv.toEmbedding π)) (pullMoved π F α ⁻¹' S) :=
  rfl

private theorem measurable_pullMoved [MeasurableSpace α] (π : Equiv.Perm ℕ) (F : Finset ℕ) :
    Measurable (pullMoved π F α) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Every measurable path-space event is approximated, in measure, by a measurable cylinder over a
finite index set. -/
private theorem exists_cylinder_measure_symmDiff_lt [MeasurableSpace α] {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] {s : Set (ℕ → α)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset ℕ) (S : Set (∀ _i : F, α)),
      MeasurableSet S ∧ ρ (symmDiff (cylinder F S) s) < ε := by
  have hcov : ∃ D : Set (Set (ℕ → α)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℕ => α) ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · rintro u (rfl : u = Set.univ)
      exact univ_mem_measurableCylinders (fun _ : ℕ => α)
    · simp
  obtain ⟨t, ht_mem, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ρ)
    isSetRing_measurableCylinders hcov generateFrom_measurableCylinders.symm hs hε
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht_mem
  exact ⟨F, S, hS, ht⟩

end Cylinder

section Independence

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Cylinders over **disjoint** index blocks are independent events under the path law of an
independent family. This is the step that turns the disjointness produced by `blockSwap` into a
product formula. -/
private theorem measure_pathLaw_inter_cylinder_of_disjoint {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : ∀ n, AEMeasurable (X n) μ)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    {F G : Finset ℕ} (hFG : Disjoint F G)
    {S : Set (∀ _i : F, α)} (hS : MeasurableSet S)
    {T : Set (∀ _j : G, α)} (hT : MeasurableSet T) :
    pathLaw μ X (cylinder F S ∩ cylinder G T)
      = pathLaw μ X (cylinder F S) * pathLaw μ X (cylinder G T) := by
  letI := h_indep.isProbabilityMeasure
  have hΦ : AEMeasurable (fun ω => (fun n => X n ω : ℕ → α)) μ := aemeasurable_pi_lambda _ hX
  have hSmeas : MeasurableSet (cylinder F S) :=
    MeasurableSet.cylinder (α := fun _ : ℕ => α) F hS
  have hTmeas : MeasurableSet (cylinder G T) :=
    MeasurableSet.cylinder (α := fun _ : ℕ => α) G hT
  rw [pathLaw_def, Measure.map_apply_of_aemeasurable hΦ (hSmeas.inter hTmeas),
    Measure.map_apply_of_aemeasurable hΦ hSmeas, Measure.map_apply_of_aemeasurable hΦ hTmeas,
    Set.preimage_inter]
  exact (h_indep.indepFun_finset₀ F G hFG hX).measure_inter_preimage_eq_mul S T hS hT

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
private theorem measureReal_sq_of_exchangeableSigma {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
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
  have ht_meas : MeasurableSet t := MeasurableSet.cylinder (α := fun _ : ℕ => α) F hS
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

/-- **Zero-one law for exchangeable events**, abstract form: an exchangeable path law in which
cylinders over disjoint index blocks are independent gives every exchangeable event measure `0`
or `1`. -/
theorem measure_eq_zero_or_one_of_exchangeableSigma {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : ExchangeableLaw ρ)
    (hprod : ∀ {F G : Finset ℕ}, Disjoint F G → ∀ {S : Set (∀ _i : F, α)}, MeasurableSet S →
      ∀ {T : Set (∀ _j : G, α)}, MeasurableSet T →
      ρ (cylinder (α := fun _ : ℕ => α) F S ∩ cylinder (α := fun _ : ℕ => α) G T)
        = ρ (cylinder (α := fun _ : ℕ => α) F S) * ρ (cylinder (α := fun _ : ℕ => α) G T))
    {s : Set (ℕ → α)} (hs : MeasurableSet[exchangeableSigma α] s) :
    ρ s = 0 ∨ ρ s = 1 := by
  have hs_meas : MeasurableSet s := MeasurableSet.ambient_of_exchangeableSigma hs
  have hsq := measureReal_sq_of_exchangeableSigma hexch hprod hs
  have htop : ρ s ≠ ⊤ := measure_ne_top ρ s
  have hE : ρ (s ∩ s) = ρ s * ρ s := by
    rw [Set.inter_self]
    refine (ENNReal.toReal_eq_toReal_iff' htop (ENNReal.mul_ne_top htop htop)).mp ?_
    rw [ENNReal.toReal_mul]
    exact hsq
  exact ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self
    ((ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hs_meas hs_meas ρ).mpr hE)

end ZeroOne

section HewittSavage

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The Hewitt–Savage zero-one law.** For an i.i.d. sequence, the exchangeable (symmetric)
σ-algebra on path space is trivial: every exchangeable event has probability `0` or `1`.

Kolmogorov's tail zero-one law does not subsume this: tail triviality needs only independence,
whereas the symmetric σ-algebra can contain non-tail events — for measurable `B` with `B ≠ ∅` and
`B ≠ Set.univ`, the event `{p | ∃ n, p n ∈ B}` is permutation-invariant but not a tail event
(see the module docstring). Identical distribution is used here to obtain exchangeability of the
path law, which is what the argument consumes; it is not claimed to be necessary for the
conclusion — `measure_eq_zero_or_one_of_exchangeableSigma` assumes exchangeability directly. -/
theorem hewittSavage_trivial_of_iIndep {μ : Measure Ω} {X : ℕ → Ω → α}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    {s : Set (ℕ → α)} (hs : MeasurableSet[exchangeableSigma α] s) :
    pathLaw μ X s = 0 ∨ pathLaw μ X s = 1 := by
  letI := h_indep.isProbabilityMeasure
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hident i).aemeasurable_fst
  haveI : IsProbabilityMeasure (pathLaw μ X) := by
    rw [pathLaw_def]
    exact Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ hX)
  have hexch : ExchangeableLaw (pathLaw μ X) :=
    (exchangeable_iff_exchangeableLaw_pathLaw hX).mp
      (Exchangeable.of_iIndepFun_identDistrib h_indep hident)
  exact measure_eq_zero_or_one_of_exchangeableSigma hexch
    (fun {_F _G} hFG {_S} hS {_T} hT =>
      measure_pathLaw_inter_cylinder_of_disjoint hX h_indep hFG hS hT) hs

end HewittSavage

end Probability

end TauCeti
