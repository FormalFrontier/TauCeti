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

private theorem symmDiff_inter_subset {Ω : Type*} {t t' s : Set Ω} :
    symmDiff (t ∩ t') s ⊆ symmDiff t s ∪ symmDiff t' s := by
  intro x hx
  simp only [Set.mem_union, symmDiff, Set.sup_eq_union, Set.mem_union, Set.mem_sdiff,
    Set.mem_inter_iff] at hx ⊢
  tauto

/-- **A measure-preserving reindexing does not change how well a set approximates an invariant
event.** If `s` is fixed by the reindexing, then `π⁻¹(t)` differs from `s` by exactly the
`π`-preimage of `t ∆ s`, whose measure is unchanged. -/
private lemma measure_symmDiff_preimage_permReindex {ρ : Measure (ℕ → α)}
    (hexch : ExchangeableLaw ρ) (π : Equiv.Perm ℕ) {t s : Set (ℕ → α)}
    (ht : NullMeasurableSet t ρ) (hs : NullMeasurableSet s ρ)
    (hs_inv : permReindex (α := α) π ⁻¹' s = s) :
    ρ (symmDiff (permReindex (α := α) π ⁻¹' t) s) = ρ (symmDiff t s) := by
  have h : symmDiff (permReindex (α := α) π ⁻¹' t) s
      = permReindex (α := α) π ⁻¹' symmDiff t s := by
    rw [Set.preimage_symmDiff, hs_inv]
  rw [h, (hexch.measurePreserving_permReindex π).measure_preimage (ht.symmDiff hs)]

/-- **A product estimate.** If `x` and `y` each lie within `e` of `q`, with `y` and `q` in
`[0, 1]`, then `x · y` lies within `2e` of `q²`: the error splits as `(x - q)·y + q·(y - q)`. -/
private lemma abs_mul_sub_mul_self_lt {x y q e : ℝ} (hx : |x - q| < e) (hy : |y - q| < e)
    (hy1 : y ≤ 1) (hy0 : 0 ≤ y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : |x * y - q * q| < 2 * e := by
  have e' : x * y - q * q = (x - q) * y + q * (y - q) := by ring
  calc |x * y - q * q| ≤ |(x - q) * y| + |q * (y - q)| := by rw [e']; exact abs_add_le _ _
    _ = |x - q| * y + q * |y - q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg hq0]
    _ < 2 * e := by nlinarith [abs_nonneg (x - q), abs_nonneg (y - q)]

/-- **Two close sets have a close intersection**, since `(A ∩ B) ∆ s` sits inside the union of
the two symmetric differences. -/
private lemma abs_measureReal_inter_sub_lt {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω}
    [IsFiniteMeasure ρ] {A B s : Set Ω} (hA : NullMeasurableSet A ρ) (hB : NullMeasurableSet B ρ)
    (hs : NullMeasurableSet s ρ)
    {e : ℝ} (h1 : ρ.real (symmDiff A s) < e) (h2 : ρ.real (symmDiff B s) < e) :
    |ρ.real (A ∩ B) - ρ.real s| < 2 * e := by
  have hIS : ρ.real (symmDiff (A ∩ B) s) < 2 * e :=
    calc ρ.real (symmDiff (A ∩ B) s)
        ≤ ρ.real (symmDiff A s ∪ symmDiff B s) :=
          measureReal_mono symmDiff_inter_subset (by finiteness)
      _ ≤ ρ.real (symmDiff A s) + ρ.real (symmDiff B s) := measureReal_union_le _ _
      _ < 2 * e := by linarith
  exact lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hB) hs) hIS

/-- **Closing the gap.** If `q` and `q²` are each within `e` of a common value `z`, they are
within `2e` of each other. -/
private lemma abs_sub_mul_self_lt_of_close {q z e : ℝ} (h1 : |q - z| < e) (h2 : |z - q * q| < e) :
    |q - q * q| < 2 * e :=
  have hsplit : q - q * q = (q - z) + (z - q * q) := by ring
  calc |q - q * q| ≤ |q - z| + |z - q * q| := by rw [hsplit]; exact abs_add_le _ _
    _ < 2 * e := by linarith

/-- **The approximation squeeze.** Suppose `t` and `t'` each approximate `s` to within `e` in
symmetric difference, and the measure of their intersection factors as the product of their
measures. Then `ρ.real s` lies within `4e` of its own square.

Two estimates meet at the factorization: `t ∩ t'` is within `2e` of `s`, while the product
`ρ.real t * ρ.real t'` is within `2e` of `(ρ.real s)²`. Nothing here concerns exchangeability or
cylinders — it is the arithmetic half of `measureReal_sq_of_exchangeableSigma`, and holds on any
probability space. -/
private lemma abs_measureReal_sub_mul_self_lt_of_symmDiff_lt {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {t t' s : Set Ω}
    (ht : NullMeasurableSet t ρ) (ht' : NullMeasurableSet t' ρ) (hs : NullMeasurableSet s ρ)
    {e : ℝ} (h1 : ρ.real (symmDiff t s) < e) (h2 : ρ.real (symmDiff t' s) < e)
    (hinter : ρ.real (t ∩ t') = ρ.real t * ρ.real t') :
    |ρ.real s - ρ.real s * ρ.real s| < 4 * e := by
  have hbt : |ρ.real t - ρ.real s| < e :=
    lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff ht hs) h1
  have hbt' : |ρ.real t' - ρ.real s| < e :=
    lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff ht' hs) h2
  have hbi : |ρ.real (t ∩ t') - ρ.real s| < 2 * e :=
    abs_measureReal_inter_sub_lt ht ht' hs h1 h2
  have hprodclose : |ρ.real t * ρ.real t' - ρ.real s * ρ.real s| < 2 * e :=
    abs_mul_sub_mul_self_lt hbt hbt' (by simp) measureReal_nonneg measureReal_nonneg (by simp)
  have hgap := abs_sub_mul_self_lt_of_close (q := ρ.real s) (z := ρ.real (t ∩ t')) (e := 2 * e)
    (by rwa [abs_sub_comm]) (hinter ▸ hprodclose)
  linarith

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
  set d := |q - q * q| with hd
  have h5 : 0 < d / 5 := by
    have : 0 < d := hd ▸ abs_pos.mpr (sub_ne_zero.mpr hne); linarith
  obtain ⟨F, S, hS, hFS⟩ := exists_cylinder_measure_symmDiff_lt (ρ := ρ) hs_meas
    (ε := ENNReal.ofReal (d / 5)) (ENNReal.ofReal_pos.mpr h5)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range F
  set π := blockSwap N with hπ
  set t := cylinder (α := fun _ : ℕ => α) F S with ht
  have ht_meas : MeasurableSet t := MeasurableSet.cylinder (α := fun _ : ℕ => α) F hS
  set t' := permReindex (α := α) π ⁻¹' t with ht'
  have ht'_meas : MeasurableSet t' := ht_meas.preimage (measurable_reindex π)
  have hsN := hs_meas.nullMeasurableSet (μ := ρ)
  have htN := ht_meas.nullMeasurableSet (μ := ρ)
  have ht'N := ht'_meas.nullMeasurableSet (μ := ρ)
  -- the moved copy is a cylinder over the disjoint block `F.map π`
  have ht'_cyl : t' = cylinder (α := fun _ : ℕ => α) (F.map (Equiv.toEmbedding π))
      (pullMoved π F α ⁻¹' S) := preimage_permReindex_cylinder π F S
  -- the event is fixed, and the law is preserved, so the moved cylinder approximates it too
  have hs_inv : permReindex (α := α) π ⁻¹' s = s :=
    MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma hs (blockSwap_finite_support N)
  have ht'_symm : ρ (symmDiff t' s) = ρ (symmDiff t s) :=
    measure_symmDiff_preimage_permReindex hexch π htN hsN hs_inv
  -- pass to real-valued measures
  have h1 : ρ.real (symmDiff t s) < d / 5 := ENNReal.toReal_lt_of_lt_ofReal hFS
  have h2 : ρ.real (symmDiff t' s) < d / 5 := ENNReal.toReal_lt_of_lt_ofReal (ht'_symm ▸ hFS)
  -- independence factors the intersection
  have hinter : ρ.real (t ∩ t') = ρ.real t * ρ.real t' := by
    rw [Measure.real, Measure.real, Measure.real, ht'_cyl, ht,
      hprod (disjoint_map_blockSwap hN) hS (hS.preimage (measurable_pullMoved π F)),
      ENNReal.toReal_mul]
  -- two copies within `d / 5` of `s` and a factoring intersection force `d < 4 * (d / 5)`
  have hfinal := abs_measureReal_sub_mul_self_lt_of_symmDiff_lt htN ht'N hsN h1 h2 hinter
  rw [← hq, ← hd] at hfinal
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
