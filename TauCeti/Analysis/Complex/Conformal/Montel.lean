/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Montel's selection theorem

A locally bounded family of holomorphic functions on an open set `Ω ⊆ ℂ` is a normal family: every
sequence drawn from it has a subsequence converging locally uniformly on `Ω`, and the limit is
again holomorphic. This completes layer **L1 (normal families / Montel)** of the conformal-mapping
roadmap, and is the compactness engine the Riemann mapping theorem runs on.

The equicontinuity half is already available in `Conformal/NormalFamilies.lean`
(`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, from Cauchy's estimate); what is added here is the
selection argument that turns it into a convergent subsequence.

The proof exhausts `Ω` by the compacts `exh Ω m`, restricts the family to each one as bounded
continuous functions, and applies Arzelà–Ascoli there. The usual next step is a diagonal argument;
instead we take the product over all levels at once. A product of the per-level compact closures is
compact by Tychonoff, and a countable product of metrizable spaces is first countable, so a single
application of `IsCompact.tendsto_subseq` yields one subsequence converging uniformly on *every*
level simultaneously. That is the diagonal argument, discharged by Mathlib's product machinery
rather than by hand.

The exhausting compacts are cut out by `∀ w ∈ Ωᶜ, 1/(m+1) ≤ dist z w` rather than by
`1/(m+1) ≤ infDist z Ωᶜ`. The two agree whenever `Ωᶜ` is nonempty, but `Metric.infDist` is
`ℝ`-valued and so must set `infDist z ∅ = 0`; the `infDist` form would therefore make every level
empty in the case `Ω = univ`. The `∀ w ∈ Ωᶜ` form is vacuously true there and needs no case split.

## Main results

* `TauCeti.montel` — a locally bounded family of holomorphic functions on an open set has a
  locally uniformly convergent subsequence, with holomorphic limit.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
which proves a Montel equicontinuity statement internally as a private lemma. **This file is
therefore a temporary shim**: once the corresponding Mathlib results land, this statement should be
backed by them — or deleted and its consumers refactored — rather than maintained as an independent
re-proof. What Tau Ceti adds at L1 is named, discoverable API, not first proof.

Note this is the **analytic** normal-families theorem; it is deliberately not routed through
Mathlib's `Analysis/LocallyConvex/Montel.lean` (`MontelSpace`), which is an unrelated notion.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Metric Filter Topology Set BoundedContinuousFunction

namespace TauCeti

variable {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}

/-- The `m`-th exhausting compact of `Ω`: points of norm at most `m` lying at distance at least
`1/(m+1)` from the complement. -/
private def exh (Ω : Set ℂ) (m : ℕ) : Set ℂ :=
  closedBall 0 m ∩ {z | ∀ w ∈ Ωᶜ, (1 : ℝ) / (m + 1) ≤ dist z w}

private theorem isCompact_exh (Ω : Set ℂ) (m : ℕ) : IsCompact (exh Ω m) := by
  refine (isCompact_closedBall (0 : ℂ) m).inter_right ?_
  have h : {z : ℂ | ∀ w ∈ Ωᶜ, (1 : ℝ) / (m + 1) ≤ dist z w}
      = ⋂ w ∈ Ωᶜ, {z : ℂ | (1 : ℝ) / (m + 1) ≤ dist z w} := by
    ext z; simp
  rw [h]
  exact isClosed_biInter fun w _ =>
    isClosed_le continuous_const (continuous_id.dist continuous_const)

private theorem exh_subset (Ω : Set ℂ) (m : ℕ) : exh Ω m ⊆ Ω := by
  rintro z ⟨-, hz⟩
  by_contra h
  have h1 := hz z h
  simp only [dist_self] at h1
  have : (0:ℝ) < 1 / (m + 1) := by positivity
  linarith

/-- Every point of an open `Ω` lies in the interior of some exhausting compact, which is what makes
uniform convergence on the levels give *locally* uniform convergence on `Ω`. -/
private theorem exists_ball_subset_exh (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    ∃ m, ∃ r > 0, ball z r ⊆ exh Ω m := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  obtain ⟨m, hm⟩ := exists_nat_gt (max (‖z‖ + 1) (2 / ε))
  refine ⟨m, min 1 (ε / 2), lt_min one_pos (by positivity), fun y hy => ?_⟩
  have hylt : dist y z < min 1 (ε / 2) := mem_ball.mp hy
  have h1 : ‖z‖ + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
  have h2 : 2 / ε < m := lt_of_le_of_lt (le_max_right _ _) hm
  constructor
  · have : ‖y‖ ≤ ‖z‖ + dist y z := by
      simpa [dist_eq_norm] using norm_le_norm_add_norm_sub' y z
    have hle : dist y z ≤ 1 := (lt_min_iff.mp hylt).1.le
    simp only [mem_closedBall, dist_zero_right]
    linarith
  · intro w hw
    by_contra hlt
    push Not at hlt
    have hdyw : dist y w < 1 / (m + 1) := hlt
    have hmpos : (0:ℝ) < m := lt_of_le_of_lt (by positivity) h1
    -- `1/(m+1) < ε/2`, so `w` would be within `ε` of `z`, contradicting `ball z ε ⊆ Ω`
    have hkey : 1 / ((m : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at h2
      nlinarith
    have : dist z w < ε := by
      have := dist_triangle z y w
      have hzy : dist z y < ε / 2 := by
        rw [dist_comm]
        exact lt_of_lt_of_le hylt (min_le_right _ _)
      linarith
    exact hw (hball (mem_ball.mpr (by rwa [dist_comm])))

/-- The restriction of a family member to a compact `K`, as a bounded continuous function. -/
private noncomputable def restr (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (n : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    (K →ᵇ ℂ) :=
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  mkOfCompact ⟨K.restrict (F n), (((hF n).continuousOn).mono hKΩ).restrict⟩

/-- **Per-level Arzelà–Ascoli.** On a compact `K ⊆ Ω` the restricted family has compact closure. -/
private theorem isCompact_closure_range (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    IsCompact (closure (Set.range (restr hF hK hKΩ))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  classical
  obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb K hKΩ hK
  refine arzela_ascoli (closedBall (0 : ℂ) C) (isCompact_closedBall _ _) _ (fun f x hf => ?_) ?_
  · obtain ⟨n, rfl⟩ := hf
    simpa [restr] using hC n x.1 x.2
  · have hbase : Equicontinuous (fun n => ⇑(restr hF hK hKΩ n)) :=
      (equicontinuous_restrict_iff F).mpr ((hb.equicontinuousOn hΩ hF).mono hKΩ)
    have hchoice : ∀ x : ↥(Set.range (restr hF hK hKΩ)), ∃ n,
        restr hF hK hKΩ n = (x : K →ᵇ ℂ) := fun x => x.2
    choose σ hσ using hchoice
    have heq : (fun x : ↥(Set.range (restr hF hK hKΩ)) => ⇑(x : K →ᵇ ℂ))
        = (fun n => ⇑(restr hF hK hKΩ n)) ∘ σ := by
      funext x
      rw [Function.comp_apply, hσ x]
    rw [heq]
    exact hbase.comp σ

/-- **Montel's selection theorem.** A locally bounded family of holomorphic functions on an open
set `Ω ⊆ ℂ` is normal: every sequence from it has a subsequence converging locally uniformly on
`Ω`, and the limit is holomorphic.

The local boundedness hypothesis cannot be dropped: `F n z = n` is a family of holomorphic
functions on any `Ω` with no locally uniformly convergent subsequence. -/
theorem montel (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ g Ω ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
  classical
  letI : ∀ m, CompactSpace (exh Ω m) := fun m => isCompact_iff_compactSpace.mp (isCompact_exh Ω m)
  set R : ∀ m : ℕ, ℕ → (exh Ω m →ᵇ ℂ) :=
    fun m => restr hF (isCompact_exh Ω m) (exh_subset Ω m) with hR
  -- one extraction in the product over all levels replaces the diagonal argument
  have hcpt : IsCompact (Set.univ.pi fun m => closure (Set.range (R m))) :=
    isCompact_univ_pi fun m =>
      isCompact_closure_range hΩ hF hb (isCompact_exh Ω m) (exh_subset Ω m)
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq (x := fun n m => R m n)
    (fun n => fun m _ => subset_closure ⟨n, rfl⟩)
  -- level by level, the subsequence converges uniformly
  have hlevel : ∀ m, TendstoUniformlyOn (fun n => F (φ n)) (fun z => if hz : z ∈ exh Ω m then
      a m ⟨z, hz⟩ else 0) atTop (exh Ω m) := by
    intro m
    have hco : Tendsto (fun n => R m (φ n)) atTop (𝓝 (a m)) :=
      ((continuous_apply m).continuousAt.tendsto).comp hconv
    have huc : TendstoUniformly (fun n => ⇑(R m (φ n))) (⇑(a m)) atTop :=
      tendsto_iff_tendstoUniformly.mp hco
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hlim : ((fun z => if hz : z ∈ exh Ω m then a m ⟨z, hz⟩ else 0) ∘
        ((↑) : exh Ω m → ℂ)) = ⇑(a m) := by
      funext x
      simp [x.2]
    rw [hlim]
    exact huc
  -- pointwise limits agree across levels, so they glue to a single `g`
  set g : ℂ → ℂ := fun z => if hz : ∃ m, z ∈ exh Ω m then a (Nat.find hz) ⟨z, Nat.find_spec hz⟩
    else 0 with hg
  have hptw : ∀ (m : ℕ) (z : ℂ) (hz : z ∈ exh Ω m),
      Tendsto (fun n => F (φ n) z) atTop (𝓝 (a m ⟨z, hz⟩)) := by
    intro m z hz
    have := (hlevel m).tendsto_at hz
    simpa [hz] using this
  have hagree : ∀ m, ∀ z (hz : z ∈ exh Ω m), g z = a m ⟨z, hz⟩ := by
    intro m z hz
    have hex : ∃ m, z ∈ exh Ω m := ⟨m, hz⟩
    have h1 := hptw (Nat.find hex) z (Nat.find_spec hex)
    have h2 := hptw m z hz
    simp only [hg, dif_pos hex]
    exact tendsto_nhds_unique h1 h2
  have hlevel' : ∀ m, TendstoUniformlyOn (fun n => F (φ n)) g atTop (exh Ω m) := by
    intro m
    refine (hlevel m).congr_right (fun z hz => ?_)
    simp [hagree m z hz, hz]
  -- levels are neighbourhoods, so this is locally uniform convergence on `Ω`
  have hloc : TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
    intro u hu x hx
    obtain ⟨m, r, hr, hball⟩ := exists_ball_subset_exh hΩ hx
    refine ⟨Ω ∩ ball x r, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr), ?_⟩
    filter_upwards [(hlevel' m) u hu] with n hn y hy
    exact hn y (hball hy.2)
  exact ⟨φ, g, hφ, hloc.differentiableOn (Eventually.of_forall fun n => hF (φ n)) hΩ, hloc⟩

end TauCeti
