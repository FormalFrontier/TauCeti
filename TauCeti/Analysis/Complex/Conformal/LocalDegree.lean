/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.Conformal.Rouche
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The open-mapping degree

The local mapping theorem: near a point `z₀` at which `f - f z₀` vanishes to order `n`, every
value `w` close enough to `f z₀` is attained exactly `n` times, counted with multiplicity. This is
the third target of layer **L0 (the local-mapping engine)** of the conformal-mapping roadmap.

This is the quantitative refinement of Mathlib's open mapping theorem
(`Complex.AnalyticOnNhd.is_constant_or_isOpenMap`, **consumed** here, not reproved). That theorem
says the image of an open set is open — every nearby value is attained *at least* once. The degree
says how many times: exactly `n`, so `f` is locally an `n`-to-one branched cover, behaving like
`z ↦ z ^ n` up to a change of coordinates.

The proof is a Rouché comparison. On a circle small enough that `z₀` is the only solution of
`f z = f z₀` inside, `‖f - f z₀‖` attains a positive minimum `δ`; for `‖w - f z₀‖ < δ` the
difference `(f - f z₀) - (f - w) = w - f z₀` is smaller than `‖f - f z₀‖` there, so Rouché equates
the zero counts of `f - w` and `f - f z₀` inside. The latter count collapses to the single order at
`z₀`, because `z₀` is its only zero in the disc.

Adding the hypothesis that `f'` is zero-free on the punctured disc upgrades the count with
multiplicity to the sharper classical statement: for `w ≠ f z₀` the `n` solutions are *distinct*
and each is a *simple* zero of `f - w`.

That refinement yields the local injectivity criterion. If `f' z₀ = 0` while `f` is non-constant
near `z₀`, the degree is at least `2`, so some nearby value is attained twice and `f` is not
injective on the disc. The converse — that `f' z₀ ≠ 0` makes `f` injective near `z₀` — is Mathlib's
inverse function theorem (`HasStrictDerivAt.eventually_left_inverse`) and is consumed, not reproved.

## Main results

* `TauCeti.localDegree` — the count form, with the radius supplied by the caller.
* `TauCeti.localDegree_card` — the distinct-and-simple form.
* `TauCeti.exists_localDegree` — the textbook form: if `z₀` is an isolated solution of `f z = f z₀`,
  suitable radii exist.
* `TauCeti.not_injOn_of_deriv_eq_zero` — a critical point destroys local injectivity.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0 material
overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the
in-progress human-curated Riemann-mapping-theorem effort. **This file is therefore a temporary
shim**: once corresponding Mathlib lemmas land, these statements should be backed by them — or
deleted and their consumers refactored — rather than maintained as independent re-proofs. What Tau
Ceti adds at L0 is named, discoverable API, not first proof.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §3.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IV §7.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

/-- If `z₀` is the only zero of `f` in the open disc, the total zero count collapses to the order
of vanishing at `z₀`. -/
private lemma count_eq_single {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R)
    (hone : ∀ z ∈ ball c R, z ≠ z₀ → f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = analyticOrderNatAt f z₀ := by
  classical
  have hsub : (({z₀} : Finset ℂ) : Set ℂ) ⊆ ball c R := by simpa using hz₀
  have h1 : ball c R ∩ Function.support (fun z => analyticOrderNatAt f z)
      ⊆ (({z₀} : Finset ℂ) : Set ℂ) := by
    rintro z ⟨hzb, hzs⟩
    simp only [Function.mem_support, ne_eq] at hzs
    by_contra hne
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hne
    exact hzs (by
      simp [analyticOrderNatAt,
        (hf z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2 (hone z hzb hne)])
  rw [finsum_mem_eq_sum_of_subset _ h1 hsub, Finset.sum_singleton]

/-- **The open-mapping degree**, count form. If `f` is holomorphic on the closed disc `C(z₀, r)`
and `z₀` is the only solution there of `f z = f z₀`, then every `w` close enough to `f z₀` is
attained in the open disc exactly as often as `f z₀` is — that is, `analyticOrderNatAt` of
`f - f z₀` at `z₀` times, counted with multiplicity. -/
theorem localDegree {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hiso : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀) :
    ∃ δ > 0, ∀ w : ℂ, ‖w - f z₀‖ < δ →
      (∑ᶠ z ∈ ball z₀ r, analyticOrderNatAt (fun ζ => f ζ - w) z)
        = analyticOrderNatAt (fun ζ => f ζ - f z₀) z₀ := by
  have hcpt : IsCompact (sphere z₀ r) := isCompact_sphere _ _
  have hsne : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hcont : ContinuousOn (fun z => ‖f z - f z₀‖) (sphere z₀ r) :=
    (((hf.continuousOn).mono sphere_subset_closedBall).sub continuousOn_const).norm
  obtain ⟨u, hu, humin⟩ := hcpt.exists_isMinOn hsne hcont
  have hzne : ∀ z ∈ sphere z₀ r, z ≠ z₀ := by
    intro z hz h
    rw [h] at hz
    simp only [mem_sphere, dist_self] at hz
    linarith
  have hδ : 0 < ‖f u - f z₀‖ :=
    norm_sub_pos_iff.mpr (hiso u (sphere_subset_closedBall hu) (hzne u hu))
  refine ⟨‖f u - f z₀‖, hδ, fun w hw => ?_⟩
  have hA0 : AnalyticOnNhd ℂ (fun ζ => f ζ - f z₀) (closedBall z₀ r) :=
    hf.sub analyticOnNhd_const
  have hAw : AnalyticOnNhd ℂ (fun ζ => f ζ - w) (closedBall z₀ r) :=
    hf.sub analyticOnNhd_const
  have hs : ∀ z ∈ sphere z₀ r, ‖(f z - f z₀) - (f z - w)‖ < ‖f z - f z₀‖ := by
    intro z hz
    have he : (f z - f z₀) - (f z - w) = w - f z₀ := by ring
    rw [he]
    exact lt_of_lt_of_le hw (humin hz)
  refine (rouche hr hA0 hAw hs).symm.trans
    (count_eq_single hA0 (mem_ball_self hr) (fun z hz hzn => ?_))
  exact sub_ne_zero.mpr (hiso z (ball_subset_closedBall hz) hzn)

/-- When every zero in the disc is simple, the count with multiplicity is the number of *distinct*
zeros. -/
private lemma count_eq_ncard {A : ℂ → ℂ} {c : ℂ} {R : ℝ} (hA : AnalyticOnNhd ℂ A (closedBall c R))
    (hsimple : ∀ z ∈ ball c R, A z = 0 → analyticOrderNatAt A z = 1) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt A z) = {z ∈ ball c R | A z = 0}.ncard := by
  classical
  set S := (MeromorphicOn.divisor_ball_support_finite hA.meromorphicOn).toFinset with hS
  have hAb : AnalyticOnNhd ℂ A (ball c R) := hA.mono ball_subset_closedBall
  have hmemS : ∀ z ∈ ball c R, analyticOrderNatAt A z ≠ 0 → z ∈ S := by
    intro z hz hne
    have : MeromorphicOn.divisor A (ball c R) z ≠ 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAb hz]
      cases h : analyticOrderAt A z with
      | top => simp [analyticOrderNatAt, h] at hne
      | coe n => simpa [analyticOrderNatAt, h] using hne
    simpa [hS, Set.Finite.mem_toFinset] using this
  have hsub : (S : Set ℂ) ⊆ ball c R := fun z hz =>
    (MeromorphicOn.divisor A (ball c R)).supportWithinDomain
      (by simpa [hS, Set.Finite.mem_toFinset] using hz)
  set T := S.filter (fun z => A z = 0) with hT
  have hZT : {z ∈ ball c R | A z = 0} = (T : Set ℂ) := by
    ext z
    simp only [Set.mem_setOf_eq, hT, Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hzb, hz0⟩
      exact ⟨hmemS z hzb (by rw [hsimple z hzb hz0]; norm_num), hz0⟩
    · rintro ⟨hzS, hz0⟩
      exact ⟨hsub (by simpa using hzS), hz0⟩
  have hcard : ((T : Set ℂ)).ncard = T.card := by simp
  rw [hZT, hcard]
  have hsum : (∑ᶠ z ∈ ball c R, analyticOrderNatAt A z) = ∑ z ∈ S, analyticOrderNatAt A z := by
    refine finsum_mem_eq_sum_of_subset _ (fun z hz => ?_) hsub
    obtain ⟨hzb, hzs⟩ := hz
    simp only [Function.mem_support, ne_eq] at hzs
    exact hmemS z hzb hzs
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not S (fun z => A z = 0)]
  have h1 : ∑ z ∈ S.filter (fun z => A z = 0), analyticOrderNatAt A z = T.card := by
    rw [Finset.sum_congr rfl (fun z hz => ?_), Finset.sum_const, smul_eq_mul, mul_one, hT]
    obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
    exact hsimple z (hsub (by simpa using hzS)) hz0
  have h2 : ∑ z ∈ S.filter (fun z => ¬ A z = 0), analyticOrderNatAt A z = 0 := by
    refine Finset.sum_eq_zero (fun z hz => ?_)
    obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
    simp [analyticOrderNatAt,
      (hAb z (hsub (by simpa using hzS))).analyticOrderAt_eq_zero.2 hz0]
  rw [h1, h2, add_zero]

/-- **The open-mapping degree**, distinct-and-simple form. Under the additional hypothesis that
`f'` is zero-free on the punctured disc, every `w ≠ f z₀` close enough to `f z₀` has exactly `n`
*distinct* preimages in the open disc, each of them a simple zero of `f - w`. -/
theorem localDegree_card {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hiso : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderiv : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → deriv f z ≠ 0) :
    ∃ δ > 0, ∀ w : ℂ, w ≠ f z₀ → ‖w - f z₀‖ < δ →
      {z ∈ ball z₀ r | f z = w}.ncard = analyticOrderNatAt (fun ζ => f ζ - f z₀) z₀ ∧
        ∀ z ∈ ball z₀ r, f z = w → analyticOrderNatAt (fun ζ => f ζ - w) z = 1 := by
  obtain ⟨δ, hδ, hcount⟩ := localDegree hr hf hiso
  refine ⟨δ, hδ, fun w hw hwδ => ?_⟩
  have hA : AnalyticOnNhd ℂ (fun ζ => f ζ - w) (closedBall z₀ r) := hf.sub analyticOnNhd_const
  have hsimple : ∀ z ∈ ball z₀ r, f z - w = 0 → analyticOrderNatAt (fun ζ => f ζ - w) z = 1 := by
    intro z hz hz0
    have hzne : z ≠ z₀ := by
      rintro rfl
      exact hw (sub_eq_zero.mp hz0).symm
    have hd : deriv (fun ζ => f ζ - w) z ≠ 0 := by
      rw [deriv_sub_const]
      exact hderiv z (ball_subset_closedBall hz) hzne
    simp [analyticOrderNatAt,
      (hA z (ball_subset_closedBall hz)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz0 hd]
  refine ⟨?_, fun z hz hfz => hsimple z hz (by rw [hfz, sub_self])⟩
  rw [← hcount w hwδ, count_eq_ncard hA hsimple]
  congr 1
  ext z
  simp [sub_eq_zero]

/-- **The open-mapping degree**, textbook form. If `f` is analytic at `z₀` and `z₀` is an isolated
solution of `f z = f z₀` — equivalently, `f` is not constant near `z₀` — then there are radii `r`
and `δ` for which `localDegree` applies. -/
theorem exists_localDegree {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ f z₀) :
    ∃ r > 0, AnalyticOnNhd ℂ f (closedBall z₀ r) ∧
      ∃ δ > 0, ∀ w : ℂ, ‖w - f z₀‖ < δ →
        (∑ᶠ z ∈ ball z₀ r, analyticOrderNatAt (fun ζ => f ζ - w) z)
          = analyticOrderNatAt (fun ζ => f ζ - f z₀) z₀ := by
  obtain ⟨ε₁, hε₁, hA₁⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  obtain ⟨ε₂, hε₂, hI₂⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
  refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (by linarith) (by linarith), fun z hz => ?_, ?_⟩
  · exact hA₁ (lt_of_le_of_lt (mem_closedBall.mp hz)
      (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  · refine localDegree (lt_min (by linarith) (by linarith)) (fun z hz => ?_) (fun z hz hzn => ?_)
    · exact hA₁ (lt_of_le_of_lt (mem_closedBall.mp hz)
        (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    · refine hI₂ (lt_of_le_of_lt (mem_closedBall.mp hz)
        (lt_of_le_of_lt (min_le_right _ _) (by linarith))) ?_
      simpa using hzn

/-- **Local injectivity fails at a critical point.** If `f'` vanishes at `z₀` while `f` is
non-constant near it, the local degree is at least `2`, so some value close to `f z₀` is attained
twice and `f` is not injective on the disc.

Together with the inverse function theorem — which supplies the converse, that `deriv f z₀ ≠ 0`
makes `f` injective near `z₀` (`HasStrictDerivAt.eventually_left_inverse`, consumed from Mathlib
rather than reproved) — this is the local injectivity criterion: near `z₀`, an analytic `f` is
injective exactly when its derivative there is nonzero. -/
theorem not_injOn_of_deriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hiso : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderiv : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → deriv f z ≠ 0)
    (hd₀ : deriv f z₀ = 0) :
    ¬ Set.InjOn f (ball z₀ r) := by
  obtain ⟨δ, hδ, hcard⟩ := localDegree_card hr hf hiso hderiv
  -- the degree is at least two: both `f - f z₀` and its derivative vanish at `z₀`
  have hA : AnalyticAt ℂ (fun ζ => f ζ - f z₀) z₀ :=
    (hf.sub analyticOnNhd_const) z₀ (mem_closedBall_self hr.le)
  have htop : analyticOrderAt (fun ζ => f ζ - f z₀) z₀ ≠ ⊤ := by
    intro hev
    rw [analyticOrderAt_eq_top] at hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    -- a point of the punctured disc where `f` would have to agree with `f z₀`
    set t : ℝ := min ε r / 2 with ht_def
    have ht0 : 0 < t := by rw [ht_def]; exact half_pos (lt_min hε hr)
    have htε : t < ε := by
      have h := min_le_left ε r
      rw [ht_def]; linarith
    have htr : t ≤ r := by
      have h := min_le_right ε r
      rw [ht_def]; linarith
    have hdist : dist (z₀ + (t : ℂ)) z₀ = t := by
      simp [dist_eq_norm, abs_of_pos ht0]
    refine hiso (z₀ + (t : ℂ)) ?_ ?_ (sub_eq_zero.mp (hball ?_))
    · simp only [mem_closedBall, hdist]; exact htr
    · simp only [ne_eq, add_eq_left, Complex.ofReal_eq_zero]
      exact ht0.ne'
    · rw [hdist]; exact htε
  have h2 : 2 ≤ analyticOrderNatAt (fun ζ => f ζ - f z₀) z₀ := by
    have hle : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun ζ => f ζ - f z₀) z₀ := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
      intro i hi
      interval_cases i
      · simp
      · simpa [iteratedDeriv_one, deriv_sub_const] using hd₀
    simpa [analyticOrderNatAt] using (ENat.toNat_le_toNat hle htop)
  -- a value just off `f z₀` therefore has two distinct preimages
  set w : ℂ := f z₀ + (δ / 2 : ℝ) with hw_def
  have hwne : w ≠ f z₀ := by
    simp [hw_def, ne_eq, add_eq_left, Complex.ofReal_eq_zero]
    linarith
  have hwlt : ‖w - f z₀‖ < δ := by
    simp only [hw_def, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < δ / 2)]
    linarith
  obtain ⟨hncard, _⟩ := hcard w hwne hwlt
  have hfin : {z ∈ ball z₀ r | f z = w}.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncard]; omega)
  have hnontriv : {z ∈ ball z₀ r | f z = w}.Nontrivial := by
    have hgt : 1 < {z ∈ ball z₀ r | f z = w}.ncard := by rw [hncard]; omega
    have := hfin.to_subtype
    exact Set.one_lt_ncard_iff_nontrivial.mp hgt
  obtain ⟨a, ha, b, hb, hab⟩ := hnontriv
  exact fun hinj => hab (hinj ha.1 hb.1 (ha.2.trans hb.2.symm))

end TauCeti
