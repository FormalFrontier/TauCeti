/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster
public import TauCeti.Analysis.Complex.Conformal.Jordan.Domain
public import TauCeti.Analysis.Complex.Conformal.Caratheodory
public import TauCeti.Analysis.Complex.PlaneSeparation.Basic
public import TauCeti.Topology.JordanCurve.SmallArc
public import TauCeti.Topology.JordanCurve.Subcontinuum

/-!
# Preconnected approach regions for Jordan domains

A Jordan domain has preconnected approach regions at every boundary point.
The proof uses Janiszewski's theorem (`TauCeti.janiszewski`) and one arc
lemma; it avoids the Jordan curve theorem and Schoenflies by using
Janiszewski.

Given `a ∈ frontier U` with `U` a Jordan domain, take an open arc
`W ⊆ frontier U ∩ ball a r` through `a` whose complement `frontier U \ W`
is closed and preconnected.  Set `S := frontier U` and
`T := sphere a r ∪ (frontier U \ W)`.  Then `S ∩ T = frontier U \ W` is
preconnected, `S` does not separate points of `U`, and `T` does not
separate points of `ball a ρ` for small `ρ`; Janiszewski puts both in one
component of `(S ∪ T)ᶜ ⊆ U ∩ ball a r`.

Combined with `injOn_closedBall_of_isPreconnected_image_approach` from
`Inverse/BoundaryCluster.lean`, this gives injectivity on the closed disc
for the Riemann map of a Jordan domain, and with `closureHomeomorph` from
`BoundaryCorrespondence.lean`, the homeomorphism of closures.

## Input

* `TauCeti.IsJordanCurve.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball`
  (`JordanCurve/SmallArc.lean`) — a Jordan curve admits a compact preconnected
  arc missing any given point, whose complement lies in a given ball.

## Main results

* `TauCeti.IsJordanDomain.isPreconnectedApproachAt`
  — a Jordan domain has preconnected approach regions at every boundary point.
* `TauCeti.injOn_closedBall_of_isJordanCurve_frontier`
  — injectivity on the closed disc for the Riemann map, Jordan case.
* `TauCeti.exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier`
  — the Riemann map extends to a homeomorphism of the closures.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Layer L5 is absent from
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
  human-curated Riemann-mapping-theorem effort, and Mathlib has no boundary correspondence for
  conformal maps, so this is new Lean formalization.
-/

public section

open Set Metric Topology Function Filter Bornology Real

namespace TauCeti

/-! ### Jordan domains -/

variable {U : Set ℂ} {a : ℂ}

/-- **Janiszewski step.**  Given an open arc `W` of the boundary through `a`,
inside `ball a r`, with closed preconnected complement, the trace `U ∩ ball a δ`
lies in one preconnected subset of `U ∩ ball a r` for some `δ > 0`.

`S := frontier U` and `T := sphere a r ∪ (frontier U \ W)` are closed and
bounded with `S ∩ T = frontier U \ W`; neither separates two points of
`U ∩ ball a δ`, so by `TauCeti.janiszewski` both lie in one component of
`(S ∪ T)ᶜ`, which sits inside `U ∩ ball a r`. -/
private theorem IsJordanDomain.exists_isPreconnected_inter_ball_subset_of_arc
    (hU : IsJordanDomain U) {r : ℝ} (hr : 0 < r) {W : Set ℂ}
    (hWJ : W ⊆ frontier U ∩ ball a r) (haW : a ∈ W)
    (hclosed : IsClosed (frontier U \ W)) (hpre : IsPreconnected (frontier U \ W)) :
    ∃ δ > 0, ∃ C ⊆ U ∩ ball a r, IsPreconnected C ∧ U ∩ ball a δ ⊆ C := by
  set J := frontier U
  -- a radius whose ball misses the complementary arc
  obtain ⟨ρ, hρ₀, hρr, hρdisj⟩ :
      ∃ ρ > 0, ρ ≤ r ∧ Disjoint (ball a ρ) (J \ W) := by
    rcases (J \ W).eq_empty_or_nonempty with hne | hne
    · exact ⟨r, hr, le_rfl, by rw [hne]; exact disjoint_empty _⟩
    · have haJW : a ∉ J \ W := fun h => h.2 haW
      have hpos : 0 < infDist a (J \ W) := by
        rcases (infDist_nonneg (x := a) (s := J \ W)).lt_or_eq with h | h
        · exact h
        · exact absurd ((hclosed.mem_iff_infDist_zero hne).mpr h.symm) haJW
      refine ⟨min r (infDist a (J \ W)), lt_min hr hpos, min_le_left _ _, ?_⟩
      rw [Set.disjoint_left]
      intro z hz hzJ
      have h1 : infDist a (J \ W) ≤ dist a z := infDist_le_dist_of_mem hzJ
      have h2 : dist a z < min r (infDist a (J \ W)) := by rw [dist_comm]; exact mem_ball.mp hz
      exact absurd (h2.trans_le (min_le_right _ _)) (not_lt.mpr h1)
  refine ⟨ρ, hρ₀, ?_⟩
  rcases (U ∩ ball a ρ).eq_empty_or_nonempty with hne | ⟨x₀, hx₀U, hx₀a⟩
  · exact ⟨∅, empty_subset _, isPreconnected_empty, hne.subset⟩
  set S : Set ℂ := J
  set T : Set ℂ := sphere a r ∪ (J \ W)
  set C : Set ℂ := connectedComponentIn (S ∪ T)ᶜ x₀
  have hUJ : U ∩ J = ∅ := hU.isOpen.inter_frontier_eq
  have hx₀J : x₀ ∉ J := fun h => (Set.eq_empty_iff_forall_notMem.mp hUJ) x₀ ⟨hx₀U, h⟩
  have hx₀r : x₀ ∈ ball a r := ball_subset_ball hρr hx₀a
  have hx₀T : x₀ ∉ T := by
    rintro (h | h)
    · exact (ne_of_lt (mem_ball.mp hx₀r)) (mem_sphere.mp h)
    · exact hx₀J h.1
  have hx₀C : x₀ ∈ C := mem_connectedComponentIn (by
    rintro (h | h)
    · exact hx₀J h
    · exact hx₀T h)
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCST : C ⊆ (S ∪ T)ᶜ := connectedComponentIn_subset _ _
  -- `C` avoids the frontier, so it lies in `U`
  have hCU : C ⊆ U := by
    refine IsPreconnected.subset_left_of_subset_union hU.isOpen
      (isClosed_closure : IsClosed (closure U)).isOpen_compl
      ?_ ?_ ⟨x₀, hx₀C, hx₀U⟩ hCpre
    · exact disjoint_compl_right.mono_left subset_closure
    · intro z hz
      by_cases hzc : z ∈ closure U
      · left
        by_contra hzU
        exact hCST hz (Or.inl ⟨hzc, fun hi => hzU (interior_subset hi)⟩)
      · exact Or.inr hzc
  -- `C` avoids the sphere, so it lies in the ball
  have hCball : C ⊆ ball a r := by
    refine IsPreconnected.subset_left_of_subset_union isOpen_ball
      (isClosed_closedBall : IsClosed (closedBall a r)).isOpen_compl
      ?_ ?_ ⟨x₀, hx₀C, hx₀r⟩ hCpre
    · exact disjoint_compl_right.mono_left ball_subset_closedBall
    · intro z hz
      by_cases hzc : z ∈ closedBall a r
      · left
        rcases (mem_closedBall.mp hzc).lt_or_eq with h | h
        · exact mem_ball.mpr h
        · exact absurd (Or.inr (Or.inl (mem_sphere.mpr h))) (hCST hz)
      · exact Or.inr hzc
  refine ⟨C, fun z hz => ⟨hCU hz, hCball hz⟩, hCpre, ?_⟩
  -- Janiszewski puts every point of `U ∩ ball a ρ` in the component of `x₀`
  rintro y ⟨hyU, hya⟩
  have hSb : IsBounded S := hU.isBounded.closure.subset frontier_subset_closure
  have hST : S ∩ T = J \ W := by
    ext z
    constructor
    · rintro ⟨hzJ, hz | hz⟩
      · refine ⟨hzJ, fun hzW => ?_⟩
        exact (ne_of_lt (mem_ball.mp (hWJ hzW).2)) (mem_sphere.mp hz)
      · exact hz
    · exact fun hz => ⟨hz.1, Or.inr hz⟩
  have hSsep : y ∈ connectedComponentIn Sᶜ x₀ :=
    hU.isConnected.isPreconnected.subset_connectedComponentIn hx₀U
      (fun z hz hzJ => (Set.eq_empty_iff_forall_notMem.mp hUJ) z ⟨hz, hzJ⟩) hyU
  have hTsep : y ∈ connectedComponentIn Tᶜ x₀ := by
    refine (convex_ball a ρ).isPreconnected.subset_connectedComponentIn hx₀a ?_ hya
    rintro z hz (h | h)
    · exact (ne_of_lt (mem_ball.mp (ball_subset_ball hρr hz))) (mem_sphere.mp h)
    · exact Set.disjoint_left.mp hρdisj hz h
  exact janiszewski isClosed_frontier (isClosed_sphere.union hclosed) hSb
    (isBounded_sphere.union (hSb.subset sdiff_subset)) (hST ▸ hpre) hSsep hTsep

/-- **A Jordan domain is locally connected from within at each boundary point.**  The arc
lemma supplies the closed complementary arc, the Janiszewski step does the
rest. -/
theorem IsJordanDomain.exists_isPreconnected_inter_ball_subset
    (hU : IsJordanDomain U) (ha : a ∈ frontier U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ C ⊆ U ∩ ball a ε, IsPreconnected C ∧ U ∩ ball a δ ⊆ C := by
  obtain ⟨S, hSJ, hScompact, hSpre, haS, hball⟩ :=
    hU.isJordanCurve_frontier.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball ha hε
  have hcancel : frontier U \ (frontier U \ S) = S := sdiff_sdiff_cancel_left hSJ
  refine hU.exists_isPreconnected_inter_ball_subset_of_arc hε
    (fun z hz => ⟨hz.1, hball hz⟩) ⟨ha, haS⟩ ?_ ?_
  · rw [hcancel]; exact hScompact.isClosed
  · rw [hcancel]; exact hSpre

/-- **A Jordan domain has preconnected approach regions at every boundary
point.** -/
theorem IsJordanDomain.isPreconnectedApproachAt
    (hU : IsJordanDomain U) (ha : a ∈ frontier U) :
    IsPreconnectedApproachAt U a :=
  isPreconnectedApproachAt_of_forall_exists_isPreconnected_superset
    fun _ hε => hU.exists_isPreconnected_inter_ball_subset ha hε

variable {f F : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- **Conformal injectivity on the closed disc when the image is a Jordan
domain.**  Feeds `IsJordanDomain.isPreconnectedApproachAt` into
`injOn_closedBall_of_isPreconnected_image_approach`. -/
theorem IsJordanDomain.injOn_closedBall_of_conformal
    (hr : 0 < r)
    (hfd : DifferentiableOn ℂ f (ball c r))
    (hfi : InjOn f (ball c r))
    (hFc : ContinuousOn F (closedBall c r))
    (hFf : EqOn F f (ball c r))
    (hJ : IsJordanDomain (f '' ball c r)) :
    InjOn F (closedBall c r) :=
  injOn_closedBall_of_isPreconnected_image_approach hr hfd hfi hFc hFf
    fun _ ha => hJ.isPreconnectedApproachAt ha

/-- **Boundary injectivity, Jordan case**, in the hypothesis shape of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier`. -/
theorem injOn_closedBall_of_isJordanCurve_frontier (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hFc : ContinuousOn F (closedBall c r)) (hFf : EqOn F f (ball c r)) :
    InjOn F (closedBall c r) := by
  have hJ : IsJordanDomain (f '' ball c r) :=
    { isOpen := isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
      isConnected := IsConnected.image ⟨nonempty_ball.mpr hr, (convex_ball c r).isPreconnected⟩
        f hf.continuousOn
      isBounded := hb
      isJordanCurve_frontier := hJf }
  exact hJ.injOn_closedBall_of_conformal hr hf hinj hFc hFf

/-- **The Riemann map of a Jordan domain extends to a homeomorphism of the
closures.** -/
theorem exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z := by
  obtain ⟨g, hgc, hgd, hgbij⟩ :=
    exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ
  have himg : g '' ball 0 1 = Ω := hgbij.image_eq
  have hgi : InjOn g (closedBall 0 1) :=
    injOn_closedBall_of_isJordanCurve_frontier one_pos hgd hgbij.injOn (himg ▸ hΩb)
      (himg ▸ hΩJ) hgc fun _ _ => rfl
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hgc' : ContinuousOn g (closure (ball (0 : ℂ) 1)) := by rwa [hcl]
  have hgi' : InjOn g (closure (ball (0 : ℂ) 1)) := by rwa [hcl]
  have himg' : closure (g '' ball 0 1) = closure Ω := by rw [himg]
  refine ⟨g, hgc, hgd, hgbij, (Homeomorph.setCongr hcl.symm).trans
    ((closureHomeomorph isBounded_ball hgc' (fun _ _ => rfl) hgi').trans
      (Homeomorph.setCongr himg')), fun z => ?_⟩
  simp only [Homeomorph.trans_apply]
  exact coe_closureHomeomorph_apply isBounded_ball hgc' (fun _ _ => rfl) hgi' _

end TauCeti
