/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.AlgebraicTopology.Sphere.Puncture

/-!
# The unit sphere is simply connected above rank two

The unit sphere of a real inner product space `E` with `2 < Module.rank ℝ E` is simply connected;
in particular `Sⁿ` is simply connected for `2 ≤ n`.

The proof is the classical one, in the form that avoids any smoothing or simplicial
approximation. A loop `γ` is compared with the *piecewise geodesic* loop through the `N + 1`
values `γ(k/N)`, where `N` is chosen so fine that `‖γ s - γ t‖ < 1` whenever `|s - t| ≤ 1/N`.
That comparison loop is written as a single global formula rather than by gluing pieces: it is
the radial projection to the sphere of

  `L t = ∑ k ≤ N, Λ k t • γ (k/N)`,   `Λ k t = max 0 (1 - |N * t - k|)`,

the piecewise linear interpolation of the nodes through the hat functions of the subdivision.
Two facts about `L` do all the work. Since `Λ k t ≠ 0` forces `|N * t - k| < 1`, hence
`⟪γ t, γ (k/N)⟫ > 1/2`, the inner product `⟪γ t, L t⟫` is positive; so the straight-line homotopy
from `γ t` to `L t` never meets the origin, and its radial projection is a homotopy of loops on
the sphere. And `Λ k t ≠ 0` also forces `k` to be `⌊N t⌋` or `⌊N t⌋ + 1`, so `L t` lies in the
span of two of the nodes. A finite family of proper subspaces of `E` cannot cover `E`
(`Submodule.exists_forall_notMem_of_forall_ne_top`), and the spans of two vectors are proper
exactly because the rank exceeds two, so the projected loop omits a point of the sphere. Loops
omitting a point are null-homotopic by `TauCeti.homotopic_refl_of_notMem_range`.

Rank two is genuinely the boundary: the circle is not simply connected.

## Main declarations

* `TauCeti.exists_homotopic_notMem_range`: every loop on the unit sphere is homotopic to a loop
  that omits a point of the sphere.
* `TauCeti.simplyConnectedSpace_sphere`: **the unit sphere of a real inner product space of rank
  greater than two is simply connected.**
* `TauCeti.simplyConnectedSpace_euclideanSphere`: the case of `Sⁿ` for `2 ≤ n`.

## References

This is the missing input to the `π₁(RPⁿ)` line of `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 4, item 13: `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv` and its corollaries were
stated against a simply connected covering sphere, and this file discharges that hypothesis. The
argument is the classical one of Hatcher, *Algebraic Topology*, Proposition 1.14, with the
subdivision realised by hat functions rather than by gluing. No Mathlib code is vendored.
-/

public section

noncomputable section

open Metric NormedSpace
open scoped unitInterval RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two unit vectors at distance less than one have inner product greater than `1 / 2`. -/
private theorem half_lt_inner {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ‖a - b‖ < 1) :
    1 / 2 < ⟪a, b⟫ := by
  have hsq : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫ := by
    rw [norm_sub_sq_real, ha, hb]; ring
  nlinarith [norm_nonneg (a - b)]

/-- The `k`-th hat function of the subdivision of the unit interval into `N` equal parts: it
peaks at `k / N` and vanishes outside `((k - 1)/N, (k + 1)/N)`. -/
private def hatFunction (N k : ℕ) (t : I) : ℝ := max 0 (1 - |(N : ℝ) * (t : ℝ) - (k : ℝ)|)

/-- The piecewise linear interpolation of the nodes `node 0, …, node N` through the hat
functions of the subdivision of the unit interval into `N` equal parts. -/
private def nodeInterp (N : ℕ) (node : ℕ → E) (t : I) : E :=
  ∑ k ∈ Finset.range (N + 1), hatFunction N k t • node k

private theorem hatFunction_nonneg (N k : ℕ) (t : I) : 0 ≤ hatFunction N k t := le_max_left _ _

private theorem continuous_hatFunction (N k : ℕ) : Continuous (hatFunction N k) := by
  unfold hatFunction
  fun_prop

/-- The hat function of the `k`-th node vanishes unless `N * t` is within `1` of `k`. -/
private theorem abs_lt_one_of_hatFunction_ne_zero {N k : ℕ} {t : I} (h : hatFunction N k t ≠ 0) :
    |(N : ℝ) * (t : ℝ) - (k : ℝ)| < 1 := by
  by_contra hc
  push Not at hc
  exact h (max_eq_left (by linarith))

/-- The only hat functions that do not vanish at `t` are those of the two nodes straddling `t`. -/
private theorem eq_floor_or_of_hatFunction_ne_zero {N k : ℕ} {t : I}
    (h : hatFunction N k t ≠ 0) :
    k = ⌊(N : ℝ) * (t : ℝ)⌋₊ ∨ k = ⌊(N : ℝ) * (t : ℝ)⌋₊ + 1 := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (unitInterval.nonneg t)
  have h1 : ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (t : ℝ) := Nat.floor_le h0
  have h2 : (N : ℝ) * (t : ℝ) < ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have habs := abs_lt.mp (abs_lt_one_of_hatFunction_ne_zero h)
  have hk1 : (k : ℝ) < ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) + 2 := by linarith [habs.1]
  have hk2 : ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) < (k : ℝ) + 1 := by linarith [habs.2]
  have hk1' : k < ⌊(N : ℝ) * (t : ℝ)⌋₊ + 2 := by exact_mod_cast hk1
  have hk2' : ⌊(N : ℝ) * (t : ℝ)⌋₊ < k + 1 := by exact_mod_cast hk2
  omega

/-- At `t` the hat function of the node `⌊N t⌋` is positive. -/
private theorem hatFunction_floor_pos {N : ℕ} (t : I) :
    0 < hatFunction N ⌊(N : ℝ) * (t : ℝ)⌋₊ t := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (unitInterval.nonneg t)
  have h1 : ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (t : ℝ) := Nat.floor_le h0
  have h2 : (N : ℝ) * (t : ℝ) < ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have habs : |(N : ℝ) * (t : ℝ) - ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  exact lt_max_of_lt_right (by linarith)

private theorem hatFunction_zero_self (N : ℕ) : hatFunction N 0 (0 : I) = 1 := by
  simp [hatFunction]

private theorem hatFunction_zero_of_ne (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    hatFunction N k (0 : I) = 0 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have habs : |(N : ℝ) * ((0 : I) : ℝ) - (k : ℝ)| = (k : ℝ) := by
    rw [Set.Icc.coe_zero, mul_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg k)]
  simp only [hatFunction, habs]
  exact max_eq_left (by linarith)

private theorem hatFunction_one_self (N : ℕ) : hatFunction N N (1 : I) = 1 := by
  simp [hatFunction]

private theorem hatFunction_one_of_ne {N k : ℕ} (hkN : k ≤ N) (hk : k ≠ N) :
    hatFunction N k (1 : I) = 0 := by
  have h1 : (k : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_ne hkN hk)
  have habs : |(N : ℝ) * ((1 : I) : ℝ) - (k : ℝ)| = (N : ℝ) - (k : ℝ) := by
    rw [Set.Icc.coe_one, mul_one, abs_of_nonneg (by linarith)]
  simp only [hatFunction, habs]
  exact max_eq_left (by linarith)

private theorem continuous_nodeInterp (N : ℕ) (node : ℕ → E) :
    Continuous (nodeInterp N node) :=
  continuous_finsetSum _ fun k _ => (continuous_hatFunction N k).smul continuous_const

private theorem nodeInterp_zero (N : ℕ) (node : ℕ → E) : nodeInterp N node 0 = node 0 := by
  rw [nodeInterp, Finset.sum_eq_single 0]
  · rw [hatFunction_zero_self, one_smul]
  · exact fun k _ hk => by rw [hatFunction_zero_of_ne N hk, zero_smul]
  · exact fun hc => absurd (Finset.mem_range.mpr (Nat.succ_pos N)) hc

private theorem nodeInterp_one (N : ℕ) (node : ℕ → E) : nodeInterp N node 1 = node N := by
  rw [nodeInterp, Finset.sum_eq_single N]
  · rw [hatFunction_one_self, one_smul]
  · exact fun k hk hkN => by
      rw [hatFunction_one_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkN, zero_smul]
  · exact fun hc => absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) hc

/-- The interpolation at `t` lies on the geodesic chord of the two nodes straddling `t`. -/
private theorem nodeInterp_mem_span (N : ℕ) (node : ℕ → E) (t : I) :
    nodeInterp N node t ∈
      Submodule.span ℝ {node ⌊(N : ℝ) * (t : ℝ)⌋₊, node (⌊(N : ℝ) * (t : ℝ)⌋₊ + 1)} := by
  rw [nodeInterp]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : hatFunction N k t = 0
  · simp [hk]
  · refine Submodule.smul_mem _ _ ?_
    rcases eq_floor_or_of_hatFunction_ne_zero hk with h | h <;>
      exact h ▸ Submodule.subset_span (by simp)

/-- If every node whose hat function is alive at `t` has inner product with `a` above `1/2`,
then the inner product of `a` with the interpolation is at least half the total weight. -/
private theorem half_mul_sum_le_inner_nodeInterp {N : ℕ} {node : ℕ → E} {a : E} (t : I)
    (h : ∀ k, hatFunction N k t ≠ 0 → 1 / 2 < ⟪a, node k⟫) :
    1 / 2 * ∑ k ∈ Finset.range (N + 1), hatFunction N k t ≤ ⟪a, nodeInterp N node t⟫ := by
  rw [nodeInterp, inner_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [real_inner_smul_right]
  rcases eq_or_ne (hatFunction N k t) 0 with hk | hk
  · simp [hk]
  · have := mul_le_mul_of_nonneg_left (h k hk).le (hatFunction_nonneg N k t)
    linarith

/-- **Every loop on the unit sphere of a real inner product space of rank greater than two is
homotopic to a loop that omits a point of the sphere.** The comparison loop is the radial
projection of the piecewise linear interpolation of finitely many values of the loop, and the
point it omits is obtained by avoiding the finitely many planes those values span. -/
theorem exists_homotopic_notMem_range (h : 2 < Module.rank ℝ E) {x : sphere (0 : E) 1}
    (γ : Path x x) :
    ∃ γ' : Path x x, γ.Homotopic γ' ∧ ∃ p : sphere (0 : E) 1, p ∉ Set.range γ' := by
  have hγnorm : ∀ t, ‖((γ t : sphere (0 : E) 1) : E)‖ = 1 := fun t =>
    mem_sphere_zero_iff_norm.mp (γ t).2
  have hγcont : Continuous fun t : I => ((γ t : sphere (0 : E) 1) : E) :=
    continuous_subtype_val.comp γ.continuous
  -- Choose a subdivision so fine that the loop moves by less than `1` across each step.
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hγcont) 1 one_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := N₀ + 1 with hNdef
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNδ : 1 / (N : ℝ) < δ := by rw [hNdef]; push_cast; exact hN₀
  -- The nodes of the subdivision, and the piecewise linear interpolation through them.
  have hparam : ∀ k : ℕ, min 1 ((k : ℝ) / (N : ℝ)) ∈ I := fun k =>
    ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  set nodeParam : ℕ → I := fun k => ⟨min 1 ((k : ℝ) / (N : ℝ)), hparam k⟩ with hnodeParam
  set node : ℕ → E := fun k => ((γ (nodeParam k) : sphere (0 : E) 1) : E) with hnode
  have hnodenorm : ∀ k, ‖node k‖ = 1 := fun k => hγnorm _
  have hfloor_le : ∀ t : I, ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ N := by
    intro t
    calc ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ :=
          Nat.floor_mono (mul_le_of_le_one_right hNR.le (unitInterval.le_one t))
      _ = N := Nat.floor_natCast N
  -- Every node alive at `t` is close to `γ t`, hence at inner product above `1/2`.
  have hclose : ∀ (t : I) (k : ℕ), hatFunction N k t ≠ 0 →
      1 / 2 < ⟪((γ t : sphere (0 : E) 1) : E), node k⟫ := by
    intro t k hk
    have habs := abs_lt_one_of_hatFunction_ne_zero hk
    have hdiff : |(t : ℝ) - (k : ℝ) / (N : ℝ)| < 1 / (N : ℝ) := by
      have hrw : (t : ℝ) - (k : ℝ) / (N : ℝ) = ((N : ℝ) * (t : ℝ) - (k : ℝ)) / (N : ℝ) := by
        field_simp
      rw [hrw, abs_div, abs_of_pos hNR]
      gcongr
    have hmin : |(t : ℝ) - min 1 ((k : ℝ) / (N : ℝ))| ≤ |(t : ℝ) - (k : ℝ) / (N : ℝ)| := by
      rcases le_or_gt ((k : ℝ) / (N : ℝ)) 1 with hc | hc
      · rw [min_eq_right hc]
      · rw [min_eq_left hc.le]
        have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    have hdist : dist t (nodeParam k) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      calc |(t : ℝ) - ((nodeParam k : I) : ℝ)| = |(t : ℝ) - min 1 ((k : ℝ) / (N : ℝ))| := rfl
        _ ≤ |(t : ℝ) - (k : ℝ) / (N : ℝ)| := hmin
        _ < 1 / (N : ℝ) := hdiff
        _ < δ := hNδ
    have hlt : ‖((γ t : sphere (0 : E) 1) : E) - node k‖ < 1 := by
      have := hδ' hdist
      rwa [dist_eq_norm] at this
    exact half_lt_inner (hγnorm t) (hnodenorm k) hlt
  -- Hence the interpolation is never antipodal to, indeed never orthogonal to, the loop.
  have hLinner : ∀ t : I, 0 < ⟪((γ t : sphere (0 : E) 1) : E), nodeInterp N node t⟫ := by
    intro t
    have hm : ⌊(N : ℝ) * (t : ℝ)⌋₊ ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hfloor_le t))
    have hpossum : 0 < ∑ k ∈ Finset.range (N + 1), hatFunction N k t :=
      lt_of_lt_of_le (hatFunction_floor_pos t)
        (Finset.single_le_sum (fun k _ => hatFunction_nonneg N k t) hm)
    have := half_mul_sum_le_inner_nodeInterp (node := node) t (fun k hk => hclose t k hk)
    linarith
  have hLne : ∀ t : I, nodeInterp N node t ≠ 0 := by
    intro t ht
    have hpos := hLinner t
    rw [ht, inner_zero_right] at hpos
    exact lt_irrefl 0 hpos
  -- The interpolation matches the loop at both ends of the interval.
  have hnodeParam0 : nodeParam 0 = (0 : I) := Subtype.ext (by simp [hnodeParam])
  have hnodeParamN : nodeParam N = (1 : I) :=
    Subtype.ext (by simp [hnodeParam])
  have hL0 : nodeInterp N node 0 = ((x : sphere (0 : E) 1) : E) := by
    simp only [nodeInterp_zero, hnode, hnodeParam0, γ.source]
  have hL1 : nodeInterp N node 1 = ((x : sphere (0 : E) 1) : E) := by
    simp only [nodeInterp_one, hnode, hnodeParamN, γ.target]
  -- The comparison loop.
  have hcontL : Continuous (nodeInterp N node) := continuous_nodeInterp N node
  have hcontγ' : Continuous fun t : I =>
      (⟨normalize (nodeInterp N node t),
        mem_sphere_zero_iff_norm.mpr (norm_normalize (hLne t))⟩ : sphere (0 : E) 1) := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun t => ‖nodeInterp N node t‖⁻¹ • nodeInterp N node t
    exact ((continuous_norm.comp hcontL).inv₀
      (fun t => norm_ne_zero_iff.mpr (hLne t))).smul hcontL
  have hx1 : ‖((x : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  set γ' : Path x x :=
    { toFun := fun t => ⟨normalize (nodeInterp N node t),
        mem_sphere_zero_iff_norm.mpr (norm_normalize (hLne t))⟩
      continuous_toFun := hcontγ'
      source' := Subtype.ext (by
        change normalize (nodeInterp N node 0) = ((x : sphere (0 : E) 1) : E)
        rw [hL0, normalize_eq_self_of_norm_eq_one hx1])
      target' := Subtype.ext (by
        change normalize (nodeInterp N node 1) = ((x : sphere (0 : E) 1) : E)
        rw [hL1, normalize_eq_self_of_norm_eq_one hx1]) } with hγ'
  -- The straight-line homotopy between the loop and the comparison loop misses the origin.
  have hGne : ∀ z : I × I,
      (1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E) + (z.1 : ℝ) • nodeInterp N node z.2
        ≠ 0 := by
    rintro ⟨u, t⟩ hz
    have hexp : ⟪((γ t : sphere (0 : E) 1) : E),
        (1 - (u : ℝ)) • ((γ t : sphere (0 : E) 1) : E) + (u : ℝ) • nodeInterp N node t⟫
          = (1 - (u : ℝ)) * 1
            + (u : ℝ) * ⟪((γ t : sphere (0 : E) 1) : E), nodeInterp N node t⟫ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hγnorm t]
      norm_num
    have hpos : 0 < (1 - (u : ℝ)) * 1
        + (u : ℝ) * ⟪((γ t : sphere (0 : E) 1) : E), nodeInterp N node t⟫ := by
      rcases (unitInterval.nonneg u).lt_or_eq with hu | hu
      · nlinarith [mul_pos hu (hLinner t), unitInterval.le_one u]
      · rw [← hu]; norm_num
    rw [← hexp] at hpos
    simp only [hz, inner_zero_right] at hpos
    exact lt_irrefl 0 hpos
  have hsquare : γ.Homotopic γ' := by
    refine Path.homotopic_of_continuous_square
      (fun z => ⟨normalize ((1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E)
          + (z.1 : ℝ) • nodeInterp N node z.2),
        mem_sphere_zero_iff_norm.mpr (norm_normalize (hGne z))⟩) ?_ ?_ ?_ ?_ ?_
    · refine Continuous.subtype_mk ?_ _
      have hg : Continuous fun z : I × I =>
          (1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E)
            + (z.1 : ℝ) • nodeInterp N node z.2 := by
        have h1 : Continuous fun z : I × I => ((γ z.2 : sphere (0 : E) 1) : E) :=
          hγcont.comp continuous_snd
        have h2 : Continuous fun z : I × I => ((z.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        exact ((continuous_const.sub h2).smul h1).add
          (h2.smul (hcontL.comp continuous_snd))
      change Continuous fun z => ‖_‖⁻¹ • _
      exact ((continuous_norm.comp hg).inv₀ (fun z => norm_ne_zero_iff.mpr (hGne z))).smul hg
    · intro s
      refine Subtype.ext ?_
      change normalize ((1 - ((0 : I) : ℝ)) • ((γ s : sphere (0 : E) 1) : E)
        + ((0 : I) : ℝ) • nodeInterp N node s) = ((γ s : sphere (0 : E) 1) : E)
      rw [Set.Icc.coe_zero]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      exact normalize_eq_self_of_norm_eq_one (hγnorm s)
    · intro s
      refine Subtype.ext ?_
      change normalize ((1 - ((1 : I) : ℝ)) • ((γ s : sphere (0 : E) 1) : E)
        + ((1 : I) : ℝ) • nodeInterp N node s) = normalize (nodeInterp N node s)
      rw [Set.Icc.coe_one]
      simp
    · intro u
      refine Subtype.ext ?_
      change normalize ((1 - (u : ℝ)) • ((γ 0 : sphere (0 : E) 1) : E)
        + (u : ℝ) • nodeInterp N node 0) = ((x : sphere (0 : E) 1) : E)
      rw [hL0, γ.source, ← add_smul, sub_add_cancel, one_smul,
        normalize_eq_self_of_norm_eq_one hx1]
    · intro u
      refine Subtype.ext ?_
      change normalize ((1 - (u : ℝ)) • ((γ 1 : sphere (0 : E) 1) : E)
        + (u : ℝ) • nodeInterp N node 1) = ((x : sphere (0 : E) 1) : E)
      rw [hL1, γ.target, ← add_smul, sub_add_cancel, one_smul,
        normalize_eq_self_of_norm_eq_one hx1]
  -- The comparison loop lives in finitely many planes, which cannot cover `E`.
  have hVne : ∀ m : Fin (N + 1),
      Submodule.span ℝ ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E) ≠ ⊤ := by
    intro m hm
    have hcard : Cardinal.mk ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E) ≤ 2 :=
      calc Cardinal.mk ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E)
          ≤ Cardinal.mk ({node ((m : ℕ) + 1)} : Set E) + 1 := Cardinal.mk_insert_le
        _ = 2 := by rw [Cardinal.mk_singleton]; exact one_add_one_eq_two
    have h2 : Module.rank ℝ
        ↥(Submodule.span ℝ ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E)) ≤ 2 :=
      (rank_span_le _).trans hcard
    rw [hm, rank_top] at h2
    exact absurd h2 (not_le.mpr h)
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun m : Fin (N + 1) => Submodule.span ℝ ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E)) hVne
  have hw0 : w ≠ 0 := fun h0 => hw ⟨0, Nat.succ_pos N⟩ (h0 ▸ Submodule.zero_mem _)
  refine ⟨γ', hsquare, ⟨normalize w, mem_sphere_zero_iff_norm.mpr (norm_normalize hw0)⟩, ?_⟩
  rintro ⟨t, ht⟩
  have hteq : normalize (nodeInterp N node t) = normalize w := congrArg Subtype.val ht
  have hwmem : w ∈
      Submodule.span ℝ ({node ⌊(N : ℝ) * (t : ℝ)⌋₊, node (⌊(N : ℝ) * (t : ℝ)⌋₊ + 1)} : Set E) := by
    have hwrite : w = (‖w‖ * ‖nodeInterp N node t‖⁻¹) • nodeInterp N node t :=
      calc w = ‖w‖ • normalize w := (norm_smul_normalize w).symm
        _ = ‖w‖ • normalize (nodeInterp N node t) := by rw [hteq]
        _ = (‖w‖ * ‖nodeInterp N node t‖⁻¹) • nodeInterp N node t := by
              rw [NormedSpace.normalize, smul_smul]
    rw [hwrite]
    exact Submodule.smul_mem _ _ (nodeInterp_mem_span N node t)
  exact hw ⟨⌊(N : ℝ) * (t : ℝ)⌋₊, Nat.lt_succ_of_le (hfloor_le t)⟩ hwmem

/-- **The unit sphere of a real inner product space of rank greater than two is simply
connected.** Every loop is homotopic to one omitting a point, and the punctured sphere contracts
to the antipode of the omitted point. -/
theorem simplyConnectedSpace_sphere (h : 2 < Module.rank ℝ E) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  have hpc : PathConnectedSpace (sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (Cardinal.one_lt_two.trans h) 0 zero_le_one)
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨hpc, fun x γ => ?_⟩
  obtain ⟨γ', hγγ', p, hp⟩ := exists_homotopic_notMem_range h γ
  exact hγγ'.trans (homotopic_refl_of_notMem_range γ' hp)

/-- **The `n`-sphere is simply connected for `2 ≤ n`.** -/
theorem simplyConnectedSpace_euclideanSphere {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  refine simplyConnectedSpace_sphere ?_
  have hrank : Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = ((n + 1 : ℕ) : Cardinal) := by
    simp [← Module.finrank_eq_rank]
  rw [hrank]
  exact_mod_cast (by omega : 2 < n + 1)

end TauCeti

end
