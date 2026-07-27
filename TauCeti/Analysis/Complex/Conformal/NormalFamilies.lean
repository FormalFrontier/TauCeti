/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Normal families: equicontinuity of a locally bounded family of holomorphic functions

A family of holomorphic functions on an open set `U ⊆ ℂ` that is *locally bounded* — uniformly
bounded on every compact subset of `U` — is automatically equicontinuous on `U`.  This is the
analytic heart of Montel's normal-families theorem: for complex-valued functions, combined with
Arzelà--Ascoli and an exhaustion/diagonal argument, it yields precompactness for local uniform
convergence.

The mechanism is Cauchy's estimate for the first derivative.  Mathlib's
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` bounds `‖deriv f c‖` at the *centre* of a
disc; halving the radius turns that pointwise bound into one that is uniform over a ball
(`norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`), and the mean value inequality on that
ball then bounds `dist (f z) (f w)` by a multiple of `dist z w` with a constant depending only on
the sup bound (`dist_le_of_forall_mem_closedBall_two_mul_norm_le`).  That constant is uniform in
the family, which is exactly equicontinuity.

## Main definitions

* `TauCeti.IsLocallyBoundedOn F s`: the family `F` is uniformly bounded on every compact subset
  of `s`.

## Main results

* `TauCeti.norm_deriv_le_of_forall_mem_closedBall_norm_le` and
  `TauCeti.norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`: Cauchy's estimate from a sup
  bound on a closed ball, at the centre and then uniformly over the ball of half the radius.
* `TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le` and
  `TauCeti.lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le`: a sup bound `M` on
  `closedBall c (2 * r)` makes a holomorphic function `M / r`-Lipschitz on `ball c r`.
* `TauCeti.IsLocallyBoundedOn.equicontinuousOn`: a locally bounded family of holomorphic
  functions is equicontinuous.  With `TauCeti.IsLocallyBoundedOn.exists_forall_norm_le`, this
  supplies the local inputs for an Arzelà--Ascoli exhaustion argument.
* `TauCeti.IsLocallyBoundedOn.deriv` and `TauCeti.IsLocallyBoundedOn.equicontinuousOn_deriv`: the
  derivatives of a locally bounded family of holomorphic functions are again locally bounded, hence
  also equicontinuous.

This advances the L1 (normal families / Montel) layer of the conformal-mapping roadmap, whose
generality bar requires scalar-valued functions `ℂ → ℂ` and fixes local boundedness as "bounded on
each compact `K ⊆ Ω`".  As with the rest of the L0--L3 conformal-mapping material it is coordinated
with the upstream Mathlib Riemann-mapping effort leanprover-community/mathlib4#33505, which proves a
Montel equicontinuity statement internally as a private lemma; these declarations are a temporary
shim, to be deleted and refactored to Mathlib's API once that human-curated work lands.

## References

Ahlfors, *Complex Analysis*, Ch. 5; Conway, *Functions of One Complex Variable I*, VII.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {ι : Type*} {U : Set ℂ} {f : ℂ → ℂ} {F : ι → ℂ → ℂ}

/-- A family `F : ι → ℂ → ℂ` is **locally bounded** on `s` if it is uniformly bounded — with a
single constant, independent of the index — on every compact subset of `s`.

This is the hypothesis of Montel's theorem, in the form fixed by the conformal-mapping roadmap. -/
def IsLocallyBoundedOn (F : ι → ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ K ⊆ s, IsCompact K → ∃ C, ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ C

/-- The defining compact-set characterization of local boundedness. -/
@[simp]
theorem isLocallyBoundedOn_def :
    IsLocallyBoundedOn F U ↔
      ∀ K ⊆ U, IsCompact K → ∃ C, ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ C :=
  Iff.rfl

/-- Local boundedness is inherited by subsets. -/
theorem IsLocallyBoundedOn.mono {s t : Set ℂ} (hb : IsLocallyBoundedOn F s) (hts : t ⊆ s) :
    IsLocallyBoundedOn F t :=
  fun _K hKt hK => hb _ (hKt.trans hts) hK

/-- A locally bounded family is bounded at each point of the set, uniformly in the index.

Together with `IsLocallyBoundedOn.equicontinuousOn`, this supplies the pointwise bounds used in
an Arzelà--Ascoli exhaustion argument. -/
theorem IsLocallyBoundedOn.exists_forall_norm_le {s : Set ℂ} (hb : IsLocallyBoundedOn F s) {z : ℂ}
    (hz : z ∈ s) : ∃ C, ∀ i, ‖F i z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb {z} (singleton_subset_iff.2 hz) isCompact_singleton
  exact ⟨C, fun i => hC i z (mem_singleton z)⟩

/-- A family bounded by a single constant on all of `s` is locally bounded on `s`. -/
theorem isLocallyBoundedOn_of_forall_norm_le {s : Set ℂ} {C : ℝ}
    (h : ∀ i, ∀ z ∈ s, ‖F i z‖ ≤ C) : IsLocallyBoundedOn F s :=
  fun _K hKs _hK => ⟨C, fun i z hz => h i z (hKs hz)⟩

/-- Every point of an open set admits a radius `r > 0` with `closedBall z (2 * r) ⊆ U`.

The doubled radius is what lets the Cauchy estimate below be applied at every point of
`ball z r`, not just at `z`. -/
private theorem exists_pos_closedBall_two_mul_subset (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ r > 0, closedBall z (2 * r) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    isCompact_singleton.exists_cthickening_subset_open hU (singleton_subset_iff.2 hz)
  refine ⟨δ / 2, by positivity, ?_⟩
  have htwo : 2 * (δ / 2) = δ := by ring
  rw [htwo]
  exact (closedBall_subset_cthickening (mem_singleton z) δ).trans hδU

section Estimates

/-- **Cauchy's estimate on a closed ball.** If `f` is holomorphic on an open set `U` containing
`closedBall c r` and `‖f‖ ≤ M` on that closed ball, then `‖deriv f c‖ ≤ M / r`.

This is Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` with its `DiffContOnCl`
hypothesis and its bound on the boundary circle both supplied from a sup bound on a closed ball
inside the domain of holomorphy, which is the form the family estimates below consume. -/
theorem norm_deriv_le_of_forall_mem_closedBall_norm_le (hf : DifferentiableOn ℂ f U) {c : ℂ}
    {r M : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ U)
    (hM : ∀ w ∈ closedBall c r, ‖f w‖ ≤ M) : ‖deriv f c‖ ≤ M / r := by
  have hd := hf.diffContOnCl_ball hsub
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd fun w hw =>
    hM w (sphere_subset_closedBall hw)

/-- **Cauchy's estimate, uniformly on a ball.** If `f` is holomorphic on an open set `U` containing
`closedBall c (2 * r)` and `‖f‖ ≤ M` on that closed ball, then `‖deriv f z‖ ≤ M / r` at *every*
point `z` of `ball c r`, not just at the centre.

Halving the radius is what leaves room to recentre `norm_deriv_le_of_forall_mem_closedBall_norm_le`
at an arbitrary `z ∈ ball c r`: the ball `closedBall z r` is still inside `closedBall c (2 * r)`. -/
theorem norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le (hf : DifferentiableOn ℂ f U)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : closedBall c (2 * r) ⊆ U)
    (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) {z : ℂ} (hz : z ∈ ball c r) :
    ‖deriv f z‖ ≤ M / r := by
  have hzc : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by have := (mem_ball.1 hz).le; linarith)
  exact norm_deriv_le_of_forall_mem_closedBall_norm_le hf hr (hzc.trans hsub)
    fun w hw => hM w (hzc hw)

/-- **A sup bound makes a holomorphic function Lipschitz on half the ball.** If `f` is holomorphic
on an open `U ⊇ closedBall c (2 * r)` and `‖f‖ ≤ M` there, then `f` moves points of `ball c r` by
at most `M / r` times the distance between them.

The constant `M / r` depends only on the sup bound and the radius, which is what makes this
estimate usable uniformly across a family; see `IsLocallyBoundedOn.equicontinuousOn`. -/
theorem dist_le_of_forall_mem_closedBall_two_mul_norm_le (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : closedBall c (2 * r) ⊆ U)
    (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) {z w : ℂ} (hz : z ∈ ball c r)
    (hw : w ∈ ball c r) : dist (f z) (f w) ≤ M / r * dist z w := by
  have hball : ball c r ⊆ U := fun x hx =>
    hsub (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hx))
  rw [dist_eq_norm, dist_eq_norm]
  exact (convex_ball c r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hf x (hball hx)).differentiableAt (hU.mem_nhds (hball hx)))
    (fun x hx => norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le hf hr hsub hM hx)
    hw hz

/-- The `LipschitzOnWith` form of `dist_le_of_forall_mem_closedBall_two_mul_norm_le`. -/
theorem lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hsub : closedBall c (2 * r) ⊆ U) (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M / r)) f (ball c r) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
  refine (dist_le_of_forall_mem_closedBall_two_mul_norm_le hU hf hr hsub hM hz hw).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg

/-- **The equicontinuity half of Montel's theorem.** A locally bounded family of holomorphic
functions on an open set `U ⊆ ℂ` is equicontinuous on `U`.

Around a point `z₀ ∈ U` pick `r > 0` with `closedBall z₀ (2 * r) ⊆ U`; local boundedness supplies
one constant `C` bounding the whole family on that compact ball, and
`dist_le_of_forall_mem_closedBall_two_mul_norm_le` then makes every member of the family
`C / r`-Lipschitz on `ball z₀ r`.  A single Lipschitz constant is a common continuity modulus. -/
theorem IsLocallyBoundedOn.equicontinuousOn (hb : IsLocallyBoundedOn F U) (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) : EquicontinuousOn F U := by
  intro z₀ hz₀
  refine EquicontinuousAt.equicontinuousWithinAt ?_ U
  obtain ⟨r, hr, hsub⟩ := exists_pos_closedBall_two_mul_subset hU hz₀
  obtain ⟨C, hC⟩ := hb _ hsub (isCompact_closedBall z₀ (2 * r))
  refine Metric.equicontinuousAt_of_continuity_modulus (fun z => C / r * dist z₀ z) ?_ F ?_
  · have hcont : Continuous fun z : ℂ => C / r * dist z₀ z :=
      continuous_const.mul (continuous_const.dist continuous_id)
    simpa using hcont.tendsto z₀
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz i
    exact dist_le_of_forall_mem_closedBall_two_mul_norm_le hU (hF i) hr hsub (hC i)
      (mem_ball_self hr) hz

/-- **The derivatives of a locally bounded family of holomorphic functions are locally bounded.**

On a compact `K ⊆ U` choose `δ > 0` with `cthickening δ K ⊆ U`; a bound `C` for the family on that
compact thickening bounds each derivative on `K` by `C / δ`, by Cauchy's estimate on
`closedBall z δ` for `z ∈ K`. -/
theorem IsLocallyBoundedOn.deriv (hb : IsLocallyBoundedOn F U) (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    IsLocallyBoundedOn (fun i => _root_.deriv (F i)) U := by
  intro K hKU hK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨C, hC⟩ := hb _ hδU hK.cthickening
  refine ⟨C / δ, fun i z hz => ?_⟩
  have hsub : closedBall z δ ⊆ cthickening δ K := closedBall_subset_cthickening hz δ
  exact norm_deriv_le_of_forall_mem_closedBall_norm_le (hF i) hδ (hsub.trans hδU)
    fun w hw => hC i w (hsub hw)

/-- The derivatives of a locally bounded family of holomorphic functions are equicontinuous.

The result follows by applying the preceding equicontinuity theorem to the locally bounded
derivative family. -/
theorem IsLocallyBoundedOn.equicontinuousOn_deriv (hb : IsLocallyBoundedOn F U) (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) : EquicontinuousOn (fun i => _root_.deriv (F i)) U :=
  (hb.deriv hU hF).equicontinuousOn hU fun i => (hF i).deriv hU

end Estimates

end TauCeti
