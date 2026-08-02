/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
public import TauCeti.Analysis.Semigroups.GrowthBound
public import TauCeti.Analysis.Semigroups.Identity
public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The generator determines the semigroup

Two strongly continuous semigroups on a real Banach space with the same infinitesimal generator
coincide. The proof is the classical interpolation argument: for `x` in the common generator
domain and a fixed time `t`, the orbit

`u ↦ S (t - u) (T u x)`

interpolates between `S t x` (at `u = 0`) and `T t x` (at `u = t`), and it is constant because
its right derivative vanishes: the derivative of the inner factor contributes the vector
`S (t - u) (A (T u x))`, and the derivative of the outer factor contributes its negative.

Differentiating the outer factor requires a two-sided derivative of a generator-domain orbit,
which is available at positive times through
`TauCeti.Semigroups.StronglyContinuousSemigroup.realOperator_hasDerivWithinAt_Ici`; both
contributions are recombined using the joint strong continuity recorded first in this file.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.tendsto_realOperator_apply`: strong continuity
  of `(u, x) ↦ S u x` in both arguments simultaneously, phrased along an arbitrary filter.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.continuousOn_realOperator_apply`: the
  `ContinuousOn` form of the previous result.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.realOperator_eq_of_generator_eq`: two
  semigroups with the same generator agree on the generator domain.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.eq_of_generator_eq` and
  `TauCeti.Semigroups.StronglyContinuousSemigroup.generator_injective`: the generator determines
  the semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.eq_id_of_generator_eq_zero` and
  `TauCeti.Semigroups.StronglyContinuousSemigroup.eq_ofBounded_of_generator_eq`: the two
  concrete identifications this makes available, namely that a semigroup with vanishing
  generator is the identity semigroup and that a semigroup whose generator is a bounded operator
  `A` is `t ↦ exp (t • A)`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.1.4.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Theorem 1.2.6.
-/

public section

noncomputable section

open Filter Set

open scoped Topology NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-! ## Joint strong continuity -/

/-- **Joint strong continuity**: if `f i → r` through nonnegative values and `g i → z`, then
`S (f i) (g i) → S r z`.

A C₀-semigroup is strongly, not uniformly, continuous, so this does not follow from continuity
of `u ↦ S.realOperator u` alone; the proof combines strong continuity at `r` with the uniform
operator bound supplied by a growth bound. -/
theorem tendsto_realOperator_apply {ι : Type*} {l : Filter ι} (S : StronglyContinuousSemigroup X)
    {f : ι → ℝ} {g : ι → X} {r : ℝ} {z : X} (hf : Tendsto f l (𝓝 r))
    (hf0 : ∀ᶠ i in l, 0 ≤ f i) (hr : 0 ≤ r) (hg : Tendsto g l (𝓝 z)) :
    Tendsto (fun i => S.realOperator (f i) (g i)) l (𝓝 (S.realOperator r z)) := by
  obtain ⟨omega, M, hb⟩ := S.existsGrowthBound
  have hM : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hb.one_le
  -- A single operator-norm bound valid for all times eventually visited by `f`.
  have hbound : ∀ᶠ i in l, ‖S.realOperator (f i)‖ ≤ M * Real.exp (|omega| * (r + 1)) := by
    filter_upwards [hf0, hf.eventually_lt_const (lt_add_one r)] with i hi0 hi1
    refine (hb.bound (f i) hi0).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM.le
    calc omega * f i ≤ |omega| * f i := mul_le_mul_of_nonneg_right (le_abs_self omega) hi0
      _ ≤ |omega| * (r + 1) := mul_le_mul_of_nonneg_left hi1.le (abs_nonneg omega)
  -- The argument moves: the operator norms are uniformly bounded, so this contribution vanishes.
  have h1 : Tendsto (fun i => S.realOperator (f i) (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => M * Real.exp (|omega| * (r + 1)) * ‖g i - z‖) ?_ ?_
    · filter_upwards [hbound] with i hi
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa using
        (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul (M * Real.exp (|omega| * (r + 1)))
  -- The time moves: this is strong continuity of the orbit of the fixed vector `z`.
  have h2 : Tendsto (fun i => S.realOperator (f i) z) l (𝓝 (S.realOperator r z)) := by
    have hfw : Tendsto f l (𝓝[Set.Ici 0] r) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf, hf0⟩
    simpa [Function.comp_def] using (S.realOperator_continuousWithinAt z r hr).tendsto.comp hfw
  have hsplit : ∀ i, S.realOperator (f i) (g i)
      = S.realOperator (f i) (g i - z) + S.realOperator (f i) z := by
    intro i
    rw [← ContinuousLinearMap.map_add, sub_add_cancel]
  simpa using (h1.add h2).congr fun i => (hsplit i).symm

/-- The `ContinuousOn` form of joint strong continuity: a continuous nonnegative time
reparametrization applied to a continuous vector-valued map gives a continuous orbit. -/
theorem continuousOn_realOperator_apply (S : StronglyContinuousSemigroup X) {s : Set ℝ}
    {f : ℝ → ℝ} {g : ℝ → X} (hf : ContinuousOn f s) (hf0 : ∀ u ∈ s, 0 ≤ f u)
    (hg : ContinuousOn g s) :
    ContinuousOn (fun u => S.realOperator (f u) (g u)) s := fun u hu =>
  S.tendsto_realOperator_apply (hf u hu) (eventually_nhdsWithin_of_forall hf0) (hf0 u hu) (hg u hu)

/-! ## Uniqueness of the semigroup generated by an operator -/

/-- The interpolation `u ↦ S (t - u) (T u x)` between the two semigroups has vanishing right
derivative at every `u ∈ [0, t)`.

The two contributions cancel: differentiating `T u x` produces `S (t - u) (A (T u x))`, and
differentiating `S (t - u)` produces its negative, because the common generator `A` computes both
derivatives. -/
private theorem hasDerivWithinAt_interpolate {S T : StronglyContinuousSemigroup X}
    (hgen : S.generator = T.generator) {t : ℝ} {x : X} (hx : x ∈ T.domain) {s : ℝ}
    (hs0 : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (fun u : ℝ => S.realOperator (t - u) (T.realOperator u x)) 0
      (Set.Ici s) s := by
  have hdom : S.domain = T.domain := by
    rw [← S.generator_domain, ← T.generator_domain, hgen]
  have hrpos : (0 : ℝ) < t - s := sub_pos.mpr hst
  set y : X := T.realOperator s x with hy_def
  have hyT : y ∈ T.domain := T.realOperator_mem_domain hs0 hx
  have hyS : y ∈ S.domain := by rw [hdom]; exact hyT
  have hyT' : y ∈ T.generator.domain := by rw [T.generator_domain]; exact hyT
  have hyS' : y ∈ S.generator.domain := by rw [S.generator_domain]; exact hyS
  set a : X := T.generator ⟨y, hyT'⟩
  have hSa : S.generator ⟨y, hyS'⟩ = a := @(LinearPMap.ext_iff.mp hgen).2 y hyS' hyT'
  -- The outer factor: a two-sided derivative of the orbit of `y ∈ D(A)` at the positive time
  -- `t - s`, composed with the reflection `u ↦ t - u`.
  have hpsi : HasDerivAt (fun u : ℝ => S.realOperator u y) (S.realOperator (t - s) a) (t - s) := by
    have h := S.realOperator_hasDerivWithinAt_Ici ⟨y, hyS⟩ hrpos.le
    rw [S.realOperator_generator_map hrpos.le ⟨y, hyS⟩] at h
    simp only [hSa] at h
    exact h.hasDerivAt (Ici_mem_nhds hrpos)
  have hrho : HasDerivAt (fun u : ℝ => S.realOperator (t - u) y)
      (-(S.realOperator (t - s) a)) s := by
    have hinner : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    simpa [Function.comp_def] using hpsi.scomp s hinner
  -- The inner factor: the defining difference quotient of the generator of `T` at `y`.
  have hshift : Tendsto (fun u : ℝ => u - s) (𝓝[>] s) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_sub_right s).tendsto s).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [Set.mem_Ioi] at hu ⊢
      linarith
  have hquot : Tendsto (fun u : ℝ => (u - s)⁻¹ • (T.realOperator (u - s) y - y))
      (𝓝[>] s) (𝓝 a) := by
    simpa [Function.comp_def, one_div] using (T.generator_tendsto ⟨y, hyT⟩).comp hshift
  have htime : Tendsto (fun u : ℝ => t - u) (𝓝[>] s) (𝓝 (t - s)) :=
    ((continuous_sub_left t).tendsto s).mono_left nhdsWithin_le_nhds
  have hterm1 : Tendsto (fun u : ℝ => S.realOperator (t - u)
      ((u - s)⁻¹ • (T.realOperator (u - s) y - y))) (𝓝[>] s) (𝓝 (S.realOperator (t - s) a)) :=
    S.tendsto_realOperator_apply htime
      ((htime.eventually_const_lt hrpos).mono fun _ h => h.le) hrpos.le hquot
  have hterm2 : Tendsto (slope (fun u : ℝ => S.realOperator (t - u) y) s) (𝓝[>] s)
      (𝓝 (-(S.realOperator (t - s) a))) :=
    hrho.tendsto_slope.mono_left (nhdsWithin_mono s fun _ hu => hu.ne')
  -- The slope of the interpolation splits into the two contributions.
  have hslope : ∀ u ∈ Set.Ioi s,
      slope (fun u : ℝ => S.realOperator (t - u) (T.realOperator u x)) s u
        = S.realOperator (t - u) ((u - s)⁻¹ • (T.realOperator (u - s) y - y))
          + slope (fun u : ℝ => S.realOperator (t - u) y) s u := by
    intro u hu
    have hus : 0 ≤ u - s := (sub_pos.mpr hu).le
    have hTu : T.realOperator u x = T.realOperator (u - s) y := by
      rw [hy_def, ← ContinuousLinearMap.comp_apply, ← T.realOperator_add (u - s) s hus hs0,
        sub_add_cancel]
    simp only [slope_def_module, hTu, map_smul, map_sub, smul_sub]
    abel
  have hIci : Set.Ici s \ {s} = Set.Ioi s := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => h.1.lt_of_ne (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hIci]
  have hsum := hterm1.add hterm2
  rw [add_neg_cancel] at hsum
  exact hsum.congr' (by filter_upwards [self_mem_nhdsWithin] with u hu using (hslope u hu).symm)

/-- Two strongly continuous semigroups with the same generator agree on the generator domain,
at every nonnegative time. -/
theorem realOperator_eq_of_generator_eq {S T : StronglyContinuousSemigroup X}
    (hgen : S.generator = T.generator) {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T.domain) :
    S.realOperator t x = T.realOperator t x := by
  have hcont : ContinuousOn (fun u : ℝ => S.realOperator (t - u) (T.realOperator u x))
      (Set.Icc 0 t) :=
    S.continuousOn_realOperator_apply (continuous_sub_left t).continuousOn
      (fun u hu => sub_nonneg.mpr hu.2)
      ((T.realOperator_continuousOn_Ici x).mono fun u hu => hu.1)
  have hderiv : ∀ u ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun u : ℝ => S.realOperator (t - u) (T.realOperator u x)) 0
        (Set.Ici u) u :=
    fun _ hu => hasDerivWithinAt_interpolate hgen hx hu.1 hu.2
  have heq := constant_of_has_deriv_right_zero hcont hderiv t (Set.right_mem_Icc.mpr ht)
  simp only [sub_self, sub_zero, S.realOperator_zero_apply, T.realOperator_zero_apply] at heq
  exact heq.symm

/-- **The generator determines the semigroup**: two strongly continuous semigroups on a real
Banach space with the same infinitesimal generator are equal ([EN] Thm. II.1.4). -/
theorem eq_of_generator_eq {S T : StronglyContinuousSemigroup X}
    (hgen : S.generator = T.generator) : S = T := by
  refine StronglyContinuousSemigroup.ext fun τ => ?_
  refine ContinuousLinearMap.ext_on (R₁ := ℝ) (s := (T.domain : Set X)) ?_ ?_
  · rw [Submodule.span_eq]
    exact T.dense_domain
  · intro x hx
    simpa using realOperator_eq_of_generator_eq hgen τ.coe_nonneg hx

/-- The infinitesimal generator is injective on strongly continuous semigroups. -/
theorem generator_injective :
    Function.Injective (StronglyContinuousSemigroup.generator (X := X)) :=
  fun _ _ h => eq_of_generator_eq h

/-- A strongly continuous semigroup whose generator vanishes is the identity semigroup. -/
theorem eq_id_of_generator_eq_zero {S : StronglyContinuousSemigroup X} (h : S.generator = 0) :
    S = StronglyContinuousSemigroup.id X :=
  eq_of_generator_eq (h.trans id_generator_eq_zero.symm)

/-- A strongly continuous semigroup whose generator is the bounded operator `A`, defined on all
of `X`, is the operator exponential `t ↦ exp (t • A)`. -/
theorem eq_ofBounded_of_generator_eq {S : StronglyContinuousSemigroup X} (A : X →L[ℝ] X)
    (h : S.generator = (A : X →ₗ[ℝ] X).toPMap ⊤) : S = ofBounded A :=
  eq_of_generator_eq (h.trans (ofBounded_generator A).symm)

end StronglyContinuousSemigroup

/-- Two contraction semigroups with the same generator are equal. -/
theorem ContractionSemigroup.eq_of_generator_eq {S T : ContractionSemigroup X}
    (hgen : S.toStronglyContinuousSemigroup.generator
      = T.toStronglyContinuousSemigroup.generator) :
    S = T := by
  have h := StronglyContinuousSemigroup.eq_of_generator_eq hgen
  refine ContractionSemigroup.ext fun τ => ?_
  rw [← S.toStronglyContinuousSemigroup_apply, ← T.toStronglyContinuousSemigroup_apply, h]

end TauCeti.Semigroups

end
