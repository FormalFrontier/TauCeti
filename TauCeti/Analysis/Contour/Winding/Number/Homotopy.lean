/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.Analysis.Contour.Winding.Proximity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Homotopy invariance of the winding number

The winding number of a piecewise-`C¹` path about `w` is invariant under an arbitrary continuous
fixed-endpoint homotopy through `ℂ \ {w}`. The proof regularizes finitely many horizontal slices
by Mathlib's endpoint-preserving Bernstein approximations, then chains the resulting smooth paths
with proximity invariance of the winding number.

The earlier smooth route remains available at the level where it has distinct content: a `C²`
homotopy preserves the actual curve integral of the Cauchy-kernel `1`-form by Mathlib's Poincaré
theorem.

## Main results

* `windingNumber_eq_two_pi_I_inv_mul_curveIntegral` identifies Tau Ceti's raw-function winding
  number of a piecewise-`C¹` path with Mathlib's curve integral of the Cauchy-kernel `1`-form.
* `isPiecewiseC1On_eval_of_smoothPathHomotopy` supplies piecewise-`C¹` regularity for every path
  in a smooth homotopy.
* `curveIntegral_inv_sub_smul_id_eq_of_pathHomotopy` is the smooth Stokes step: a `C²` homotopy
  through `ℂ \ {w}` preserves the curve integral of the Cauchy-kernel `1`-form.
* `exists_isPiecewiseC1On_dist_lt_of_continuousMap` gives endpoint-preserving smooth
  approximations of continuous complex paths.
* `windingNumber_eq_of_pathHomotopy` proves the Layer 0 homotopy invariance result without any
  regularity hypothesis on the homotopy.
* `isNullHomologous_iff_of_pathHomotopy` transfers null-homology across a homotopy in the ambient
  set.

## Provenance

The continuous homotopy step reuses Mathlib's `bernsteinApproximation_uniform`; the independent
smooth curve-integral statement reuses
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`. No formal source
is vendored. Homotopy invariance of the classical winding number is standard complex analysis; see
the references in the Contour Integration roadmap.
-/

public section

noncomputable section

open scoped unitInterval
open MeasureTheory Set

namespace TauCeti.Contour

/-- The polynomial on `ℝ` underlying Mathlib's `n`-th Bernstein approximation of `f` on the
unit interval. Keeping the polynomial formula on all of `ℝ` makes its contour regularity
immediate, while `bernsteinCurve_apply` connects it to Mathlib's uniform approximation theorem. -/
private def bernsteinCurve (n : ℕ) (f : C(I, ℂ)) (t : ℝ) : ℂ :=
  ∑ k : Fin (n + 1),
    ((n.choose k : ℝ) * t ^ (k : ℕ) * (1 - t) ^ (n - (k : ℕ))) • f (bernstein.z k)

private theorem bernsteinCurve_apply (n : ℕ) (f : C(I, ℂ)) (t : I) :
    bernsteinCurve n f t = bernsteinApproximation n f t := by
  simp only [bernsteinCurve, bernsteinApproximation.apply, bernstein_apply]

private theorem contDiff_bernsteinCurve (n : ℕ) (f : C(I, ℂ)) :
    ContDiff ℝ ⊤ (bernsteinCurve n f) := by
  unfold bernsteinCurve
  fun_prop

/-- **Endpoint-preserving smooth approximation of a continuous complex path.** Every continuous
map from the unit interval to `ℂ` is uniformly approximated, to any positive tolerance, by a
globally smooth curve with the same values at `0` and `1`.

The approximants are Mathlib's Bernstein approximations, interpreted as polynomials on `ℝ`.
This is the regularization step used to compare the merely continuous intermediate paths of a
path homotopy with Tau Ceti's piecewise-`C¹` winding number. -/
theorem exists_isPiecewiseC1On_dist_lt_of_continuousMap (f : C(I, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → ℂ, IsPiecewiseC1On γ 0 1 ∧ γ 0 = f 0 ∧ γ 1 = f 1 ∧
      ∀ t : I, dist (γ t) (f t) < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (bernsteinApproximation_uniform f) ε hε
  let n := max N 1
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
  refine ⟨bernsteinCurve n f,
    IsPiecewiseC1On.of_contDiffOn ((contDiff_bernsteinCurve n f).contDiffOn.of_le (by norm_num)),
    ?_, ?_, ?_⟩
  · exact (bernsteinCurve_apply n f 0).trans (bernsteinApproximation.apply_zero n f)
  · exact (bernsteinCurve_apply n f 1).trans (bernsteinApproximation.apply_one hn f)
  · intro t
    rw [bernsteinCurve_apply]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt (hN n hnN)

private def indexForm (w : ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ

private def indexFormDeriv (w z : ℂ) : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  ((1 : ℂ →L[ℂ] ℂ).smulRight (-((z - w) ^ 2)⁻¹) |>.smulRight
    (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private theorem hasFDerivAt_indexForm {w z : ℂ} (hzw : z ≠ w) :
    HasFDerivAt (indexForm w) (indexFormDeriv w z) z := by
  have hscalar : HasDerivAt (fun y : ℂ => (y - w)⁻¹) (-((z - w) ^ 2)⁻¹) z := by
    convert ((hasDerivAt_id z).sub_const w).inv (sub_ne_zero.mpr hzw) using 1
    · rfl
    · rfl
    · rfl
    · simp [div_eq_mul_inv]
  exact (hscalar.hasFDerivAt.smul_const (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private theorem indexFormDeriv_apply_comm (w z u v : ℂ) :
    indexFormDeriv w z u v = indexFormDeriv w z v u := by
  have happly (x y : ℂ) : indexFormDeriv w z x y = x * (-((z - w) ^ 2)⁻¹) * y := by
    simp [indexFormDeriv, mul_assoc]
  rw [happly, happly]
  ring

/-- For a piecewise-`C¹` path avoiding `w`, its winding number about `w` is the normalized curve
integral of the closed `1`-form `z ↦ (z - w)⁻¹ dz`. This is the bridge from Tau Ceti's raw-function
winding number to Mathlib's path-based curve integral. -/
theorem windingNumber_eq_two_pi_I_inv_mul_curveIntegral {x y w : ℂ} {p : Path x y}
    (hp : IsPiecewiseC1On p.extend 0 1) (havoid : ∀ t : Set.Icc (0 : ℝ) 1, p t ≠ w) :
    windingNumber p.extend 0 1 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
  have havoid_extend : ∀ t ∈ Set.uIcc (0 : ℝ) 1, p.extend t ≠ w := by
    rw [Set.uIcc_of_le zero_le_one]
    intro t ht
    rw [Path.extend_apply p ht]
    exact havoid ⟨t, ht⟩
  rw [windingNumber_eq_integral_of_avoidance hp.continuousOn havoid_extend
      (intervalIntegrable_inv_sub_mul_deriv hp.continuousOn havoid_extend
        hp.intervalIntegrable_deriv),
    curveIntegral_eq_intervalIntegral_deriv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- If the extension of a path homotopy is `C²` on the unit square, then every intermediate
path, extended constantly from the unit interval to `ℝ`, is piecewise `C¹` on `[0, 1]`. -/
theorem isPiecewiseC1On_eval_of_smoothPathHomotopy {x y : ℂ} {p q : Path x y} (φ : p.Homotopy q)
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) (Set.Icc 0 1))
    (s : I) :
    IsPiecewiseC1On (φ.eval s).extend 0 1 := by
  apply IsPiecewiseC1On.of_contDiffOn
  rw [Set.uIcc_of_le zero_le_one]
  have hs : ContDiffOn ℝ 1
      ((fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) ∘
        fun t : ℝ => ((s, t) : ℝ × ℝ)) (Set.Icc 0 1) :=
    (hφsmooth.of_le (by norm_num)).comp (by fun_prop)
      (fun t ht => by
        simpa [Prod.le_def] using ⟨⟨s.2.1, ht.1⟩, ⟨s.2.2, ht.2⟩⟩)
  exact hs.congr fun _ _ => by simp [Path.extend, Path.Homotopy.eval]

/-- **A path homotopy avoiding `w` preserves the curve integral of the Cauchy kernel.** Paths with
the same endpoints, joined by a `C²` homotopy through `ℂ \ {w}`, have equal integrals of the
`1`-form `z ↦ (z - w)⁻¹ dz`. -/
theorem curveIntegral_inv_sub_smul_id_eq_of_pathHomotopy {x y w : ℂ} {p q : Path x y}
    (φ : p.Homotopy q)
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) (Set.Icc 0 1))
    (haway : ∀ z ∈ Set.range φ, z ≠ w) :
    (∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in q, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
  -- `indexForm w` is the private abbreviation for this integrand; fold it so the closedness and
  -- derivative lemmas below, which are stated for it, apply.
  change (∫ᶜ z in p, indexForm w z) = ∫ᶜ z in q, indexForm w z
  have hrange : IsClosed (Set.range φ) :=
    (isCompact_range φ.toHomotopy.continuous).isClosed
  have hclosedForm : ∀ z ∈ Set.range φ,
      HasFDerivWithinAt (indexForm w) (indexFormDeriv w z) (Set.range φ) z :=
    fun z hz ↦ (hasFDerivAt_indexForm (haway z hz)).hasFDerivWithinAt
  have hcontinuousForm : ContinuousOn (indexForm w) (closure (Set.range φ)) := by
    rw [hrange.closure_eq]
    exact fun z hz ↦ (hasFDerivAt_indexForm (haway z hz)).continuousAt.continuousWithinAt
  have hboundary :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
      (t := Set.range φ) (ω := indexForm w) (dω := indexFormDeriv w)
      (fun s _ t _ ↦ Set.mem_range_self (s, t)) hclosedForm hcontinuousForm
      (fun z _ u _ v _ ↦ indexFormDeriv_apply_comm w z u v) hφsmooth
  have heval_zero :
      φ.toHomotopy.evalAt 0 = (Path.refl x).cast p.source q.source := by
    ext t
    exact φ.source t
  have heval_one :
      φ.toHomotopy.evalAt 1 = (Path.refl y).cast p.target q.target := by
    ext t
    exact φ.target t
  rw [heval_zero, heval_one] at hboundary
  simpa only [curveIntegral_cast, curveIntegral_refl, add_zero] using hboundary

/-- A continuous path homotopy avoiding `w` stays a uniformly positive distance from `w`, since
its domain is the compact unit square. -/
private theorem exists_pathHomotopy_dist_lower_bound {x y w : ℂ} {p q : Path x y}
    (φ : p.Homotopy q) (havoid : ∀ st : I × I, φ st ≠ w) :
    ∃ ρ > 0, ∀ st : I × I, ρ ≤ dist (φ st) w := by
  have hcompact : IsCompact (Set.range φ) := isCompact_range φ.toHomotopy.continuous
  have hnonempty : (Set.range φ).Nonempty := Set.range_nonempty φ
  have hw : w ∉ Set.range φ := by
    rintro ⟨st, hst⟩
    exact havoid st hst
  refine ⟨Metric.infDist w (Set.range φ),
    (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hw, fun st => ?_⟩
  simpa [dist_comm] using Metric.infDist_le_dist_of_mem (x := w) (Set.mem_range_self st)

/-- Uniform continuity lets a path homotopy be divided into finitely many nearby horizontal
slices. The stages use `bernstein.z`, the same uniform mesh used by the smooth approximants. -/
private theorem exists_nat_dist_pathHomotopy_stage_lt {x y : ℂ} {p q : Path x y}
    (φ : p.Homotopy q) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ k : Fin N, ∀ t : I,
      dist (φ (bernstein.z k.succ, t)) (φ (bernstein.z k.castSucc, t)) < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous φ.toHomotopy.continuous) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hmesh : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hN
  refine ⟨N, Nat.ne_of_gt (by exact_mod_cast hNpos), fun k t => hclose ?_⟩
  simp only [Prod.dist_eq, dist_self]
  have hsub : (((k : ℕ) + 1 : ℕ) : ℝ) / N - ((k : ℕ) : ℝ) / N = 1 / N := by
    push_cast
    ring
  simp only [bernstein.z, Subtype.dist_eq, Real.dist_eq, Fin.succ, Fin.castSucc, Fin.val_castAdd]
  rw [hsub, abs_of_pos (by positivity), max_eq_left (by positivity)]
  exact hmesh

/-- **Homotopy invariance of the winding number off the curve.** Two piecewise-`C¹` paths with the
same endpoints, joined through `ℂ \ {w}` by an arbitrary continuous path homotopy, have the same
winding number about `w`. No differentiability of the homotopy is required. -/
theorem windingNumber_eq_of_pathHomotopy {x y w : ℂ} {p q : Path x y} (φ : p.Homotopy q)
    (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1)
    (havoid : ∀ st : I × I, φ st ≠ w) :
    windingNumber p.extend 0 1 w = windingNumber q.extend 0 1 w := by
  obtain ⟨ρ, hρ, hρle⟩ := exists_pathHomotopy_dist_lower_bound φ havoid
  obtain ⟨N, hN, hstage⟩ := exists_nat_dist_pathHomotopy_stage_lt φ (div_pos hρ (by norm_num :
    (0 : ℝ) < 5))
  let slice : Fin (N + 1) → C(I, ℂ) := fun k => (φ.eval (bernstein.z k)).toContinuousMap
  choose γ hγ using fun k : Fin (N + 1) =>
    exists_isPiecewiseC1On_dist_lt_of_continuousMap (slice k) (ε := ρ / 5)
      (div_pos hρ (by norm_num))
  have hγpw (k : Fin (N + 1)) : IsPiecewiseC1On (γ k) 0 1 := (hγ k).1
  have hγclose (k : Fin (N + 1)) (t : I) : dist (γ k t) (φ (bernstein.z k, t)) < ρ / 5 := by
    change dist (γ k t) ((φ.eval (bernstein.z k)) t) < ρ / 5
    simpa only [slice, Path.coe_toContinuousMap] using (hγ k).2.2.2 t
  have hγzero (k : Fin (N + 1)) : γ k 0 = x := by
    calc
      γ k 0 = slice k 0 := (hγ k).2.1
      _ = x := by simp [slice]
  have hγone (k : Fin (N + 1)) : γ k 1 = y := by
    calc
      γ k 1 = slice k 1 := (hγ k).2.2.1
      _ = y := by simp [slice]
  have hγdist (k : Fin (N + 1)) (t : I) : 4 * ρ / 5 < dist (γ k t) w := by
    have htriangle := dist_triangle (φ (bernstein.z k, t)) (γ k t) w
    have hlower := hρle (bernstein.z k, t)
    have hclose := hγclose k t
    rw [dist_comm (φ (bernstein.z k, t)) (γ k t)] at htriangle
    linarith
  -- Consecutive smooth approximants are close enough for the dog-on-a-leash lemma.
  have hadjacent (k : Fin N) : windingNumber (γ k.succ) 0 1 w =
      windingNumber (γ k.castSucc) 0 1 w := by
    apply (hγpw k.castSucc).windingNumber_eq_of_dist_lt_dist_of_eq_endpoints (hγpw k.succ)
      ((hγzero k.castSucc).trans (hγzero k.succ).symm)
      ((hγone k.castSucc).trans (hγone k.succ).symm)
    intro t ht
    let tI : I := ⟨t, by simpa [Set.uIcc_of_le zero_le_one] using ht⟩
    have h₁ := hγclose k.succ tI
    have h₂ := hstage k tI
    have h₃ := hγclose k.castSucc tI
    have hupper : dist (γ k.succ t) (γ k.castSucc t) < 3 * ρ / 5 := by
      calc
        dist (γ k.succ t) (γ k.castSucc t) ≤
            dist (γ k.succ t) (φ (bernstein.z k.succ, tI)) +
              dist (φ (bernstein.z k.succ, tI)) (γ k.castSucc t) := dist_triangle _ _ _
        _ ≤ dist (γ k.succ t) (φ (bernstein.z k.succ, tI)) +
              (dist (φ (bernstein.z k.succ, tI)) (φ (bernstein.z k.castSucc, tI)) +
                dist (φ (bernstein.z k.castSucc, tI)) (γ k.castSucc t)) := by
                  gcongr
                  exact dist_triangle _ _ _
        _ < 3 * ρ / 5 := by rw [dist_comm (φ _ ) (γ k.castSucc t)]; linarith
    exact hupper.trans (by linarith [hγdist k.castSucc tI])
  -- Chain the finitely many approximants from homotopy time `0` to time `1`.
  have hchain : ∀ k : ℕ, ∀ hk : k ≤ N,
      windingNumber (γ ⟨k, Nat.lt_succ_iff.mpr hk⟩) 0 1 w = windingNumber (γ 0) 0 1 w := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hkN : k < N := Nat.lt_of_succ_le hk
      exact (hadjacent ⟨k, hkN⟩).trans (ih hkN.le)
  have hchain_final : windingNumber (γ (Fin.last N)) 0 1 w = windingNumber (γ 0) 0 1 w := by
    simpa only [Fin.last] using hchain N le_rfl
  -- The first and last approximants are close to the original endpoint paths.
  have hstart : windingNumber (γ 0) 0 1 w = windingNumber p.extend 0 1 w := by
    apply hp.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints (hγpw 0)
      (by rw [Path.extend_zero, hγzero]) (by rw [Path.extend_one, hγone])
    intro t ht
    let tI : I := ⟨t, by simpa [Set.uIcc_of_le zero_le_one] using ht⟩
    have hp_apply : p.extend t = φ (0, tI) := by
      calc
        p.extend t = p tI := Path.extend_apply p tI.property
        _ = φ (0, tI) := by simp
    have hclose : dist (γ 0 t) (p.extend t) < ρ / 5 := by
      rw [hp_apply]
      simpa using hγclose 0 tI
    exact hclose.trans (by rw [hp_apply]; linarith [hρle (0, tI)])
  have hend : windingNumber q.extend 0 1 w = windingNumber (γ (Fin.last N)) 0 1 w := by
    apply (hγpw (Fin.last N)).windingNumber_eq_of_dist_lt_dist_of_eq_endpoints hq
      (by rw [Path.extend_zero, hγzero]) (by rw [Path.extend_one, hγone])
    intro t ht
    let tI : I := ⟨t, by simpa [Set.uIcc_of_le zero_le_one] using ht⟩
    have hq_apply : q.extend t = φ (1, tI) := by
      calc
        q.extend t = q tI := Path.extend_apply q tI.property
        _ = φ (1, tI) := by simp
    have hz : bernstein.z (Fin.last N) = 1 := bernstein.z_last hN
    have hφz : φ (bernstein.z (Fin.last N), tI) = φ (1, tI) := by rw [hz]
    have hclose : dist (q.extend t) (γ (Fin.last N) t) < ρ / 5 := by
      rw [hq_apply, ← hφz, dist_comm]
      exact hγclose (Fin.last N) tI
    exact hclose.trans (by linarith [hγdist (Fin.last N) tI])
  exact hstart.symm.trans (hchain_final.symm.trans hend.symm)

/-- Null-homology in `Ω` is invariant under an arbitrary continuous path homotopy whose image lies
in `Ω`. The endpoint paths themselves are piecewise `C¹`; no regularity is assumed of the
intermediate paths. -/
theorem isNullHomologous_iff_of_pathHomotopy {x y : ℂ} {p q : Path x y} {Ω : Set ℂ}
    (φ : p.Homotopy q)
    (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1)
    (hφΩ : ∀ st : I × I, φ st ∈ Ω) :
    IsNullHomologous p.extend 0 1 Ω ↔ IsNullHomologous q.extend 0 1 Ω := by
  constructor
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      (windingNumber_eq_of_pathHomotopy φ hp hq
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))).symm
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      windingNumber_eq_of_pathHomotopy φ hp hq
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))

end TauCeti.Contour

end
