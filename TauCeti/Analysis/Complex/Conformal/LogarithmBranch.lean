/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.GlobalBranch
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# The logarithm: a germ that continues in the punctured plane but has no branch there

`Conformal/GlobalBranch.lean` proves that on a **simply connected** domain a germ continuing
along every path is the germ of one holomorphic function. `Conformal/Continuation.lean` asserts,
in the docstring of `TauCeti.ContinuesInside`, the classical example that shows the hypothesis
cannot be dropped: *the germ of `Complex.log` at `1` continues inside `ℂ \ {0}`, and continues
inside the slit plane, but is single-valued only on the latter.* This file proves that assertion,
and reads off from it that the punctured plane is not simply connected.

## The branch based at a point

Everything runs on one elementary object: for `a : ℂ` the function

`logBranch a z = a + Complex.log (z * Complex.exp (-a))`

is the branch of the logarithm **based at `a`** — the holomorphic function that takes the value
`a` at the point `Complex.exp a`, obtained by translating Mathlib's principal branch so that its
cut is rotated away from that point. It really is a logarithm
(`TauCeti.exp_logBranch`, `TauCeti.hasDerivAt_logBranch`), it is the principal branch for `a = 0`
(`TauCeti.logBranch_zero`), and two branches agree at a point of the punctured plane as soon as
the value of one of them lies within `π` of the base point of the other
(`TauCeti.logBranch_eq_logBranch`) — a strip condition, because `Complex.log_exp` inverts
`Complex.exp` exactly on the strip `-π < im ≤ π`.

That comparison is what makes the branches into a continuation: if `L` is any continuous lift of
a path through `Complex.exp`, then `t ↦ logBranch (L t)` is an analytic continuation along the
path `t ↦ Complex.exp (L t)`, because nearby parameter times have nearby base points
(`TauCeti.isAnalyticContinuationAlong_logBranch`). The statement is for an arbitrary parameter
space and parameter set, as `TauCeti.IsAnalyticContinuationAlong` is.

## The two halves of the example

*Continuation everywhere.* A path in `ℂ \ {0}` starting at `1` lifts through `Complex.exp`,
because `Complex.exp : ℂ → ℂ \ {0}` is a covering map (Mathlib's
`Complex.isCoveringMap_exp`), and the lift may be started at `0`; the branches based along that
lift continue the principal branch (`TauCeti.continuesAlong_log`), so the germ continues inside
the whole punctured plane (`TauCeti.continuesInside_log`). Inside the slit plane there is nothing
to do: the principal branch is holomorphic there (`TauCeti.continuesInside_log_slitPlane`).

*No branch on the punctured plane.* Around the unit circle the lift is `t ↦ 2 π i t`, so the
terminal branch is based at `2 π i` and the terminal germ is `log + 2 π i`, not `log`. By uniqueness
of continuation along a fixed path this is forced for *every* continuation of the germ around that
loop (`TauCeti.eventuallyEq_add_two_pi_mul_I_of_isAnalyticContinuationAlong`), and a holomorphic
function on `ℂ \ {0}` would be its own continuation, so no such function has the germ of `log` at
`1` (`TauCeti.not_exists_analyticOnNhd_eventuallyEq_log`).

Feeding the two halves into `TauCeti.ContinuesInside.exists_analyticOnNhd` gives
`TauCeti.not_isSimplyConnected_compl_singleton_zero`: the punctured plane is not simply
connected. So the monodromy theorem is sharp in the strongest sense — its hypothesis fails for the
very first domain one would try to drop it for, and the failure is detected analytically, by the
logarithm itself.

## Main results

* `TauCeti.logBranch` — the branch of the logarithm based at a point, with its basic API.
* `TauCeti.logBranch_eq_logBranch` — two branches agree where the strip condition holds.
* `TauCeti.isAnalyticContinuationAlong_logBranch` — the branches along a continuous lift of a
  path through `Complex.exp` are an analytic continuation along that path.
* `TauCeti.continuesAlong_log`, `TauCeti.continuesInside_log` — the germ of `Complex.log` at `1`
  continues along every path in the punctured plane, hence inside the punctured plane.
* `TauCeti.eventuallyEq_add_two_pi_mul_I_of_isAnalyticContinuationAlong` — continuing that germ
  once around the origin adds `2 π i`.
* `TauCeti.not_exists_analyticOnNhd_eventuallyEq_log` — no function analytic on the punctured
  plane has the germ of `Complex.log` at `1`.
* `TauCeti.not_isSimplyConnected_compl_singleton_zero` — the punctured plane is not simply
  connected.

## Relation to the roadmap and to Mathlib

This completes the L4 layer "analytic continuation & the reflection principle" of
`TauCetiRoadmap/ConformalMapping/README.md` on its continuation side, by discharging the
sharpness claim that `Conformal/Continuation.lean` records in prose and that
`Conformal/GlobalBranch.lean` leaves open. Layer L4 lies outside the roadmap's shim-deletion
clause for the upstream Riemann-mapping effort leanprover-community/mathlib4#33505, which
contains no continuation or monodromy material.

Nothing is vendored. The covering-map structure of the complex exponential
(`Complex.isCoveringMap_exp`, `Mathlib/Analysis/Complex/CoveringMap.lean`, by Junyan Xu) and the
path-lifting property of covering maps (`IsCoveringMap.exists_path_lifts`,
`Mathlib/Topology/Homotopy/Lifting.lean`) are consumed as they stand, as are the principal
branch and its analyticity (`Complex.log`, `Complex.log_exp`, `analyticAt_clog`).

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
* W. Rudin, *Real and Complex Analysis*, Ch. 16.
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval
open scoped Real

variable {X : Type*} [TopologicalSpace X]

/-! ### The branch of the logarithm based at a point -/

/-- The branch of the logarithm **based at `a`**: the translate of Mathlib's principal branch
that takes the value `a` at the point `Complex.exp a`.

Like `Complex.log` itself this is a total function; it is a genuine holomorphic logarithm exactly
where `z * Complex.exp (-a)` misses the branch cut, which is a neighbourhood of `Complex.exp a`.
-/
noncomputable def logBranch (a z : ℂ) : ℂ := a + Complex.log (z * Complex.exp (-a))

/-- The defining formula for `TauCeti.logBranch`. -/
theorem logBranch_apply (a z : ℂ) : logBranch a z = a + Complex.log (z * Complex.exp (-a)) := by
  rw [logBranch]

/-- The branch based at `0` is Mathlib's principal branch. -/
@[simp]
theorem logBranch_zero : logBranch 0 = Complex.log := by
  funext z
  rw [logBranch_apply]
  simp

/-- **Every branch is a logarithm**: exponentiating it returns the point, wherever that point is
nonzero. -/
theorem exp_logBranch (a : ℂ) {z : ℂ} (hz : z ≠ 0) : Complex.exp (logBranch a z) = z := by
  have ha : Complex.exp a ≠ 0 := Complex.exp_ne_zero a
  rw [logBranch_apply, Complex.exp_add, Complex.exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)),
    Complex.exp_neg]
  field_simp

/-- The branch based at `a` takes the value `a` at the base point `Complex.exp a`. -/
@[simp]
theorem logBranch_exp (a : ℂ) : logBranch a (Complex.exp a) = a := by
  rw [logBranch_apply, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, Complex.log_one,
    add_zero]

/-- The branch based at `a` is analytic wherever the translated point misses the branch cut. -/
theorem analyticAt_logBranch {a z : ℂ} (h : z * Complex.exp (-a) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (logBranch a) z := by
  have hfun : logBranch a = fun z => a + Complex.log (z * Complex.exp (-a)) :=
    funext (logBranch_apply a)
  rw [hfun]
  exact analyticAt_const.add ((analyticAt_id.mul analyticAt_const).clog h)

/-- **Every branch has the derivative `z⁻¹`**, wherever it is analytic. -/
theorem hasDerivAt_logBranch {a z : ℂ} (h : z * Complex.exp (-a) ∈ Complex.slitPlane) :
    HasDerivAt (logBranch a) z⁻¹ z := by
  have ha : Complex.exp (-a) ≠ 0 := Complex.exp_ne_zero _
  have hfun : logBranch a = fun z => a + Complex.log (z * Complex.exp (-a)) :=
    funext (logBranch_apply a)
  have hmul : HasDerivAt (fun z : ℂ => z * Complex.exp (-a)) (Complex.exp (-a)) z := by
    have h := (hasDerivAt_id z).mul_const (Complex.exp (-a))
    rwa [one_mul] at h
  have hcomp := (Complex.hasDerivAt_log h).comp z hmul
  rw [hfun]
  refine (hcomp.const_add a).congr_deriv ?_
  field_simp

/-- **Comparison of two branches.** Two branches of the logarithm take the same value at a
nonzero point as soon as the value of one of them lies in the strip of height `2 π` centred at
the base point of the other.

This is the whole content of "the branches fit together": `Complex.exp` is injective exactly on
such a strip, so the two candidate values, which have the same exponential, must coincide. -/
theorem logBranch_eq_logBranch {a b z : ℂ} (hz : z ≠ 0) (h₁ : -π < (logBranch b z - a).im)
    (h₂ : (logBranch b z - a).im ≤ π) :
    logBranch a z = logBranch b z := by
  have hzb : z * Complex.exp (-b) ≠ 0 := mul_ne_zero hz (Complex.exp_ne_zero _)
  have heq : Complex.log (z * Complex.exp (-b)) + (b - a) = logBranch b z - a := by
    rw [logBranch_apply]; ring
  have hsplit : z * Complex.exp (-b) * Complex.exp (b - a) = z * Complex.exp (-a) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hkey : Complex.log (z * Complex.exp (-b) * Complex.exp (b - a))
      = Complex.log (z * Complex.exp (-b)) + (b - a) := by
    conv_lhs => rw [← Complex.exp_log hzb]
    rw [← Complex.exp_add]
    refine Complex.log_exp ?_ ?_
    · rw [heq]; exact h₁
    · rw [heq]; exact h₂
  rw [logBranch_apply a z, ← hsplit, hkey, logBranch_apply b z]
  ring

/-! ### The branches along a lift form a continuation -/

/-- **The branches based along a continuous lift are an analytic continuation.** If `L` is
continuous on the parameter set `s`, then `t ↦ logBranch (L t)` is an analytic continuation along
the path `t ↦ Complex.exp (L t)`.

At each parameter time the carried branch is analytic at the path point, because the translated
point is `1`; and the carried germ is locally constant because nearby times have base points less
than `π` apart, which is exactly the strip condition of `TauCeti.logBranch_eq_logBranch`. -/
theorem isAnalyticContinuationAlong_logBranch {L : X → ℂ} {s : Set X} (hL : ContinuousOn L s) :
    IsAnalyticContinuationAlong (fun t => logBranch (L t)) (fun t => Complex.exp (L t)) s where
  continuousOn := hL.cexp
  analyticAt t _ := analyticAt_logBranch (by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    exact Complex.one_mem_slitPlane)
  locallyEq t ht := by
    have hLt : Tendsto L (𝓝[s] t) (𝓝 (L t)) := hL t ht
    filter_upwards [Metric.tendsto_nhds.1 hLt π Real.pi_pos] with u hu
    have hdist : ‖L u - L t‖ < π := by rwa [dist_eq_norm] at hu
    have hmem : Complex.exp (L u) * Complex.exp (-L u) ∈ Complex.slitPlane := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      exact Complex.one_mem_slitPlane
    have hcont : ContinuousAt (logBranch (L u)) (Complex.exp (L u)) :=
      (analyticAt_logBranch hmem).continuousAt
    have hten : Tendsto (fun z => ‖logBranch (L u) z - L t‖) (𝓝 (Complex.exp (L u)))
        (𝓝 ‖L u - L t‖) := by
      have hnorm : ContinuousAt (fun z => ‖logBranch (L u) z - L t‖) (Complex.exp (L u)) :=
        (hcont.sub continuousAt_const).norm
      have h : Tendsto (fun z => ‖logBranch (L u) z - L t‖) (𝓝 (Complex.exp (L u)))
          (𝓝 ‖logBranch (L u) (Complex.exp (L u)) - L t‖) := hnorm.tendsto
      rwa [logBranch_exp] at h
    filter_upwards [hten.eventually_lt_const hdist,
      isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (Complex.exp_ne_zero (L u)))] with z hzlt hz0
    have habs := (Complex.abs_im_le_norm (logBranch (L u) z - L t)).trans_lt hzlt
    exact (logBranch_eq_logBranch (Set.mem_compl_singleton_iff.mp hz0) (abs_lt.mp habs).1
      (abs_lt.mp habs).2.le).symm

/-! ### The logarithm continues along every path in the punctured plane -/

/-- **The germ of `Complex.log` at `1` continues along every path in the punctured plane.**

The continuation is explicit: lift the path through `Complex.exp`, which is possible because that
map is a covering of `ℂ \ {0}`, and carry the branch based at the lift. -/
theorem continuesAlong_log {c : I → ℂ} (hc : Continuous c) (hc0 : c 0 = 1)
    (hcne : ∀ x, c x ≠ 0) : ContinuesAlong Complex.log c := by
  obtain ⟨Γ, hΓ, hΓ0⟩ :=
    Complex.isCoveringMap_exp.exists_path_lifts
      (⟨fun x => ⟨c x, hcne x⟩, by fun_prop⟩ : C(I, {z : ℂ // z ≠ 0})) 0
      (Subtype.ext (by simp [hc0]))
  have hexp : ∀ x, Complex.exp (Γ x) = c x := fun x =>
    congrArg Subtype.val (congrFun hΓ x)
  refine continuesAlong_iff_exists.mpr ⟨fun t => logBranch (Γ t), ?_, ?_⟩
  · have h := isAnalyticContinuationAlong_logBranch (X := I) (L := fun x => (Γ x : ℂ))
      (s := Set.univ) Γ.continuous.continuousOn
    simpa only [hexp] using h
  · simp only [hΓ0, logBranch_zero]
    exact Filter.EventuallyEq.rfl

/-- **The germ of `Complex.log` at `1` continues inside the punctured plane.** This is the
hypothesis of the monodromy theorem `TauCeti.ContinuesInside.exists_analyticOnNhd`, satisfied on
a domain that is not simply connected. -/
theorem continuesInside_log : ContinuesInside Complex.log ({0}ᶜ : Set ℂ) 1 :=
  ContinuesInside.of_forall fun _ hc hcU hc0 =>
    continuesAlong_log hc hc0 fun x => Set.mem_compl_singleton_iff.mp (hcU x)

/-- **The germ of `Complex.log` at `1` continues inside the slit plane**, where the principal
branch is already single-valued.

The base point is that of `TauCeti.continuesInside_log`, so that the two halves of the claim in
the docstring of `TauCeti.ContinuesInside` compare directly. A base point outside the slit plane
would make the statement vacuous, since no path can start there and stay in the domain; the
general statement, for any base point of any open set on which a function is holomorphic, is
`TauCeti.ContinuesInside.of_differentiableOn`. -/
theorem continuesInside_log_slitPlane :
    ContinuesInside Complex.log Complex.slitPlane 1 :=
  ContinuesInside.of_differentiableOn Complex.isOpen_slitPlane fun _ hz =>
    (Complex.differentiableAt_log hz).differentiableWithinAt

/-! ### Nontrivial monodromy around the origin -/

/-- The branches based along `t ↦ 2 π i t` continue the logarithm once around the unit circle. -/
private theorem isAnalyticContinuationAlong_logBranch_circle :
    IsAnalyticContinuationAlong (fun t : I => logBranch (2 * π * Complex.I * (t : ℝ)))
      (fun t : I => Complex.exp (2 * π * Complex.I * (t : ℝ))) Set.univ :=
  isAnalyticContinuationAlong_logBranch (Continuous.continuousOn (by fun_prop))

/-- **Continuing the logarithm once around the origin adds `2 π i`.** Every analytic continuation
along the unit-circle loop `t ↦ exp (2 π i t)` that starts at the germ of `Complex.log` at `1`
ends at the germ of `Complex.log + 2 π i` there.

The explicit continuation is the family of branches based along the lift `t ↦ 2 π i t`, whose
terminal member is based at `2 π i`; uniqueness of continuation along a fixed path
(`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`) forces every other continuation to agree with
it. -/
theorem eventuallyEq_add_two_pi_mul_I_of_isAnalyticContinuationAlong {f : I → ℂ → ℂ}
    (hf : IsAnalyticContinuationAlong f
      (fun t : I => Complex.exp (2 * π * Complex.I * (t : ℝ))) Set.univ)
    (hf0 : f 0 =ᶠ[𝓝 1] Complex.log) :
    f 1 =ᶠ[𝓝 1] fun z => Complex.log z + 2 * π * Complex.I := by
  have hzero : (2 : ℂ) * π * Complex.I * ((0 : I) : ℝ) = 0 := by norm_num
  have hone : (2 : ℂ) * π * Complex.I * ((1 : I) : ℝ) = 2 * π * Complex.I := by norm_num
  have hstart : f 0 =ᶠ[𝓝 (Complex.exp (2 * π * Complex.I * ((0 : I) : ℝ)))]
      logBranch (2 * π * Complex.I * ((0 : I) : ℝ)) := by
    rw [hzero, Complex.exp_zero, logBranch_zero]
    exact hf0
  have hmid := hf.eventuallyEq isAnalyticContinuationAlong_logBranch_circle isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ 1) hstart
  rw [hone, Complex.exp_two_pi_mul_I] at hmid
  refine hmid.trans (Filter.EventuallyEq.of_eq (funext fun z => ?_))
  have hexp : Complex.exp (-(2 * π * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [logBranch_apply, hexp, mul_one, add_comm]

/-- **The logarithm has no branch on the punctured plane.** No function analytic on `ℂ \ {0}`
has the germ of `Complex.log` at `1`: such a function would be its own continuation around the
unit circle, and would therefore differ from itself by `2 π i`. -/
theorem not_exists_analyticOnNhd_eventuallyEq_log :
    ¬ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F ({0}ᶜ : Set ℂ) ∧ F =ᶠ[𝓝 1] Complex.log := by
  rintro ⟨F, hF, hFlog⟩
  have hloop : IsAnalyticContinuationAlong (fun _ : I => F)
      (fun t : I => Complex.exp (2 * π * Complex.I * (t : ℝ))) Set.univ :=
    .const (Continuous.continuousOn (by fun_prop)) fun _ _ =>
      hF _ (Set.mem_compl_singleton_iff.mpr (Complex.exp_ne_zero _))
  have h := eventuallyEq_add_two_pi_mul_I_of_isAnalyticContinuationAlong hloop hFlog
  have h1 := (hFlog.symm.trans h).eq_of_nhds
  rw [Complex.log_one] at h1
  simp only [zero_add] at h1
  exact (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) h1.symm

/-- **The punctured plane is not simply connected**, proved analytically: were it simply
connected, the monodromy theorem `TauCeti.ContinuesInside.exists_analyticOnNhd` would turn
`TauCeti.continuesInside_log` into a branch of the logarithm on it, and
`TauCeti.not_exists_analyticOnNhd_eventuallyEq_log` says there is none.

Read the other way round, this is the sharpness of that monodromy theorem: its
simple-connectivity hypothesis is not removable, and the logarithm on `ℂ \ {0}` is the witness. -/
theorem not_isSimplyConnected_compl_singleton_zero :
    ¬ IsSimplyConnected ({0}ᶜ : Set ℂ) := fun h =>
  not_exists_analyticOnNhd_eventuallyEq_log
    (continuesInside_log.exists_analyticOnNhd isOpen_compl_singleton h
      (Set.mem_compl_singleton_iff.mpr one_ne_zero))

end TauCeti
