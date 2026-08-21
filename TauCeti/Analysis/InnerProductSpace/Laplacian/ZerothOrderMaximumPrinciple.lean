/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
-- Support only: the shared maximizer step is proof machinery, not part of this file's API.
import TauCeti.Analysis.InnerProductSpace.Laplacian.BarrierMaximizer

/-!
# The weak maximum principle for `-Δ + c` with a nonnegative zeroth-order term

`TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple` proves the weak maximum
principle for the bare Laplacian: a subharmonic (`0 ≤ Δ f`) function on a compact set is bounded on
all of `K` by any bound it satisfies on `frontier K`. The next step of the PDE roadmap (Lane C,
item 13, "then for general elliptic `L` (sign condition `c ≥ 0`)") is to restore the zeroth-order
term, i.e. to allow the operator `L u = -Δ u + c u` with a **nonnegative** coefficient `c`.

The sign condition `c ≥ 0` is load-bearing: it is exactly what lets the maximum principle survive
the extra term. A subsolution of `L`, `L f ≤ 0`, is a function with `c · f ≤ Δ f` on the interior,
and the conclusion is one-sided in the standard `sup u ≤ sup_{∂} u⁺` shape: a subsolution bounded
by a **nonnegative** `m` on the frontier is bounded by `m` throughout. (The nonnegativity of `m` is
needed once `c ≠ 0`; on the set where `f ≤ 0 ≤ m` the estimate is automatic, and the argument only
has to control the set where `f` is positive, where `c · f ≥ 0` makes `f` subharmonic.)

The proof reuses the perturbation `f + ε‖·‖²` of the bare-Laplacian file, but replaces the
strictly-subharmonic boundary principle by the maximizer step `TauCeti.le_of_isMaxOn_add_smul` of
`TauCeti.Analysis.InnerProductSpace.Laplacian.BarrierMaximizer`, run here with no drift and the
quadratic barrier. At a maximizer of the perturbation the bound `f z ≤ m` either holds already, or
`m < f z` puts `f z` above the nonnegative `m`, which forces `Δ(f + ε‖·‖²) > 0` and so contradicts
local maximality. Letting `ε → 0` gives the bound.

## Main declarations

* `TauCeti.le_of_mul_le_laplacian_le_frontier`: **weak maximum principle for `-Δ + c`, `c ≥ 0`**. A
  continuous function that is `C²` on the interior with `c · f ≤ Δ f` (a subsolution of `-Δ + c`)
  and `c ≥ 0` there is bounded by any nonnegative `m` it respects on `frontier K`.
* `TauCeti.le_of_mul_le_laplacian_le_of_le_frontier`: **comparison principle for `-Δ + c`,
  `c ≥ 0`**. A subsolution `f` and a supersolution `g` ordered by `f ≤ g` on `frontier K` stay
  ordered `f ≤ g` on all of `K`.
* `TauCeti.ge_of_laplacian_le_mul_ge_frontier`: the dual weak minimum principle for supersolutions
  (`Δ f ≤ c · f`), bounded below by any nonpositive lower bound on the frontier.
* `TauCeti.abs_le_of_laplacian_eq_mul_abs_le_frontier`: a solution of `-Δ u + c u = 0`
  (`Δ f = c · f`) is bounded on `K` by any bound its absolute value respects on `frontier K`.
* `TauCeti.eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier`: **uniqueness for the Dirichlet problem
  for `-Δ + c`**. Two functions with the same `Δ · - c · ·` on the interior and the same boundary
  values agree on `K`.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Nontrivial

variable [Nontrivial E]

/-- **Weak maximum principle for the operator `-Δ + c` with `c ≥ 0`.**

Let `K` be compact. If `f` is continuous on `K`, is `C²` on `interior K`, and is a subsolution of
`-Δ + c` there (`c x * f x ≤ Δ f x`) with a nonnegative coefficient (`0 ≤ c x`), then any
**nonnegative** bound `m` that `f` respects on `frontier K` bounds `f` on all of `K`.

The nonnegativity of `m` cannot be dropped once `c ≠ 0`; it encodes the `sup u ≤ sup_{∂} u⁺` shape
of the estimate. -/
theorem le_of_mul_le_laplacian_le_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x) (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  have hfrpos : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  refine le_of_forall_pos_exists_isMaxOn_perturbation hK.isBounded hxK fun ε hε => ?_
  have hgcont : ContinuousOn (fun y : E => f y + ε • ‖y‖ ^ 2) K := hcont.add (by fun_prop)
  -- The perturbation attains its maximum over `K` at some point `z`.
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hgcont
  -- The maximizer step is the shared one, run with no drift and the quadratic barrier `‖·‖²`,
  -- whose Laplacian `2 · finrank` is the strict positivity it asks for.
  refine ⟨z, hzK, hzmax, le_of_isMaxOn_add_smul (v := 0) hε (fun h => hcd h) (fun hz hlt => ?_)
    (fun hz => hbdry hz) hzK (fun _ => (contDiff_norm_sq ℝ).contDiffAt) (fun _ => ?_) hzmax⟩
  · simpa using (mul_nonneg (hc hz) (hm.trans hlt.le)).trans (hsub hz)
  · simpa [laplacian_norm_sq] using mul_pos two_pos hfrpos

/-- **Comparison principle for `-Δ + c` with `c ≥ 0`.**

Let `K` be compact and let `f`, `g` be continuous on `K` and `C²` on `interior K`, with a
nonnegative coefficient `c` there. If `f` is a subsolution and `g` a supersolution of `-Δ + c`
(`c · f ≤ Δ f` and `Δ g ≤ c · g`) and `f ≤ g` on `frontier K`, then `f ≤ g` on all of `K`. This is
the two-function form of `le_of_mul_le_laplacian_le_frontier`. -/
theorem le_of_mul_le_laplacian_le_of_le_frontier {K : Set E} (hK : IsCompact K) {c f g : E → ℝ}
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → Δ g x ≤ c x * g x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hxK
  -- Bound the difference `f - g` above by `0` via the weak maximum principle for `-Δ + c`.
  have hdiff : ∀ ⦃y⦄, y ∈ K → (f - g) y ≤ 0 :=
    le_of_mul_le_laplacian_le_frontier (c := c) hK le_rfl (hfcont.sub hgcont)
      (fun y hy => (hfcd hy).sub (hgcd hy)) hc
      (fun y hy => by
        rw [(hfcd hy).laplacian_sub (hgcd hy), Pi.sub_apply, mul_sub]
        linarith [hsub hy, hsuper hy])
      (fun y hy => by
        rw [Pi.sub_apply]
        linarith [hbdry hy])
  have := hdiff hxK
  rw [Pi.sub_apply] at this
  linarith

/-- **Weak minimum principle for supersolutions of `-Δ + c` with `c ≥ 0`.**

The dual of `le_of_mul_le_laplacian_le_frontier`: a continuous, `C²`, supersolution
(`Δ f x ≤ c x * f x`) with a nonnegative coefficient is bounded below on `K` by any **nonpositive**
lower bound it respects on `frontier K`. -/
theorem ge_of_laplacian_le_mul_ge_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ} {m : ℝ}
    (hm : m ≤ 0) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x) (hsuper : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_mul_le_laplacian_le_frontier (c := c) (f := -f) (m := -m) hK (by linarith)
    hcont.neg (fun y hy => (hcd hy).neg) hc
    (fun y hy => by
      have h1 : Δ (-f) y = -Δ f y := by rw [congrFun laplacian_neg y, Pi.neg_apply]
      rw [h1, Pi.neg_apply, mul_neg]
      linarith [hsuper hy])
    (fun y hy => by rw [Pi.neg_apply]; linarith [hbdry hy]) hxK
  rw [Pi.neg_apply] at hle
  linarith

/-- A solution of `-Δ u + c u = 0` (`Δ f = c · f`) with `c ≥ 0`, continuous on a compact set `K` and
`C²` on its interior, is bounded on `K` by any bound `M` its absolute value respects on
`frontier K`. -/
theorem abs_le_of_laplacian_eq_mul_abs_le_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hsol : ∀ ⦃x⦄, x ∈ interior K → Δ f x = c x * f x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M := by
  intro x hxK
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · exact ge_of_laplacian_le_mul_ge_frontier (c := c) hK (by linarith) hcont hcd hc
      (fun y hy => (hsol hy).le) (fun y hy => (abs_le.mp (hbdry hy)).1) hxK
  · exact le_of_mul_le_laplacian_le_frontier (c := c) hK hM hcont hcd hc
      (fun y hy => (hsol hy).ge) (fun y hy => (abs_le.mp (hbdry hy)).2) hxK

/-- **Uniqueness for the Dirichlet problem for `-Δ + c` with `c ≥ 0`.**

If `f` and `g` are continuous on a compact set `K`, `C²` on `interior K` with the same source term
`Δ · - c · ·` there (so both solve `-Δ u + c u = h` for one `h`), and agree on `frontier K`, then
they agree on all of `K`. -/
theorem eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier {K : Set E} (hK : IsCompact K)
    {c f g : E → ℝ} (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x - c x * f x = Δ g x - c x * g x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x = g x) :
    Set.EqOn f g K := by
  intro x hxK
  have habs : |(f - g) x| ≤ 0 := by
    refine abs_le_of_laplacian_eq_mul_abs_le_frontier (c := c) (f := f - g) hK le_rfl
      (hfcont.sub hgcont) (fun y hy => (hfcd hy).sub (hgcd hy)) hc (fun y hy => ?_)
      (fun y hy => ?_) hxK
    · rw [(hfcd hy).laplacian_sub (hgcd hy), Pi.sub_apply, mul_sub]
      linarith [hlap hy]
    · rw [Pi.sub_apply, hbdry hy]
      simp
  rw [Pi.sub_apply] at habs
  exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)

end Nontrivial

end TauCeti

end
