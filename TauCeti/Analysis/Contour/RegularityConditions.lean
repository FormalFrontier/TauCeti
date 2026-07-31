/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Contour.Argument.Lift

/-!
# The Hungerbühler–Wasem crossing angle and regularity conditions (A′) and (B)

For a curve `γ : ℝ → ℂ` on `[a, b]` and an integrand `f : ℂ → ℂ`, this file defines the **crossing
angle** and the **flatness** of `γ` at a time, and the roadmap's two Hungerbühler–Wasem regularity
conditions at its on-curve singularities: the geometric flatness condition **(A′)** and the analytic
sector-cancellation condition **(B)**, the two regularity hypotheses of the generalized residue
theorem (HW Thm 3.3), evaluating the Cauchy principal value `PV ∮_γ f`. Condition (A′) asks that
at each prescribed singularity `s ∈ S` the curve `γ` be **flat of order equal to the order of `f`'s
pole there** — with a one-sided tangent line at a simple pole, hugged ever tighter at a higher-order
pole — and that it meet each `s` only finitely often. Condition (B) governs poles of order
`> 1`, coupling the Laurent principal part of `f` at each such pole with the entry/exit tangents of
`γ` there, via a sector-cancellation identity; simple poles need no sector condition.

## Main definitions

* `crossingAngle γ t₀` — the model-sector opening angle in `[0, 2π)`, from the exit tangent `L₊`
  to the reversed entry tangent `−L₋` (`mod 2π`), where `L₋`, `L₊` are the one-sided limits of
  `deriv γ` from the left and right at `t₀`. Junk when a one-sided tangent fails to exist; a smooth
  crossing gives `π` (`crossingAngle_eq_pi`). Meaningful at the corners/crossings of a
  piecewise-`C¹` curve.
* `basepointAngle γ a b` — the analogous opening angle at the join `γ a = γ b` of a closed curve,
  from the outgoing tangent at `a` to the reversed incoming tangent at `b`.
* `FlatOfOrder γ t₀ n` — `γ` is **flat of order `n`** at `t₀` (HW Def. 3.2): from each side the
  perpendicular distance from `γ t` to a one-sided tangent line at `γ t₀` is `o(‖γ t − γ t₀‖ⁿ)`.
  Order `1` gives a one-sided tangent line; larger `n` hugs the line more tightly.
* `FlatOfOrderBasepoint γ a b n` — the analogue at the join `γ a = γ b` of a closed curve, for the
  outgoing branch at `a` (from the right) and the incoming branch at `b` (from the left).
* `flatOfOrder_of_eventually_collinear` — a curve whose one-sided branches at `t₀` eventually stay
  on a line through `γ t₀` is flat there to **every** order; the two one-sided directions may
  differ, so a corner at `t₀` is allowed.
* `ConditionAprime γ a b f S` — HW condition (A′), a structure requiring `γ` to meet each `s ∈ S`
  finitely often (`finite_crossings`) and be flat of order `n` wherever `f` has a pole of order `n`
  there (`interior`, `basepoint`). Pole orders come from `f` via `meromorphicOrderAt`; `S` selects
  the singularities.
* `SectorCompatible f z₀ θ` — the one-crossing Hungerbühler–Wasem sector condition, a structure with
  fields `angle_rational` (`θ` is a rational multiple of `π`) and `laurent_compatible` (the Laurent
  principal part of `f` at `z₀` resonates with `θ`).
* `ConditionB γ a b f` — HW condition (B), a structure imposing `SectorCompatible` at every
  higher-order (order `> 1`) on-curve pole of `f`: at each interior crossing (`ConditionB.interior`)
  and at the basepoint (`ConditionB.basepoint`).
* `FlatOfOrder.of_le` / `FlatOfOrderBasepoint.of_le` and `pow_unit_tangent_eq_of_resonance` /
  `pow_unit_tangent_eq_of_basepoint_resonance` — the consuming bridges, at interior crossings
  and at the join: flatness restricts downward in the order, and the sector resonance
  `k · θ ∈ 2π · ℤ` at the crossing angle is the power equation of the unit tangent
  directions.
* `crossingAngle_eq_of_tendsto` / `basepointAngle_eq_of_tendsto` — the characteristic equations,
  evaluating each angle from one-sided `Tendsto` hypotheses on `deriv γ`. Downstream files cannot
  unfold the definitions (their bodies are not exposed), so these are the intended entry points.
* `coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div` — the crossing angle, read in
  `Real.Angle`, is exactly what the two boundary arguments of a crossing window carry beyond the
  argument swept between the window endpoints. This is the geometric identification the per-window
  principal value (`perWindow_truncated_integral_tendsto`) needs, and the `Real.Angle` form is the
  exact one:
  `Complex.arg` is additive only mod `2π`.

Both conditions read the on-curve pole orders of `f` from `meromorphicOrderAt`. Condition (B) needs
no explicit singular set — it fires **intrinsically** at the times `t₀` where
`meromorphicOrderAt f (γ t₀) < -1` (a pole of order `> 1`), so it is `S`-free. Condition (A′) is
imposed at the prescribed set `S` (selecting the singularities), with the required flatness order
taken from `f`. Both match the roadmap signatures and the way the residue theorem consumes them.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (`angleAtCrossing`, `FlatOfOrder`,
and `SatisfiesConditionB`), specialised to the raw-function (`γ : ℝ → ℂ` on `[a, b]`) design of the
contour-integration roadmap. `FlatOfOrder` here uses HW Def. 3.2's tangent-*line* (orthogonal
projection) distance, so it is speed-independent at every order. Condition (A′) matches the flatness
order to `f`'s pole order at each `s ∈ S`; condition (B) detects the higher-order poles of
`f` intrinsically via `meromorphicOrderAt`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **Crossing angle** of `γ : ℝ → ℂ` at a time `t₀`, valued in `[0, 2π)`: the opening angle of the
model sector, from the exit tangent `L₊` to the reversed entry tangent `−L₋`, taken `mod 2π`. Here
`L₋ = lim_{t → t₀⁻} γ'(t)`, `L₊ = lim_{t → t₀⁺} γ'(t)` are the one-sided limits of `deriv γ`. This
is the orientation of Hungerbühler–Wasem's model sector-curve, whose arc of opening angle `α` runs
counterclockwise from the exit ray to the reversed entry ray and contributes `α / 2π`
(`indexIntegral_arc`). The normalization keeps it nonnegative: a **smooth** crossing
(`L₊ = L₋`) gives `π`, as in HW §3, and a cusp (`L₋ = -L₊`) gives `0`, the tangents alone not
distinguishing a degenerate sector from a full turn. As a `limUnder`-based value it is junk when a
one-sided tangent fails to exist; it is meaningful at the corners/crossings of a piecewise-`C¹`
curve. -/
def crossingAngle (γ : ℝ → ℂ) (t₀ : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)) - Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)))

/-- **Basepoint crossing angle** of a closed curve `γ` on `[a, b]`, valued in `[0, 2π)`: the opening
angle at the join `γ a = γ b`, from the outgoing tangent `L₊` to the reversed incoming tangent
`−L₋`, where `L₋ = lim_{t → b⁻} γ'(t)` and `L₊ = lim_{t → a⁺} γ'(t)`. This is `crossingAngle`'s
analogue at the basepoint, where the two tangents come from opposite ends of `[a, b]`; a smooth join
(`L₊ = L₋`) gives `π`. -/
def basepointAngle (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] b) (deriv γ)) - Complex.arg (limUnder (𝓝[>] a) (deriv γ)))

/-- For a nonzero `L : ℂ`, the normalized angle from `L` to `−L` is `π`. This is the engine behind
the smooth-crossing values of `crossingAngle` and `basepointAngle`. -/
private theorem toIcoMod_arg_neg_sub_arg {L : ℂ} (hL : L ≠ 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg (-L) - Complex.arg L) = Real.pi := by
  -- `arg (-L) = arg L + π` holds in `Real.Angle`; transporting back to `ℝ` leaves `π` up to a
  -- multiple of `2π`, which the `[0, 2π)` normalization discards.
  have hangle : ((Complex.arg (-L) - Complex.arg L : ℝ) : Real.Angle) = (Real.pi : ℝ) := by
    rw [Real.Angle.coe_sub, Complex.arg_neg_coe_angle hL]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle
  have hshift : Complex.arg (-L) - Complex.arg L = Real.pi + k • (2 * Real.pi) := by
    rw [zsmul_eq_mul]
    linarith
  rw [hshift, toIcoMod_add_zsmul]
  exact (toIcoMod_eq_self Real.two_pi_pos).mpr
    (Set.mem_Ico.mpr ⟨Real.pi_nonneg, by rw [zero_add]; linarith [Real.pi_pos]⟩)

/-- **Characteristic equation for `crossingAngle`.** When `deriv γ` tends to `L_L` from the left
and to `L_R` from the right at `t₀`, the crossing angle is the normalized angle from the exit
tangent `L_R` to the reversed entry tangent `−L_L`. This is the form consumers should rewrite with:
the body of `crossingAngle` is not exposed across module boundaries, so it cannot be unfolded
downstream. -/
theorem crossingAngle_eq_of_tendsto {γ : ℝ → ℂ} {t₀ : ℝ} {L_R L_L : ℂ}
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    crossingAngle γ t₀ =
      toIcoMod Real.two_pi_pos 0 (Complex.arg (-L_L) - Complex.arg L_R) := by
  rw [crossingAngle, h_R.limUnder_eq, h_L.limUnder_eq]

/-- **Characteristic equation for `basepointAngle`.** The join analogue of
`crossingAngle_eq_of_tendsto`, with the outgoing tangent limit at `a` and the incoming one
at `b`. -/
theorem basepointAngle_eq_of_tendsto {γ : ℝ → ℂ} {a b : ℝ} {L_R L_L : ℂ}
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] a) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] b) (𝓝 L_L)) :
    basepointAngle γ a b =
      toIcoMod Real.two_pi_pos 0 (Complex.arg (-L_L) - Complex.arg L_R) := by
  rw [basepointAngle, h_R.limUnder_eq, h_L.limUnder_eq]

/-- `crossingAngle γ t₀` lies in `[0, 2π)`, the range of the model-sector normalization. Its two
projections `crossingAngle_nonneg`/`crossingAngle_lt_two_pi` are the `@[simp]` normal forms. -/
theorem crossingAngle_mem_Ico (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)) - Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)))
  rw [zero_add] at h
  rw [crossingAngle]
  exact h

@[simp] theorem crossingAngle_nonneg (γ : ℝ → ℂ) (t₀ : ℝ) : 0 ≤ crossingAngle γ t₀ :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).1

@[simp] theorem crossingAngle_lt_two_pi (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ < 2 * Real.pi :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).2

/-- **Smooth-crossing value.** If the one-sided tangents of `γ` at `t₀` agree and are nonzero, the
crossing angle is `π`: there is no genuine corner. -/
theorem crossingAngle_eq_pi {γ : ℝ → ℂ} {t₀ : ℝ}
    (h : limUnder (𝓝[<] t₀) (deriv γ) = limUnder (𝓝[>] t₀) (deriv γ))
    (hL : limUnder (𝓝[>] t₀) (deriv γ) ≠ 0) :
    crossingAngle γ t₀ = Real.pi := by
  rw [crossingAngle, h]
  exact toIcoMod_arg_neg_sub_arg hL

/-- **The crossing angle is what the boundary arguments carry beyond the endpoint sweep.** Fix
non-zero one-sided tangent limits `L_L`, `L_R` at `t₀` and non-zero `w_L`, `w_R`. Then the two
sum `arg (−L_L / w_L) + arg (w_R / L_R)` is the argument `arg (w_R / w_L)` swept from `w_L` to
`w_R`, plus exactly the crossing angle.

The intended reading takes `w_L = γ (t₀ − r) − s` and `w_R = γ (t₀ + r) − s` at the ends of a
crossing window, where the first two
arguments on the right are precisely the boundary arguments of the per-window principal value
(`perWindow_truncated_integral_tendsto`): the identity says that limit sees the crossing angle plus
a term depending only on the window endpoints. Nothing in the proof uses that reading, so `w_L` and
`w_R` are left free.

The equation is between `Real.Angle`s. That is not a weakening for convenience but the exact
statement: `Complex.arg` is additive only mod `2π`, and `crossingAngle` is itself a `toIcoMod`
normalization, so no `ℝ`-valued form is available without pinning a branch. -/
theorem coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div {γ : ℝ → ℂ} {t₀ : ℝ}
    {L_R L_L w_L w_R : ℂ} (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0) (hw_L : w_L ≠ 0) (hw_R : w_R ≠ 0)
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    (crossingAngle γ t₀ : Real.Angle)
      = ((((-L_L) / w_L).arg : ℝ) : Real.Angle) + (((w_R / L_R).arg : ℝ) : Real.Angle)
        - (((w_R / w_L).arg : ℝ) : Real.Angle) := by
  rw [crossingAngle_eq_of_tendsto h_R h_L, Real.Angle.coe_toIcoMod,
    Complex.arg_div_coe_angle (neg_ne_zero.mpr hL_L) hw_L, Complex.arg_div_coe_angle hw_R hL_R,
    Complex.arg_div_coe_angle hw_R hw_L, Real.Angle.coe_sub]
  abel

/-- `basepointAngle γ a b` lies in `[0, 2π)`, the range of the model-sector normalization. Its two
projections `basepointAngle_nonneg`/`basepointAngle_lt_two_pi` are the `@[simp]` normal forms. -/
theorem basepointAngle_mem_Ico (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] b) (deriv γ)) - Complex.arg (limUnder (𝓝[>] a) (deriv γ)))
  rw [zero_add] at h
  rw [basepointAngle]
  exact h

@[simp] theorem basepointAngle_nonneg (γ : ℝ → ℂ) (a b : ℝ) : 0 ≤ basepointAngle γ a b :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).1

@[simp] theorem basepointAngle_lt_two_pi (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b < 2 * Real.pi :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).2

/-- **Smooth-join value.** If the incoming tangent at `b` and the outgoing tangent at `a` agree and
are nonzero, the basepoint angle is `π`: the closed curve joins smoothly. -/
theorem basepointAngle_eq_pi {γ : ℝ → ℂ} {a b : ℝ}
    (h : limUnder (𝓝[<] b) (deriv γ) = limUnder (𝓝[>] a) (deriv γ))
    (hL : limUnder (𝓝[>] a) (deriv γ) ≠ 0) :
    basepointAngle γ a b = Real.pi := by
  rw [basepointAngle, h]
  exact toIcoMod_arg_neg_sub_arg hL

/-- **Flatness of order `n`** of `γ : ℝ → ℂ` at `t₀` (HW Def. 3.2): from each side, `γ` hugs a
one-sided **tangent line** through `γ t₀`, its perpendicular distance to that line vanishing faster
than `‖γ t − γ t₀‖ⁿ`. There are nonzero one-sided directions `v_plus` (right) and `v_minus` (left)
for which the component of `γ t − γ t₀` orthogonal to `v` — of length
`|((γ t − γ t₀) · conj v).im| / ‖v‖`, the distance from `γ t` to the line `γ t₀ + ℝ • v` — is
`o(‖γ t − γ t₀‖ⁿ)` as `t → t₀⁺`, symmetrically as `t → t₀⁻`. Order `1` is first-order tangency to a
line; larger `n` forces it to hug the line ever more tightly. Distance is measured to the tangent
*line*, not to a moving point on it, so flatness ignores the along-tangent speed, as in HW. -/
def FlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
        =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
    (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
        =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n)

/-- **Flatness of order `n` at the basepoint** of a closed curve `γ` on `[a, b]`, at the join
`γ a = γ b`: the outgoing branch at `a` (from the right) and the incoming branch at `b` (from the
left) each hug their one-sided tangent line in the perpendicular sense of `FlatOfOrder`, to order
`n`. The two branches come from opposite ends of `[a, b]`. -/
def FlatOfOrderBasepoint (γ : ℝ → ℂ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖) =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
    (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖) =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n)

/-- `FlatOfOrder` unfolded: the one-sided little-o clauses that build the flatness hypothesis, so
downstream code can construct or destruct it without unfolding the definition. -/
theorem flatOfOrder_iff {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ} :
    FlatOfOrder γ t₀ n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
        (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) :=
  Iff.rfl

/-- **A curve with straight one-sided branches at `t₀` is flat there to every order.** If, on each
side of `t₀`, the curve eventually stays on the line through `γ t₀` with direction `v` — which for
complex numbers is exactly the vanishing of `Im ((γ t - γ t₀) * conj v)` — then the perpendicular
deviation is identically `0` near `t₀`, hence `o` of anything. The two directions are allowed to
differ, so a curve with a *corner* at `t₀` still qualifies. This supplies the **flatness** clause
of Hungerbühler–Wasem condition (A′) for indented and polygonal contours; the finite-crossing and
basepoint clauses are separate and must be established independently. -/
theorem flatOfOrder_of_eventually_collinear {γ : ℝ → ℂ} {t₀ : ℝ} {v_plus v_minus : ℂ}
    (hv_plus : v_plus ≠ 0) (hv_minus : v_minus ≠ 0) (n : ℕ)
    (hplus : ∀ᶠ t in 𝓝[>] t₀, ((γ t - γ t₀) * star v_plus).im = 0)
    (hminus : ∀ᶠ t in 𝓝[<] t₀, ((γ t - γ t₀) * star v_minus).im = 0) :
    FlatOfOrder γ t₀ n := by
  rw [flatOfOrder_iff]
  refine ⟨v_plus, v_minus, hv_plus, hv_minus, ?_, ?_⟩ <;>
    refine (Asymptotics.isLittleO_zero _ _).congr' ?_ Filter.EventuallyEq.rfl
  · filter_upwards [hplus] with t ht
    rw [ht]
    simp
  · filter_upwards [hminus] with t ht
    rw [ht]
    simp

/-- `FlatOfOrderBasepoint` unfolded: the two one-sided little-o clauses (outgoing at `a`, incoming
at `b`) that build the basepoint flatness hypothesis, exposed without unfolding the definition. -/
theorem flatOfOrderBasepoint_iff {γ : ℝ → ℂ} {a b : ℝ} {n : ℕ} :
    FlatOfOrderBasepoint γ a b n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
        (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n) :=
  Iff.rfl

/-- **Hungerbühler–Wasem condition (A′)** for `γ` along `[a, b]`, at the prescribed singular set `S`
of the integrand `f`: `γ` meets each singularity only **finitely often** and is **flat** to the
order of `f`'s pole there. Wherever `γ` meets a point of `S` at which `f` has a pole of order `n`,
the curve is flat of order `n` — tangent to a line at a simple pole, flatter at a higher pole — and
each such `s` is met only finitely often. Together with
condition (B) it is a regularity hypothesis of the generalized residue theorem (HW Thm 3.3). It is
imposed at each *interior* crossing `t₀` strictly between the endpoints and at the *basepoint*
`γ (min a b)` (`= γ (max a b)` for a closed curve), so a join singularity is not left free. The
clauses are stated over `min`/`max`, so the condition is invariant under swapping the endpoints
(`conditionAprime_comm`), like the curve predicates it accompanies. Pole orders are read from
`f` via `meromorphicOrderAt`; `S` selects the singularities to constrain. -/
structure ConditionAprime (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (S : Finset ℂ) : Prop where
  /-- Each prescribed singularity `s ∈ S` is met only **finitely often** on `[[a, b]]`: the
  crossing set `[[a, b]] ∩ γ ⁻¹' {s}` is finite. -/
  finite_crossings : ∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite
  /-- At each interior crossing of a prescribed singularity where `f` has a pole of order `n`, the
  curve `γ` is flat of order `n`. -/
  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n
  /-- If the basepoint `γ (min a b)` (`= γ (max a b)` for a closed curve) is a prescribed
  singularity where `f` has a pole of order `n`, then `γ` is flat of order `n` across the
  join. -/
  basepoint : γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
      FlatOfOrderBasepoint γ (min a b) (max a b) n

/-- Characterization of `ConditionAprime` by its three clauses, for rewriting the hypothesis into
the `finite_crossings ∧ interior ∧ basepoint` conjunction (and back via the anonymous constructor).
-/
theorem conditionAprime_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔
      (∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite) ∧
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n) ∧
        (γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
          FlatOfOrderBasepoint γ (min a b) (max a b) n) :=
  ⟨fun h => ⟨h.finite_crossings, h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Condition (A′) is invariant under swapping the endpoints: all its clauses are stated over
`min`/`max`. -/
theorem conditionAprime_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔ ConditionAprime γ b a f S := by
  rw [conditionAprime_iff, conditionAprime_iff, Set.uIcc_comm, min_comm a b, max_comm a b]

/-- **Sector compatibility** of `f` at an on-curve singularity `z₀` whose sector opens at angle `θ`
(the Hungerbühler–Wasem condition at one crossing): the angle is a rational multiple of `π` and the
finite Laurent principal part of `f` at `z₀` resonates with `θ` under the sector-cancellation
identity `k · θ ∈ 2π · ℤ`. -/
structure SectorCompatible (f : ℂ → ℂ) (z₀ : ℂ) (θ : ℝ) : Prop where
  /-- The opening angle `θ` is a rational multiple `p·π/q` of `π` (`q ≠ 0`, `p`, `q` coprime). -/
  angle_rational : ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)
  /-- Near `z₀`, `f` is an analytic remainder plus a finite Laurent principal part whose surviving
  higher-order coefficients (`coeff k ≠ 0`, `k ≥ 1`) resonate with `θ` as `k · θ ∈ 2π · ℤ`. -/
  laurent_compatible : ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
    (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
      ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val → ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi)

/-- Characterization of `SectorCompatible` by its two fields, for rewriting the hypothesis into the
`angle_rational ∧ laurent_compatible` conjunction (and back via the anonymous constructor). -/
theorem sectorCompatible_iff {f : ℂ → ℂ} {z₀ : ℂ} {θ : ℝ} :
    SectorCompatible f z₀ θ ↔
      (∃ p q : ℕ,
        q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)) ∧
      ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
        (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
        ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val →
          ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi) :=
  ⟨fun h => ⟨h.angle_rational, h.laurent_compatible⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Hungerbühler–Wasem condition (B)** for `f` along `γ` on `[a, b]`: at each higher-order
on-curve pole of `f` the crossing sector is `SectorCompatible`. Together with condition (A′)
it is a hypothesis of the generalized residue theorem (HW Thm 3.3), where it forces the
order-`> 1` principal parts to cancel, so that the `PV ∮_γ f` the theorem evaluates is
well-defined. Imposed at each *interior* crossing `t₀` strictly between the endpoints and at
the *basepoint* `γ (min a b)` (via `basepointAngle`), so a join singularity is not left free;
stated over `min`/`max`, the condition is invariant under swapping the endpoints
(`conditionB_comm`). Higher-order poles are found intrinsically via
`meromorphicOrderAt f (γ t₀) < -1`; simple poles need no sector
condition, so the predicate is `S`-free. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where
  /-- At each interior higher-order (order `> 1`) on-curve pole of `f`, the crossing sector at
  `γ t₀` is compatible. -/
  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
    SectorCompatible f (γ t₀) (crossingAngle γ t₀)
  /-- If the basepoint `γ (min a b)` (`= γ (max a b)` for a closed curve) is a higher-order
  on-curve pole of `f`, its join sector is compatible — the endpoint case the `interior` clause
  cannot reach. -/
  basepoint : meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
    SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))

/-- Characterization of `ConditionB` by its two clauses, for rewriting the hypothesis into the
`interior ∧ basepoint` conjunction (and back via the anonymous constructor). -/
theorem conditionB_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
          SectorCompatible f (γ t₀) (crossingAngle γ t₀)) ∧
        (meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
          SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))) :=
  ⟨fun h => ⟨h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Condition (B) is invariant under swapping the endpoints: both its clauses are stated over
`min`/`max`. -/
theorem conditionB_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔ ConditionB γ b a f := by
  rw [conditionB_iff, conditionB_iff, min_comm a b, max_comm a b]

/-! ### Consuming the conditions

The two bridges from the conditions' data to the raw hypotheses the principal-value theorems
take: flatness restricts downward in the order, and the sector resonance `k · θ ∈ 2π · ℤ` at
the crossing angle is the power equation of the unit tangent directions. -/

/-- One-sided core of the downward restrictions: near `c` the chord is small, so on any
filter within `𝓝 c` an `o(‖γ · - γ c‖ ^ n)` bound is an `o(‖γ · - γ c‖ ^ m)` bound for
`m ≤ n`. -/
private theorem isLittleO_chord_pow_of_le {γ : ℝ → ℂ} {c : ℝ} {u : ℝ → ℝ} {m n : ℕ}
    {l : Filter ℝ} (hmn : m ≤ n) (h_le : l ≤ 𝓝 c) (h_cont : ContinuousAt γ c)
    (h : u =o[l] fun t => ‖γ t - γ c‖ ^ n) : u =o[l] fun t => ‖γ t - γ c‖ ^ m := by
  refine h.trans_isBigO (Asymptotics.IsBigO.of_bound 1 ?_)
  have h_ev : ∀ᶠ t in 𝓝 c, ‖γ t - γ c‖ ≤ 1 := by
    have h1 : Filter.Tendsto (fun t => γ t - γ c) (𝓝 c) (𝓝 (γ c - γ c)) :=
      (h_cont.sub continuousAt_const).tendsto
    rw [sub_self] at h1
    have h0 : Filter.Tendsto (fun t => ‖γ t - γ c‖) (𝓝 c) (𝓝 0) := by
      simpa using h1.norm
    exact h0.eventually_le_const one_pos
  filter_upwards [h_le h_ev] with t ht
  rw [one_mul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _),
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_of_le_one (norm_nonneg _) ht hmn

/-- **Flatness restricts downward**: a curve flat of order `n` at `t₀` is flat of every order
`m ≤ n` — near the crossing the chord is small, so a higher power of it is the stronger
bound. -/
theorem FlatOfOrder.of_le {γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ} (h : FlatOfOrder γ t₀ n)
    (hmn : m ≤ n) (h_cont : ContinuousAt γ t₀) : FlatOfOrder γ t₀ m := by
  obtain ⟨v_p, v_m, hv_p, hv_m, h_right, h_left⟩ := h
  exact ⟨v_p, v_m, hv_p, hv_m,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont h_right,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont h_left⟩

/-- **Basepoint flatness restricts downward**: a closed curve flat of order `n` across the
join is flat of every order `m ≤ n` there. -/
theorem FlatOfOrderBasepoint.of_le {γ : ℝ → ℂ} {a b : ℝ} {m n : ℕ}
    (h : FlatOfOrderBasepoint γ a b n) (hmn : m ≤ n)
    (h_cont_a : ContinuousAt γ a) (h_cont_b : ContinuousAt γ b) :
    FlatOfOrderBasepoint γ a b m := by
  obtain ⟨v_p, v_m, hv_p, hv_m, h_right, h_left⟩ := h
  exact ⟨v_p, v_m, hv_p, hv_m,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont_a h_right,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont_b h_left⟩

/-- The `[0, 2π)` representative differs from its argument by an integer multiple of `2π`. -/
private theorem toIcoMod_two_pi_sub_witness (θ : ℝ) :
    ∃ j : ℤ, toIcoMod Real.two_pi_pos 0 θ = θ - (j : ℝ) * (2 * Real.pi) := by
  refine ⟨toIcoDiv Real.two_pi_pos 0 θ, ?_⟩
  have h_sub := self_sub_toIcoMod Real.two_pi_pos 0 θ
  rw [zsmul_eq_mul] at h_sub
  linarith

/-- Angle core of the resonance bridges: if `θ` is the angle from `L_R` to `-L_L` up to
`2πℤ` and `k · θ ∈ 2π · ℤ`, the `k`-th powers of the unit directions agree. -/
private theorem pow_unit_eq_of_angle_resonance {L_R L_L : ℂ} {θ : ℝ} {k : ℕ}
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (hθ : ∃ j : ℤ, θ = (Complex.arg (-L_L) - Complex.arg L_R) - (j : ℝ) * (2 * Real.pi))
    (h_res : ∃ m : ℤ, (k : ℝ) * θ = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := hθ
  obtain ⟨m, hm⟩ := h_res
  rw [hj] at hm
  have h_real : (k : ℝ) * Complex.arg L_R
      = (k : ℝ) * Complex.arg (-L_L) + (-((m : ℝ) + (k : ℝ) * (j : ℝ))) * (2 * Real.pi) := by
    linear_combination -hm
  have hnorm : (‖L_L‖ : ℂ) = (‖-L_L‖ : ℂ) := by rw [norm_neg]
  rw [div_norm_eq_exp_arg_mul_I hL_R, hnorm,
    div_norm_eq_exp_arg_mul_I (neg_ne_zero.mpr hL_L), ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(m + (k : ℤ) * j), ?_⟩
  have hC := congrArg (fun x : ℝ => (x : ℂ) * Complex.I) h_real
  push_cast at hC ⊢
  linear_combination hC

/-- **Resonance to tangent powers**: if `k · crossingAngle γ t₀` is a multiple of `2π` and the
one-sided derivative limits at `t₀` are `L_R` and `L_L`, both non-zero, then the `k`-th powers
of the unit tangent directions agree — the raw sector equation the higher-order
principal-value theorems consume. -/
theorem pow_unit_tangent_eq_of_resonance {γ : ℝ → ℂ} {t₀ : ℝ} {L_R L_L : ℂ} {k : ℕ}
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_res : ∃ m : ℤ, (k : ℝ) * crossingAngle γ t₀ = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := toIcoMod_two_pi_sub_witness (Complex.arg (-L_L) - Complex.arg L_R)
  refine pow_unit_eq_of_angle_resonance hL_R hL_L ⟨j, ?_⟩ h_res
  rw [crossingAngle_eq_of_tendsto h_R h_L]
  exact hj

/-- **Basepoint resonance to tangent powers**: the join analogue of
`pow_unit_tangent_eq_of_resonance`, with the outgoing tangent limit at `a` and the incoming
tangent limit at `b` — the raw sector equation at the basepoint of a closed curve. -/
theorem pow_unit_tangent_eq_of_basepoint_resonance {γ : ℝ → ℂ} {a b : ℝ} {L_R L_L : ℂ}
    {k : ℕ} (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] a) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] b) (𝓝 L_L))
    (h_res : ∃ m : ℤ, (k : ℝ) * basepointAngle γ a b = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := toIcoMod_two_pi_sub_witness (Complex.arg (-L_L) - Complex.arg L_R)
  refine pow_unit_eq_of_angle_resonance hL_R hL_L ⟨j, ?_⟩ h_res
  rw [basepointAngle_eq_of_tendsto h_R h_L]
  exact hj

end TauCeti.Contour
