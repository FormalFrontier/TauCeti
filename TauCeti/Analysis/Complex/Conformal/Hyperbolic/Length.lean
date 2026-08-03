/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.ClosedForm
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.AutomorphismIsometry
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Poincaré metric is the length metric of its density

`Hyperbolic/Distance.lean` defines the hyperbolic distance on the complex open unit disc by the
closed formula `hyperbolicDist z w = Real.artanh (pseudoHyperbolicExpr z w)`, and
`Hyperbolic/Density.lean` shows that its infinitesimal density is `(1 - ‖z‖ ^ 2)⁻¹` and that the
distance from the origin along a *radius* is the integral of that density along the radius. The
latter file records, in so many words, what was still missing: "the density-weighted length of a
general curve is not defined here, so this does not identify `hyperbolicDist` with the length
metric of the density between arbitrary points". This file supplies the definition and the
identification.

The definition is the obvious one: for a path `γ : ℝ → ℂ` in the disc,

`TauCeti.hyperbolicLength γ a b = ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)`,

the Euclidean speed integrated against the Poincaré density over the *unordered* parameter
interval, as for Mathlib's `Manifold.pathELength`: the length of a path does not depend on the
orientation of its parameter interval, and is nonnegative. The theorem is that
`hyperbolicDist z w` is the **least** such length over `C¹` paths from `z` to `w`
(`TauCeti.isLeast_hyperbolicLength`): no path is shorter
(`TauCeti.hyperbolicDist_le_hyperbolicLength`), and one path realises the value
(`TauCeti.exists_hyperbolicLength_eq_hyperbolicDist`). Regularity is always asked of the path
*relative to its parameter interval*: continuity on the closed interval, an ordinary derivative
at its interior points, and a derivative that extends continuously to the closed interval.

## The proof

Both halves rest on one algebraic fact, which `Conformal/SchwarzPick/AutomorphismIsometry.lean`
already supplies as the equality case of the infinitesimal Schwarz--Pick lemma
(`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one`): the disc
Moebius factor `M z = (z - c) / (1 - conj c * z)` preserves the Poincaré density,

`‖M ′ z‖ / (1 - ‖M z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2)`.

Integrating it along a path gives `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`:
hyperbolic length is unchanged by post-composition with a disc Moebius factor. That is what moves
an arbitrary path to one starting at the origin.

*The lower bound.* For a path with `γ a = 0` the estimate is a one-variable calculus argument.
Choosing a unit vector `v` with `v * γ b = ‖γ b‖` — one exists for every `γ b`, including
`γ b = 0`, by Mathlib's `Complex.exists_norm_eq_mul_self` — the real function `ψ t = (v * γ t).re`
runs from `0` to `‖γ b‖` and satisfies `|ψ| ≤ ‖γ‖` and `|ψ ′| ≤ ‖γ ′‖`. Hence, pointwise,

`(Real.artanh ∘ ψ) ′ = ψ ′ / (1 - ψ ^ 2) ≤ ‖γ ′‖ / (1 - ‖γ‖ ^ 2)`,

the first inequality being `1 - ‖γ‖ ^ 2 ≤ 1 - ψ ^ 2` in the denominator. So Mathlib's
displacement bound `norm_sub_le_integral_of_norm_deriv_le_of_le` applies to `Real.artanh ∘ ψ`,
whose displacement is `Real.artanh ‖γ b‖ = hyperbolicDist (γ a) (γ b)`. Projecting on a *linear*
functional rather than on the norm is what keeps the comparison function differentiable where the
path crosses the origin.

*The bound is attained.* By the same invariance it suffices to exhibit a shortest path from the
origin, and the Euclidean radius `t ↦ u * t` is one: its hyperbolic length over `[0, r]` is
`∫ t in (0)..r, (1 - t ^ 2)⁻¹ = Real.artanh r` (`TauCeti.hyperbolicLength_ray`), which is
`Real.integral_one_sub_sq_inv_eq_artanh`, the same input the radial statement of
`Hyperbolic/Density.lean` spends. Transporting the radius by the Moebius factor centred at `-z`
joins `z` to `w` with length `hyperbolicDist z w`. The minimisers exhibited here are therefore
the radii through the origin and their Moebius images, the hyperbolic geodesics classified in
`Conformal/Poincare/Betweenness.lean`; the converse — that a path of least length is a
reparametrisation of one of them — is an equality case that this file does not prove.

## Schwarz--Pick: hyperbolic length is contracted, and conformally invariant

The Moebius invariance above is the equality case of a one-sided estimate, and the estimate holds
for *every* holomorphic self-map of the disc, not only for the automorphisms. Integrating the
infinitesimal Schwarz--Pick inequality
`TauCeti.norm_deriv_div_one_sub_norm_sq_le` of `Conformal/SchwarzPick/Derivative.lean` along a
path, exactly as the Moebius statement integrates its equality case, gives
`TauCeti.hyperbolicLength_comp_le`: post-composing a path with a holomorphic self-map of the disc
does not increase its hyperbolic length. The comparison is termwise, because the chain rule turns
the density-weighted speed of `f ∘ γ` into

`‖deriv f (γ t)‖ / (1 - ‖f (γ t)‖ ^ 2) * ‖γ' t‖`,

the first factor of which Schwarz--Pick bounds by `(1 - ‖γ t‖ ^ 2)⁻¹`; both integrands are
continuous, since the derivative of a holomorphic function is again holomorphic, so the estimate
integrates.

Applying the estimate to a biholomorphism and to its inverse in turn pins the two lengths together
and makes hyperbolic length a **conformal invariant** of the disc
(`TauCeti.hyperbolicLength_comp_eq_of_leftInvOn`): no explicit automorphism formula enters, only
the existence of a holomorphic inverse. Read at the standard automorphism
`z ↦ u * (z - c) / (1 - conj c * z)` it recovers
`TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` with its rotation factor restored, the
rotation costing nothing because multiplying a path by a unit scalar changes neither its Euclidean
speed nor its distance from the origin (`TauCeti.hyperbolicLength_const_mul`). Reflection in the
real axis is invariant too (`TauCeti.hyperbolicLength_conj`), which the conformal statement cannot
see, conjugation being antiholomorphic; with it the invariance covers the whole isometry group of
the Poincaré disc as `Conformal/Poincare/Isometry/Classification.lean` exhibits it.

## Relation to Mathlib's `Manifold.pathELength`

Mathlib's `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean` defines `Manifold.pathELength`
and `Manifold.riemannianEDist`, the infimum of path lengths, for a charted space each of whose
tangent spaces carries an `ENorm`. Routing this file through it would first require equipping the
open unit disc with a manifold structure and its tangent spaces with the Poincaré `ENorm`, none of
which exists in this tree; and it would state the result in `ℝ≥0∞`, whereas `hyperbolicDist` and
the entire disc development are real-valued. `hyperbolicLength` is therefore the elementary
integral over the parameter interval rather than a `pathELength` specialisation. Should the
Poincaré disc later be given a Riemannian structure, `TauCeti.isLeast_hyperbolicLength` is
precisely the input needed to identify `hyperbolicDist` with `Manifold.riemannianEDist`, and this
file should be refactored onto that API at that point.

## Main declarations

* `TauCeti.hyperbolicLength` — the density-weighted length of a path in the disc, with
  `TauCeti.hyperbolicLength_eq_integral` rewriting it against an explicit derivative, and
  `TauCeti.hyperbolicLength_symm`, `TauCeti.hyperbolicLength_nonneg`,
  `TauCeti.hyperbolicLength_const`, `TauCeti.hyperbolicLength_add` the basic evaluations and
  operations.
* `TauCeti.hyperbolicLength_comp_of_deriv_nonneg` and
  `TauCeti.hyperbolicLength_comp_of_deriv_nonpos` — **hyperbolic length is a reparametrisation
  invariant**: precomposing a path with a differentiable monotone, respectively antitone, map of
  the parameter transports the parameter interval and leaves the length unchanged. For the affine
  reparametrisations `t ↦ s * t + d` this needs nothing of the path,
  `TauCeti.hyperbolicLength_comp_mul_add`.
* `TauCeti.hyperbolicLength_congr` — the hyperbolic length of a path depends only on its values
  along its own parameter interval.
* `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` — hyperbolic length is a Moebius
  invariant, the integrated form of the infinitesimal isometry
  `TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one`;
  `TauCeti.hyperbolicLength_const_mul` is the same statement for a rotation, and
  `TauCeti.hyperbolicLength_conj` for the reflection in the real axis.
* `TauCeti.hyperbolicLength_comp_le` — **Schwarz--Pick for the Poincaré length**: post-composing
  a path in the disc with a holomorphic self-map of the disc does not increase its hyperbolic
  length.
* `TauCeti.hyperbolicLength_comp_eq_of_leftInvOn` — **hyperbolic length is a conformal
  invariant**: a holomorphic self-map of the disc with a holomorphic left inverse preserves it.
* `TauCeti.hyperbolicLength_ray` — the hyperbolic length of a Euclidean radius is `Real.artanh`
  of its Euclidean length.
* `TauCeti.hyperbolicDist_le_hyperbolicLength` — **no `C¹` path in the disc is hyperbolically
  shorter than the hyperbolic distance between its endpoints.**
* `TauCeti.exists_hyperbolicLength_eq_hyperbolicDist` — the bound is attained.
* `TauCeti.isLeast_hyperbolicLength` — **the Poincaré metric is the length metric of its
  density**: `hyperbolicDist z w` is the least hyperbolic length of a `C¹` path from `z` to `w`.

## Coordination with upstream Mathlib

As with the rest of the L2 material of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), this file is coordinated with the in-progress
human-curated Riemann-mapping effort [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
which contains no hyperbolic metric on the disc; Mathlib has the hyperbolic metric on the upper
half-plane (`Analysis/Complex/UpperHalfPlane/Metric.lean`) but neither a disc version nor a
length-metric characterisation of it. Should a human-curated Poincaré metric land upstream, this
file should be refactored onto it.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1 (the Poincaré metric as a length metric).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {γ γ' : ℝ → ℂ} {a b : ℝ} {c z w : ℂ}

/-! ## The hyperbolic length of a path -/

/-- The **hyperbolic length** of the path `γ` over the parameter interval with endpoints `a` and
`b`: the Euclidean speed `‖deriv γ t‖` integrated over the unordered interval `uIcc a b` against
the Poincaré density `(1 - ‖γ t‖ ^ 2)⁻¹` of `Conformal/Hyperbolic/Density.lean`.

Taking the integral over the unordered interval, as Mathlib's `Manifold.pathELength` does, makes
the length independent of the orientation of the parameter interval
(`TauCeti.hyperbolicLength_symm`) and nonnegative for a path in the disc whichever way round its
endpoints are (`TauCeti.hyperbolicLength_nonneg`); it is a reparametrisation invariant of the path
(`TauCeti.hyperbolicLength_comp_of_deriv_nonneg` and `TauCeti.hyperbolicLength_comp_of_deriv_nonpos`
for the monotone and the antitone reparametrisations, `TauCeti.hyperbolicLength_comp_mul_add` for
the affine ones).

The definition is stated for an arbitrary `γ : ℝ → ℂ`, and only the derivative at the interior
parameters enters (`TauCeti.hyperbolicLength_eq_integral`). It is the intended notion of length
when `γ` is a `C¹` path with values in the open unit disc, which is what the comparison with
`TauCeti.hyperbolicDist` below assumes; the evaluations of the length itself need no such
hypothesis. -/
noncomputable def hyperbolicLength (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)

/-- The defining formula for the hyperbolic length of a path. -/
theorem hyperbolicLength_def (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ a b = ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2) := by
  rw [hyperbolicLength]

/-- A degenerate parameter interval carries no hyperbolic length. -/
@[simp]
theorem hyperbolicLength_self (γ : ℝ → ℂ) (a : ℝ) : hyperbolicLength γ a a = 0 := by
  rw [hyperbolicLength_def, uIcc_self]
  simp

/-- Hyperbolic length does not depend on the orientation of the parameter interval. -/
theorem hyperbolicLength_symm (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ b a = hyperbolicLength γ a b := by
  rw [hyperbolicLength_def, hyperbolicLength_def, uIcc_comm]

/-- A constant path has zero hyperbolic length. -/
@[simp]
theorem hyperbolicLength_const (c : ℂ) (a b : ℝ) :
    hyperbolicLength (fun _ => c) a b = 0 := by
  rw [hyperbolicLength_def]
  simp

/-- The hyperbolic length over an ordered parameter interval as an interval integral of any
function agreeing with the density-weighted speed at the interior parameters, the two endpoints
forming a null set. -/
private theorem hyperbolicLength_eq_intervalIntegral_of_eqOn {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : EqOn (fun t => ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)) f (Ioo a b)) :
    hyperbolicLength γ a b = ∫ t in a..b, f t := by
  rw [hyperbolicLength_def, uIcc_of_le hab,
    ← MeasureTheory.restrict_Ioo_eq_restrict_Icc,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hf,
    MeasureTheory.restrict_Ioo_eq_restrict_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The hyperbolic length computed from an explicit derivative rather than from `deriv`. The
derivative is only asked for at the interior parameters, the two endpoints forming a null set. -/
theorem hyperbolicLength_eq_integral (hab : a ≤ b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) :=
  hyperbolicLength_eq_intervalIntegral_of_eqOn hab fun t ht => by simp only [(hderiv t ht).deriv]

/-- A path running through the open unit disc has nonnegative hyperbolic length, whichever way
round its endpoints are. -/
theorem hyperbolicLength_nonneg (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    0 ≤ hyperbolicLength γ a b := by
  rw [hyperbolicLength_def]
  exact MeasureTheory.setIntegral_nonneg measurableSet_uIcc fun t ht =>
    div_nonneg (norm_nonneg _) (by nlinarith [norm_nonneg (γ t), hmem t ht])

/-- For a `C¹` path in the disc the density-weighted speed is interval integrable: it is
continuous, its denominator staying away from zero because the path stays in the open disc. -/
private theorem intervalIntegrable_norm_div_one_sub_norm_sq (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγ' : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine hγ'.norm.div (continuousOn_const.sub (hγ.norm.pow 2)) fun t ht => ?_
  have hpos : (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := by nlinarith [norm_nonneg (γ t), hmem t ht]
  exact hpos.ne'

/-- The hyperbolic length over an ordered parameter interval as an interval integral of the
density-weighted speed. -/
private theorem hyperbolicLength_eq_intervalIntegral (γ : ℝ → ℂ) (hab : a ≤ b) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2) :=
  hyperbolicLength_eq_intervalIntegral_of_eqOn hab fun _ _ => rfl

/-- The congruence over an ordered parameter interval; the general case follows by symmetry. -/
private theorem hyperbolicLength_congr_of_le {δ : ℝ → ℂ} (hab : a ≤ b)
    (hδ : EqOn δ γ (Icc a b)) : hyperbolicLength δ a b = hyperbolicLength γ a b := by
  rw [hyperbolicLength_eq_intervalIntegral γ hab]
  refine hyperbolicLength_eq_intervalIntegral_of_eqOn hab fun t ht => ?_
  have hnhds : δ =ᶠ[nhds t] γ :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (hδ.mono Ioo_subset_Icc_self)
  simp only [hnhds.deriv_eq, hδ (Ioo_subset_Icc_self ht)]

/-- **The hyperbolic length of a path depends only on its parameter interval.** Two paths that
agree on the interval with endpoints `a` and `b` have the same hyperbolic length over it: at an
interior parameter they have the same germ, hence the same derivative, and the two endpoints form
a null set. -/
theorem hyperbolicLength_congr {δ : ℝ → ℂ} (hδ : EqOn δ γ (uIcc a b)) :
    hyperbolicLength δ a b = hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hδ
    exact hyperbolicLength_congr_of_le hab hδ
  · rw [uIcc_comm, uIcc_of_le hab] at hδ
    rw [hyperbolicLength_symm δ b a, hyperbolicLength_symm γ b a]
    exact hyperbolicLength_congr_of_le hab hδ

/-- **Hyperbolic length is additive along the parameter interval**: the lengths of the two halves
of a path add up to the length of the whole, as soon as the density-weighted speed is integrable
over the whole. For a `C¹` path in the disc that hypothesis holds by continuity. -/
theorem hyperbolicLength_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hint : IntervalIntegrable (fun t => ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2))
      MeasureTheory.volume a c) :
    hyperbolicLength γ a b + hyperbolicLength γ b c = hyperbolicLength γ a c := by
  have hac : a ≤ c := hab.trans hbc
  rw [hyperbolicLength_eq_intervalIntegral γ hab, hyperbolicLength_eq_intervalIntegral γ hbc,
    hyperbolicLength_eq_intervalIntegral γ hac]
  refine intervalIntegral.integral_add_adjacent_intervals (hint.mono_set ?_) (hint.mono_set ?_)
  · rw [uIcc_of_le hab, uIcc_of_le hac]
    exact Icc_subset_Icc le_rfl hbc
  · rw [uIcc_of_le hbc, uIcc_of_le hac]
    exact Icc_subset_Icc hab le_rfl

/-- The affine reparametrisation invariance over an ordered parameter interval; the general case
follows by symmetry. -/
private theorem hyperbolicLength_comp_mul_add_of_le (γ : ℝ → ℂ) {s : ℝ} (hs : s ≠ 0) (d : ℝ)
    (hab : a ≤ b) :
    hyperbolicLength (fun t => γ (s * t + d)) a b
      = hyperbolicLength γ (s * a + d) (s * b + d) := by
  have hderiv : ∀ t : ℝ, deriv (fun u : ℝ => γ (s * u + d)) t = s • deriv γ (s * t + d) := by
    intro t
    have h := deriv_comp_mul_left s (fun u : ℝ => γ (u + d)) t
    rw [deriv_comp_add_const] at h
    simpa using h
  have hLHS : hyperbolicLength (fun t => γ (s * t + d)) a b
      = |s| * ∫ t in a..b, ‖deriv γ (s * t + d)‖ / (1 - ‖γ (s * t + d)‖ ^ 2) := by
    rw [hyperbolicLength_eq_intervalIntegral _ hab, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hderiv t, norm_smul, Real.norm_eq_abs, mul_div_assoc]
  rw [hLHS, intervalIntegral.integral_comp_mul_add
    (fun u => ‖deriv γ u‖ / (1 - ‖γ u‖ ^ 2)) hs d, smul_eq_mul]
  rcases hs.lt_or_gt with hneg | hpos
  · have hle : s * b + d ≤ s * a + d := by nlinarith
    rw [hyperbolicLength_symm, hyperbolicLength_eq_intervalIntegral _ hle,
      intervalIntegral.integral_symm (s * a + d) (s * b + d), abs_of_neg hneg]
    field_simp
  · have hle : s * a + d ≤ s * b + d := by nlinarith
    rw [hyperbolicLength_eq_intervalIntegral _ hle, abs_of_pos hpos]
    field_simp

/-- **Hyperbolic length is invariant under affine reparametrisation.** Replacing the parameter `t`
by `s * t + d` for `s ≠ 0`, an orientation-preserving reparametrisation for `0 < s` and an
orientation-reversing one for `s < 0`, transports the parameter interval and leaves the length
unchanged: two affinely reparametrised copies of one path have the same hyperbolic length. For
instance `s = r`, `d = 0` reads the path of
`TauCeti.exists_hyperbolicLength_eq_hyperbolicDist`, defined on `[0, r]`, on the parameter
interval `[0, 1]` without changing its length. Being a change of variables in the parameter alone,
it asks nothing of the path, unlike the reparametrisations by a general monotone or antitone map
below (`TauCeti.hyperbolicLength_comp_of_deriv_nonneg`,
`TauCeti.hyperbolicLength_comp_of_deriv_nonpos`), which need the path to be differentiable to
differentiate the composite. -/
theorem hyperbolicLength_comp_mul_add (γ : ℝ → ℂ) {s : ℝ} (hs : s ≠ 0) (d a b : ℝ) :
    hyperbolicLength (fun t => γ (s * t + d)) a b
      = hyperbolicLength γ (s * a + d) (s * b + d) := by
  rcases le_total a b with hab | hab
  · exact hyperbolicLength_comp_mul_add_of_le γ hs d hab
  · rw [hyperbolicLength_symm (fun t => γ (s * t + d)) b a,
      hyperbolicLength_symm γ (s * b + d) (s * a + d)]
    exact hyperbolicLength_comp_mul_add_of_le γ hs d hab

/-- The monotone reparametrisation invariance over an ordered parameter interval; the general case
follows by symmetry. -/
private theorem hyperbolicLength_comp_of_deriv_nonneg_of_le {φ φ' : ℝ → ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hsign : ∀ t ∈ Ioo a b, 0 ≤ φ' t) (hγ : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) := by
  have hIoo : Ioo (min a b) (max a b) = Ioo a b := by rw [min_eq_left hab, max_eq_right hab]
  -- inside the parameter interval the density-weighted speed of `γ ∘ φ` is `φ'` times that of
  -- `γ` read at `φ`, written as a composition to meet the change of variables below
  have hEq : EqOn (fun t => ‖deriv (γ ∘ φ) t‖ / (1 - ‖(γ ∘ φ) t‖ ^ 2))
      (fun t => φ' t • ((fun u => ‖deriv γ u‖ / (1 - ‖γ u‖ ^ 2)) ∘ φ) t) (Ioo a b) := by
    intro t ht
    have hchain : deriv (γ ∘ φ) t = φ' t • deriv γ (φ t) :=
      ((hγ t ht).hasDerivAt.scomp t (hderiv t ht)).deriv
    simp only [Function.comp_apply, hchain, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hsign t ht), smul_eq_mul]
    ring
  have hmono : MonotoneOn φ (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hφ (fun t ht => ?_) fun t ht => ?_
    · rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      exact hsign t ht
  have hφab : φ a ≤ φ b := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [hyperbolicLength_eq_intervalIntegral_of_eqOn hab hEq,
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (by rwa [uIcc_of_le hab])
      (by rwa [hIoo]) (by rwa [hIoo]),
    ← hyperbolicLength_eq_intervalIntegral γ hφab]

/-- **Hyperbolic length is invariant under monotone reparametrisation.** Precomposing a path with
a map `φ` that is continuous on the parameter interval and has a nonnegative derivative inside it —
so that `φ` is monotone there — reparametrises the path and transports the parameter interval,
leaving the length unchanged. The path is asked to be differentiable at the reparametrised
parameters, which is what makes the composite differentiable; no regularity beyond that is needed,
because Mathlib's change of variables for a monotone substitution
(`intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`) asks nothing of the integrand. -/
theorem hyperbolicLength_comp_of_deriv_nonneg {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, 0 ≤ φ' t)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hφ
    rw [uIoo_of_le hab] at hderiv hsign hγ
    exact hyperbolicLength_comp_of_deriv_nonneg_of_le hab hφ hderiv hsign hγ
  · rw [uIcc_comm, uIcc_of_le hab] at hφ
    rw [uIoo_comm, uIoo_of_le hab] at hderiv hsign hγ
    rw [hyperbolicLength_symm (γ ∘ φ) b a, hyperbolicLength_symm γ (φ b) (φ a)]
    exact hyperbolicLength_comp_of_deriv_nonneg_of_le hab hφ hderiv hsign hγ

/-- The antitone reparametrisation invariance over an ordered parameter interval; the general case
follows by symmetry. -/
private theorem hyperbolicLength_comp_of_deriv_nonpos_of_le {φ φ' : ℝ → ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hsign : ∀ t ∈ Ioo a b, φ' t ≤ 0) (hγ : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) := by
  have hIoo : Ioo (min a b) (max a b) = Ioo a b := by rw [min_eq_left hab, max_eq_right hab]
  -- as in the monotone case, save that `φ'` is now nonpositive, so that the speed of `γ ∘ φ`
  -- is *minus* `φ'` times the speed of `γ` read at `φ`
  have hEq : EqOn (fun t => ‖deriv (γ ∘ φ) t‖ / (1 - ‖(γ ∘ φ) t‖ ^ 2))
      (fun t => -(φ' t • ((fun u => ‖deriv γ u‖ / (1 - ‖γ u‖ ^ 2)) ∘ φ) t)) (Ioo a b) := by
    intro t ht
    have hchain : deriv (γ ∘ φ) t = φ' t • deriv γ (φ t) :=
      ((hγ t ht).hasDerivAt.scomp t (hderiv t ht)).deriv
    simp only [Function.comp_apply, hchain, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (hsign t ht), smul_eq_mul]
    ring
  have hanti : AntitoneOn φ (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hφ (fun t ht => ?_) fun t ht => ?_
    · rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      exact hsign t ht
  have hφab : φ b ≤ φ a := hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [hyperbolicLength_eq_intervalIntegral_of_eqOn hab hEq, intervalIntegral.integral_neg,
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (by rwa [uIcc_of_le hab])
      (by rwa [hIoo]) (by rwa [hIoo]),
    ← intervalIntegral.integral_symm, hyperbolicLength_symm γ (φ b) (φ a),
    ← hyperbolicLength_eq_intervalIntegral γ hφab]

/-- **Hyperbolic length is invariant under antitone reparametrisation.** The orientation-reversing
counterpart of `TauCeti.hyperbolicLength_comp_of_deriv_nonneg`: precomposing a path with a map `φ`
that is continuous on the parameter interval and has a nonpositive derivative inside it — so that
`φ` is antitone there — leaves the length unchanged, the parameter interval being transported with
its orientation reversed. Together the two lemmas say that hyperbolic length is a property of a
path rather than of its parametrisation. -/
theorem hyperbolicLength_comp_of_deriv_nonpos {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, φ' t ≤ 0)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hφ
    rw [uIoo_of_le hab] at hderiv hsign hγ
    exact hyperbolicLength_comp_of_deriv_nonpos_of_le hab hφ hderiv hsign hγ
  · rw [uIcc_comm, uIcc_of_le hab] at hφ
    rw [uIoo_comm, uIoo_of_le hab] at hderiv hsign hγ
    rw [hyperbolicLength_symm (γ ∘ φ) b a, hyperbolicLength_symm γ (φ b) (φ a)]
    exact hyperbolicLength_comp_of_deriv_nonpos_of_le hab hφ hderiv hsign hγ

/-- **The hyperbolic length of a Euclidean radius.** For a unit vector `u` and `0 ≤ r < 1`, the
path `t ↦ u * t` has hyperbolic length `Real.artanh r` over `[0, r]`, which by
`TauCeti.hyperbolicDist_zero_right` is the hyperbolic distance from `0` to its endpoint. This is
the radial computation of `Conformal/Hyperbolic/Density.lean` read as a statement about lengths. -/
theorem hyperbolicLength_ray {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    hyperbolicLength (fun t : ℝ => u * (t : ℂ)) 0 r = Real.artanh r := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u * (s : ℂ)) u t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul u
  rw [hyperbolicLength_eq_integral (γ' := fun _ => u) hr fun t _ => hderiv t,
    ← Real.integral_one_sub_sq_inv_eq_artanh ⟨by linarith, hr1⟩]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hr] at ht
  have hnorm : ‖u * (t : ℂ)‖ = t := by
    rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [hnorm, hu, one_div]

/-! ## Conformal invariance of the density -/

/-- **Hyperbolic length is a rotation invariant.** Multiplying a path by a scalar of modulus one
scales neither its Euclidean speed nor its distance from the origin, so it changes no term of the
density-weighted integrand. Unlike the Moebius invariance below, this asks nothing of the path:
where the path fails to be differentiable so does its rotation, and both sides read the same
junk value of `deriv`. -/
@[simp]
theorem hyperbolicLength_const_mul {u : ℂ} (hu : ‖u‖ = 1) :
    hyperbolicLength (fun t => u * γ t) a b = hyperbolicLength γ a b := by
  rw [hyperbolicLength_def, hyperbolicLength_def]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_uIcc fun t _ => ?_
  simp only [deriv_const_mul_field, norm_mul, hu, one_mul]

/-- **Hyperbolic length is a conjugation invariant.** Reflecting a path in the real axis leaves its
hyperbolic length unchanged. As for the rotation invariance this asks nothing of the path:
conjugation is a real-linear isometry, so it changes neither term of the density-weighted
integrand, and at a parameter where the path fails to be differentiable both sides read the same
junk value of `deriv` (`deriv.star`). Conjugation is antiholomorphic, so this is not an instance of
the conformal invariance `TauCeti.hyperbolicLength_comp_eq_of_leftInvOn` below; together the two
cover the whole isometry group of the Poincaré disc, which
`Conformal/Poincare/Isometry/Classification.lean` exhibits as the standard automorphisms and their
conjugates. -/
@[simp]
theorem hyperbolicLength_conj (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength (fun t => (starRingEnd ℂ) (γ t)) a b = hyperbolicLength γ a b := by
  rw [hyperbolicLength_def, hyperbolicLength_def]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_uIcc fun t _ => ?_
  simp only [← Complex.star_def, deriv.star, norm_star]

/-- The Moebius invariance of hyperbolic length over an ordered parameter interval; the general
case follows by symmetry. -/
private theorem hyperbolicLength_unitDiscMoebiusFormula_comp_of_le (hc : ‖c‖ < 1) (hab : a ≤ b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  have key : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => (γ s - c) / (1 - (starRingEnd ℂ) c * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2)) t := by
    intro t ht
    have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t (Ioo_subset_Icc_self ht)) hc
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).scomp t (hderiv t ht)
  rw [hyperbolicLength_eq_integral hab key, hyperbolicLength_eq_integral hab hderiv]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  rw [norm_mul, mul_div_assoc, ← (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).deriv,
    norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one hc (hmem t ht),
    mul_one_div]

/-- **Hyperbolic length is a Moebius invariant.** Post-composing a path in the disc with the
Moebius factor `z ↦ (z - c) / (1 - conj c * z)` leaves its hyperbolic length unchanged: this is
the infinitesimal Poincaré isometry
`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one` integrated along
the path. It is the tool that moves the starting point of a path to the origin. -/
theorem hyperbolicLength_unitDiscMoebiusFormula_comp (hc : ‖c‖ < 1)
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIoo_of_le hab] at hderiv
    rw [uIcc_of_le hab] at hmem
    exact hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem
  · rw [uIoo_comm, uIoo_of_le hab] at hderiv
    rw [uIcc_comm, uIcc_of_le hab] at hmem
    rw [hyperbolicLength_symm _ b a, hyperbolicLength_symm γ b a]
    exact hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem

/-! ## Schwarz--Pick: holomorphic self-maps of the disc contract hyperbolic length -/

/-- The chain rule for a path in the disc post-composed with a function holomorphic on the disc:
at a parameter where the path is differentiable and stays in the open disc, `f ∘ γ` has derivative
`γ' t * deriv f (γ t)`. -/
private theorem hasDerivAt_comp_of_norm_lt_one {f : ℂ → ℂ} {t : ℝ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hmem : ‖γ t‖ < 1)
    (hderiv : HasDerivAt γ (γ' t) t) :
    HasDerivAt (f ∘ γ) (γ' t * deriv f (γ t)) t := by
  have hf' : HasDerivAt f (deriv f (γ t)) (γ t) :=
    (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hmem))).hasDerivAt
  simpa [smul_eq_mul] using hf'.scomp t hderiv

/-- The Schwarz--Pick length estimate over an ordered parameter interval; the general case follows
by symmetry. -/
private theorem hyperbolicLength_comp_le_of_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc a b)) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicLength (f ∘ γ) a b ≤ hyperbolicLength γ a b := by
  have hball : MapsTo γ (Icc a b) (ball (0 : ℂ) 1) := fun t ht => mem_ball_zero_iff.mpr (hmem t ht)
  have hcomp : ∀ t ∈ Ioo a b, HasDerivAt (f ∘ γ) (γ' t * deriv f (γ t)) t := fun t ht =>
    hasDerivAt_comp_of_norm_lt_one hf (hmem t (Ioo_subset_Icc_self ht)) (hderiv t ht)
  have hfmem : ∀ t ∈ Icc a b, ‖(f ∘ γ) t‖ < 1 := fun t ht => mem_ball_zero_iff.mp (hmaps (hball ht))
  -- the derivative of a holomorphic function is again holomorphic, hence continuous on the disc
  have hdf : ContinuousOn (fun t => deriv f (γ t)) (Icc a b) :=
    ((hf.analyticOnNhd isOpen_ball).deriv.continuousOn).comp hγ hball
  rw [hyperbolicLength_eq_integral hab hcomp, hyperbolicLength_eq_integral hab hderiv]
  refine intervalIntegral.integral_mono_on hab
    (intervalIntegrable_norm_div_one_sub_norm_sq hab (hf.continuousOn.comp hγ hball)
      (hγ'.mul hdf) hfmem)
    (intervalIntegrable_norm_div_one_sub_norm_sq hab hγ hγ' hmem) fun t ht => ?_
  calc ‖γ' t * deriv f (γ t)‖ / (1 - ‖(f ∘ γ) t‖ ^ 2)
      = ‖γ' t‖ * (‖deriv f (γ t)‖ / (1 - ‖f (γ t)‖ ^ 2)) := by
        simp only [Function.comp_apply, norm_mul, mul_div_assoc]
    _ ≤ ‖γ' t‖ * (1 / (1 - ‖γ t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (norm_deriv_div_one_sub_norm_sq_le hf hmaps (hball ht)) (norm_nonneg _)
    _ = ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := mul_one_div _ _

/-- **Schwarz--Pick for the Poincaré length.** Post-composing a path in the open unit disc with a
holomorphic self-map of the disc does not increase its hyperbolic length. This is the infinitesimal
Schwarz--Pick inequality `TauCeti.norm_deriv_div_one_sub_norm_sq_le` integrated along the path, in
the same way as `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` integrates its equality
case; the path is asked to be `C¹` on its parameter interval, as in
`TauCeti.hyperbolicDist_le_hyperbolicLength`, so that both density-weighted speeds are
integrable. -/
theorem hyperbolicLength_comp_le {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (f ∘ γ) a b ≤ hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_of_le hab] at hderiv
    exact hyperbolicLength_comp_le_of_le hf hmaps hab hγ hderiv hγ' hmem
  · rw [uIcc_comm, uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_comm, uIoo_of_le hab] at hderiv
    rw [hyperbolicLength_symm (f ∘ γ) b a, hyperbolicLength_symm γ b a]
    exact hyperbolicLength_comp_le_of_le hf hmaps hab hγ hderiv hγ' hmem

/-- **Hyperbolic length is a conformal invariant of the disc.** A holomorphic self-map of the open
unit disc that has a holomorphic left inverse there preserves the hyperbolic length of every `C¹`
path in the disc: the Schwarz--Pick estimate `TauCeti.hyperbolicLength_comp_le` applied to the map
and to its inverse in turn traps the two lengths at each other. No explicit automorphism formula
enters, only the existence of the holomorphic inverse. -/
theorem hyperbolicLength_comp_eq_of_leftInvOn {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : LeftInvOn g f (ball (0 : ℂ) 1)) (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (f ∘ γ) a b = hyperbolicLength γ a b := by
  have hball : MapsTo γ (uIcc a b) (ball (0 : ℂ) 1) := fun t ht => mem_ball_zero_iff.mpr (hmem t ht)
  refine le_antisymm (hyperbolicLength_comp_le hf hfmaps hγ hderiv hγ' hmem) ?_
  have hcomp : ∀ t ∈ uIoo a b, HasDerivAt (f ∘ γ) (γ' t * deriv f (γ t)) t := fun t ht =>
    hasDerivAt_comp_of_norm_lt_one hf (hmem t (uIoo_subset_uIcc_self ht)) (hderiv t ht)
  have hfmem : ∀ t ∈ uIcc a b, ‖(f ∘ γ) t‖ < 1 := fun t ht =>
    mem_ball_zero_iff.mp (hfmaps (hball ht))
  have hdf : ContinuousOn (fun t => deriv f (γ t)) (uIcc a b) :=
    ((hf.analyticOnNhd isOpen_ball).deriv.continuousOn).comp hγ hball
  have key := hyperbolicLength_comp_le hg hgmaps (hf.continuousOn.comp hγ hball) hcomp
    (hγ'.mul hdf) hfmem
  rwa [hyperbolicLength_congr (δ := g ∘ (f ∘ γ)) fun t ht => hgf (hball ht)] at key

/-! ## The distance is a lower bound for the length -/

/-- The lower bound for a path issued from the origin, where the hyperbolic distance to the
endpoint is `Real.artanh` of its Euclidean norm. Comparing with the real function
`t ↦ (v * γ t).re` for a suitable unit vector `v` — rather than with `t ↦ ‖γ t‖`, which need not
be differentiable — turns the estimate into Mathlib's displacement bound
`norm_sub_le_integral_of_norm_deriv_le_of_le` applied to `Real.artanh ∘ ψ`. -/
private theorem artanh_norm_le_integral (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) (h0 : γ a = 0) :
    Real.artanh ‖γ b‖ ≤ ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
  have hpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := fun t ht => by
    nlinarith [norm_nonneg (γ t), hmem t ht]
  have hint2 : IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b :=
    intervalIntegrable_norm_div_one_sub_norm_sq hab hγ hγ' hmem
  obtain ⟨v, hvnorm, hvb⟩ := Complex.exists_norm_eq_mul_self (γ b)
  set ψ : ℝ → ℝ := fun t => (v * γ t).re with hψdef
  have hψa : ψ a = 0 := by simp [hψdef, h0]
  have hψb : ψ b = ‖γ b‖ := by simp only [hψdef, ← hvb, Complex.ofReal_re]
  have hψbound : ∀ t : ℝ, |ψ t| ≤ ‖γ t‖ := fun t =>
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul])
  have hψmem : ∀ t ∈ Icc a b, ψ t ∈ Ioo (-1 : ℝ) 1 := fun t ht =>
    abs_lt.mp ((hψbound t).trans_lt (hmem t ht))
  have hψderiv : ∀ t ∈ Ioo a b, HasDerivAt ψ ((v * γ' t).re) t := fun t ht => by
    simpa [hψdef, Function.comp_def] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hderiv t ht).const_mul v)
  have hψcont : ContinuousOn ψ (Icc a b) :=
    Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hγ)
  have hPpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ψ t ^ 2 := fun t ht => by
    have := hψmem t ht
    nlinarith [this.1, this.2]
  -- `Real.artanh ∘ ψ` runs from `0` to `Real.artanh ‖γ b‖` with speed at most the
  -- density-weighted speed of `γ`, so Mathlib's displacement bound applies to it.
  have hcont : ContinuousOn (fun t => Real.artanh (ψ t)) (Icc a b) :=
    Real.continuousOn_artanh.comp hψcont fun t ht => hψmem t ht
  have hdiff : DifferentiableOn ℝ (fun t => Real.artanh (ψ t)) (Ioo a b) := fun t ht =>
    ((hψderiv t ht).artanh
      (hψmem t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
  have hbound : ∀ᵐ t, t ∈ Ioo a b →
      ‖deriv (fun s => Real.artanh (ψ s)) t‖ ≤ ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) :=
    .of_forall fun t ht => by
      have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
      have hnum : |(v * γ' t).re| ≤ ‖γ' t‖ :=
        (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul])
      have hPQ : 1 - ‖γ t‖ ^ 2 ≤ 1 - ψ t ^ 2 := by
        nlinarith [hψbound t, abs_nonneg (ψ t), sq_abs (ψ t), norm_nonneg (γ t)]
      rw [((hψderiv t ht).artanh (hψmem t htI)).deriv, Real.norm_eq_abs, abs_mul, abs_inv,
        abs_of_pos (hPpos t htI), inv_mul_eq_div]
      gcongr
      exact hpos t htI
  have key := norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont hdiff hbound hint2
  simp only [hψa, hψb, Real.artanh_zero, sub_zero, Real.norm_eq_abs] at key
  exact (le_abs_self _).trans key

/-- The lower bound over an ordered parameter interval; the general case follows by symmetry. -/
private theorem hyperbolicDist_le_hyperbolicLength_of_le (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc a b)) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b := by
  have hc : ‖γ a‖ < 1 := hmem a ⟨le_rfl, hab⟩
  have hden : ∀ t ∈ Icc a b, (1 : ℂ) - (starRingEnd ℂ) (γ a) * γ t ≠ 0 := fun t ht =>
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  have hσderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => (γ s - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
          (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) t := fun t ht => by
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula (γ a) (γ t)
        (hden t (Ioo_subset_Icc_self ht))).scomp t (hderiv t ht)
  have hσcont : ContinuousOn (fun s => (γ s - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ s))
      (Icc a b) :=
    (hγ.sub continuousOn_const).div (continuousOn_const.sub (continuousOn_const.mul hγ)) hden
  have hσ'cont : ContinuousOn (fun t => γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
      (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) (Icc a b) :=
    hγ'.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul hγ)).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  have hσmem : ∀ t ∈ Icc a b,
      ‖(γ t - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ t)‖ < 1 := fun t ht => by
    rw [← pseudoHyperbolicExpr_def]
    exact pseudoHyperbolicExpr_lt_one_of_norm_lt_one (hmem t ht) hc
  have hσa : (γ a - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ a) = 0 := by
    rw [sub_self, zero_div]
  have key := artanh_norm_le_integral hab hσcont hσderiv hσ'cont hσmem hσa
  rw [← hyperbolicLength_eq_integral hab hσderiv,
    hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem] at key
  refine le_trans (le_of_eq ?_) key
  rw [hyperbolicDist_comm, hyperbolicDist_def, pseudoHyperbolicExpr_def]

/-- **No path in the disc is hyperbolically shorter than the hyperbolic distance between its
endpoints.** For a path `γ` staying in the open unit disc, continuous on its parameter interval
and continuously differentiable inside it,
`hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b`.

The starting point is moved to the origin by the Moebius factor centred at `γ a`, which changes
neither side: the left-hand side because the factor is a hyperbolic isometry, the right-hand side
by `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`. -/
theorem hyperbolicDist_le_hyperbolicLength (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_of_le hab] at hderiv
    exact hyperbolicDist_le_hyperbolicLength_of_le hab hγ hderiv hγ' hmem
  · rw [uIcc_comm, uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_comm, uIoo_of_le hab] at hderiv
    have key := hyperbolicDist_le_hyperbolicLength_of_le hab hγ hderiv hγ' hmem
    rwa [hyperbolicDist_comm, hyperbolicLength_symm] at key

/-! ## The bound is attained -/

/-- **The hyperbolic distance is realised by a path.** Any two points of the open unit disc are
joined by a `C¹` path in the disc whose hyperbolic length is exactly their hyperbolic distance,
namely the Moebius image of a Euclidean radius. -/
theorem exists_hyperbolicLength_eq_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ ContinuousOn γ (Icc 0 r) ∧
      (∀ t ∈ Ioo 0 r, HasDerivAt γ (γ' t) t) ∧ ContinuousOn γ' (Icc 0 r) ∧
      (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
      hyperbolicLength γ 0 r = hyperbolicDist z w := by
  have hp0 : 0 ≤ pseudoHyperbolicExpr w z := pseudoHyperbolicExpr_nonneg w z
  have hp1 : pseudoHyperbolicExpr w z < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hw hz
  set p : ℝ := pseudoHyperbolicExpr w z with hpdef
  set m : ℂ := (w - z) / (1 - (starRingEnd ℂ) z * w) with hmdef
  have hmnorm : ‖m‖ = p := by rw [hpdef, pseudoHyperbolicExpr_def, hmdef]
  -- A unit vector pointing along `m`. `Complex.norm_mul_exp_arg_mul_I` supplies one for *every*
  -- `m`, including `m = 0`, so the direction needs no case split on whether `p` vanishes.
  set u : ℂ := Complex.exp ((m.arg : ℝ) * Complex.I) with hudef
  have hunorm : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hup : u * (p : ℂ) = m := by
    rw [hudef, ← hmnorm, mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have hρderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u * (s : ℂ)) u t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul u
  have hρmem : ∀ t ∈ Icc (0 : ℝ) p, ‖u * (t : ℂ)‖ < 1 := fun t ht => by
    rw [norm_mul, hunorm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hp1
  have hnz : ‖(-z)‖ < 1 := by rwa [norm_neg]
  have hden : ∀ t ∈ Icc (0 : ℝ) p, (1 : ℂ) - (starRingEnd ℂ) (-z) * (u * (t : ℂ)) ≠ 0 :=
    fun t ht => one_sub_conj_mul_ne_zero_of_norm_lt_one (hρmem t ht) hnz
  have hσderiv : ∀ t ∈ Icc (0 : ℝ) p,
      HasDerivAt (fun s : ℝ => (u * (s : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (s : ℂ))))
        (u * ((1 - (starRingEnd ℂ) (-z) * -z) /
          (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))) ^ 2)) t := fun t ht => by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using
      (hasDerivAt_unitDiscMoebiusFormula (-z) (u * (t : ℂ)) (hden t ht)).scomp t (hρderiv t)
  have huIcc : uIcc (0 : ℝ) p = Icc 0 p := uIcc_of_le hp0
  refine ⟨p, fun t => (u * (t : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))),
    fun t => u * ((1 - (starRingEnd ℂ) (-z) * -z) /
      (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))) ^ 2),
    hp0, fun t ht => (hσderiv t ht).continuousAt.continuousWithinAt,
    fun t ht => hσderiv t (Ioo_subset_Icc_self ht), ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · exact continuousOn_const.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul
        (Continuous.continuousOn (by fun_prop)))).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  · exact mem_ball_zero_iff.mp (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnz
      (mem_ball_zero_iff.mpr (hρmem t ht)))
  · simp
  · have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hz (mem_ball_zero_iff.mpr hw)
    -- the goal is the path exhibited above applied at the endpoint `p`; `dsimp only`
    -- beta-reduces that application, after which `u * p` is the Moebius image of `w`
    dsimp only
    rw [hup, hmdef]
    simpa using hinv
  · rw [hyperbolicLength_unitDiscMoebiusFormula_comp hnz (γ' := fun _ => u)
      (fun t _ => hρderiv t) (fun t ht => hρmem t (huIcc ▸ ht)),
      hyperbolicLength_ray hunorm hp0 hp1, hpdef, ← hyperbolicDist_def, hyperbolicDist_comm]

/-- **The Poincaré metric is the length metric of the Poincaré density.** For two points of the
open unit disc, `hyperbolicDist z w` is the least hyperbolic length of a path in the disc running
from `z` to `w` that is continuous on its parameter interval and continuously differentiable
inside it.

Together with the classification of the hyperbolic geodesics in
`Conformal/Poincare/Betweenness.lean` this closes the circle of descriptions of the Poincaré
metric: the closed formula of `Hyperbolic/Distance.lean`, the infinitesimal density of
`Hyperbolic/Density.lean`, and the induced length metric all agree. -/
theorem isLeast_hyperbolicLength (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    IsLeast {L : ℝ | ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ ContinuousOn γ (Icc 0 r) ∧
      (∀ t ∈ Ioo 0 r, HasDerivAt γ (γ' t) t) ∧ ContinuousOn γ' (Icc 0 r) ∧
      (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
      hyperbolicLength γ 0 r = L} (hyperbolicDist z w) := by
  constructor
  · exact exists_hyperbolicLength_eq_hyperbolicDist hz hw
  · rintro L ⟨r, γ, γ', hr, hγ, hderiv, hγ', hmem, h0, hr', rfl⟩
    have := hyperbolicDist_le_hyperbolicLength_of_le hr hγ hderiv hγ' hmem
    rwa [h0, hr'] at this

end TauCeti
