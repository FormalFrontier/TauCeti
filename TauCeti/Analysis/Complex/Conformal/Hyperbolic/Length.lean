/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DensityLength
public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.ClosedForm
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.AutomorphismIsometry
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Derivative
public import TauCeti.Analysis.SpecialFunctions.Artanh
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
orientation of its parameter interval, and is nonnegative. That is the length of `γ` measured
against the density `(1 - ‖z‖ ^ 2)⁻¹` in the sense of `TauCeti.densityLength` of
`TauCeti/Analysis/Calculus/DensityLength.lean`, and `hyperbolicLength` is *defined* as that
instance: everything about the *parameter* side of the integral — that the length is unoriented
and additive, that it depends on the path only through its restriction to the parameter interval,
that it is unchanged by an affine, monotone or antitone reparametrisation, and that comparing the
density-weighted speeds of two paths compares their lengths — is proved there, for an arbitrary
density on an arbitrary real normed space, and is only read off here. What this file adds is what
the Poincaré density itself contributes. The two post-composition statements below — the Moebius
invariance `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` and the Schwarz--Pick estimate
`TauCeti.hyperbolicLength_comp_le` — reduce to a *pointwise* identity, respectively estimate,
between density-weighted speeds, which is where the Poincaré density enters, the passage from
there to the integrals being the general congruence and comparison; the lower bound below and the
path attaining it are one-variable calculus arguments of their own, described next.

The theorem is that `hyperbolicDist z w` is the **least** such length over `C¹` paths from `z` to
`w` (`TauCeti.isLeast_hyperbolicLength`): no path is shorter
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

the first inequality being `1 - ‖γ‖ ^ 2 ≤ 1 - ψ ^ 2` in the denominator. That is precisely the
hypothesis of the displacement bound `TauCeti.norm_sub_le_densityLength` — a function of the
parameter whose speed is dominated by the density-weighted speed of `γ` moves by at most the
length of `γ` — read at the Poincaré density and at `Real.artanh ∘ ψ`, whose displacement is
`Real.artanh ‖γ b‖ = hyperbolicDist (γ a) (γ b)`. Projecting on a *linear* functional rather than
on the norm is what keeps the comparison function differentiable where the path crosses the
origin.

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
continuous, since the derivative of a holomorphic function is again holomorphic, so
`TauCeti.densityLength_le_densityLength` integrates the estimate. The Moebius invariance is the
same reading of the same general lemma's equality counterpart
`TauCeti.densityLength_congr_of_eqOn`, which asks for no integrability, and that is why it holds
for a path with no regularity beyond a derivative inside its parameter interval.

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

Why `TauCeti.densityLength`, and not Mathlib's `ℝ≥0∞`-valued `Manifold.pathELength` of
`Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`, is the notion being instantiated is
argued in `TauCeti/Analysis/Calculus/DensityLength.lean`. Should the Poincaré disc later be given
a Riemannian structure, `TauCeti.isLeast_hyperbolicLength` is precisely the input needed to
identify `hyperbolicDist` with `Manifold.riemannianEDist`, and this file should be refactored onto
that API at that point.

## Main declarations

* `TauCeti.hyperbolicLength` — the density-weighted length of a path in the disc, with
  `TauCeti.hyperbolicLength_eq_integral` rewriting it against an explicit derivative, and
  `TauCeti.hyperbolicLength_symm`, `TauCeti.hyperbolicLength_nonneg`,
  `TauCeti.hyperbolicLength_const`, `TauCeti.hyperbolicLength_add` the basic evaluations and
  operations.
* `TauCeti.intervalIntegrable_norm_div_one_sub_norm_sq` and
  `TauCeti.intervalIntegrable_norm_deriv_div_one_sub_norm_sq` — for a `C¹` path in the disc the
  density-weighted speed is interval integrable, against an explicit derivative and against
  `deriv` respectively. The latter is the integrability hypothesis of
  `TauCeti.hyperbolicLength_add`, and what the Schwarz--Pick estimate and the lower bound below
  spend.
* `TauCeti.hyperbolicLength_comp_of_deriv_nonneg` and
  `TauCeti.hyperbolicLength_comp_of_deriv_nonpos` — **hyperbolic length is a reparametrisation
  invariant**: precomposing a path with a differentiable monotone, respectively antitone, map of
  the parameter transports the parameter interval and leaves the length unchanged. For the affine
  reparametrisations `t ↦ s * t + d` this needs nothing of the path,
  `TauCeti.hyperbolicLength_comp_mul_add`.
* `TauCeti.hyperbolicLength_congr` — the hyperbolic length of a path depends only on its values
  along its own parameter interval.

  These last three groups are the Poincaré readings of the density-independent statements
  `TauCeti.densityLength_symm`, `TauCeti.densityLength_nonneg`, `TauCeti.densityLength_const`,
  `TauCeti.densityLength_add`, `TauCeti.densityLength_comp_of_deriv_nonneg`,
  `TauCeti.densityLength_comp_of_deriv_nonpos`, `TauCeti.densityLength_comp_mul_add` and
  `TauCeti.densityLength_congr`, and are proved by naming them.
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
`b`: its length measured against the Poincaré density `(1 - ‖z‖ ^ 2)⁻¹` of
`Conformal/Hyperbolic/Density.lean`, in the sense of `TauCeti.densityLength`. Unfolded, it is the
Euclidean speed `‖deriv γ t‖` integrated over the unordered interval `uIcc a b` against that
density (`TauCeti.hyperbolicLength_def`).

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
  densityLength (fun z : ℂ => (1 - ‖z‖ ^ 2)⁻¹) γ a b

/-- The defining formula for the hyperbolic length of a path. -/
theorem hyperbolicLength_def (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ a b = ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2) := by
  simp only [hyperbolicLength, densityLength_def, div_eq_inv_mul]

/-- A degenerate parameter interval carries no hyperbolic length. -/
@[simp]
theorem hyperbolicLength_self (γ : ℝ → ℂ) (a : ℝ) : hyperbolicLength γ a a = 0 :=
  densityLength_self _ γ a

/-- Hyperbolic length does not depend on the orientation of the parameter interval. -/
theorem hyperbolicLength_symm (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ b a = hyperbolicLength γ a b :=
  densityLength_symm _ γ a b

/-- A constant path has zero hyperbolic length. -/
@[simp]
theorem hyperbolicLength_const (c : ℂ) (a b : ℝ) :
    hyperbolicLength (fun _ => c) a b = 0 :=
  densityLength_const _ c a b

/-- The hyperbolic length computed from an explicit derivative rather than from `deriv`. The
derivative is only asked for at the interior parameters, the two endpoints forming a null set. -/
theorem hyperbolicLength_eq_integral (hab : a ≤ b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
  rw [hyperbolicLength]
  simpa only [div_eq_inv_mul] using
    densityLength_eq_integral (ρ := fun z : ℂ => (1 - ‖z‖ ^ 2)⁻¹) hab hderiv

/-- A path running through the open unit disc has nonnegative hyperbolic length, whichever way
round its endpoints are: the Poincaré density is positive there. Only the interior parameters are
asked about, the two endpoints forming a null set. -/
theorem hyperbolicLength_nonneg (hmem : ∀ t ∈ uIoo a b, ‖γ t‖ < 1) :
    0 ≤ hyperbolicLength γ a b :=
  densityLength_nonneg fun t ht =>
    inv_nonneg.2 (by nlinarith [norm_nonneg (γ t), hmem t ht])

/-- For a `C¹` path in the disc the density-weighted speed is interval integrable: it is
continuous, its denominator staying away from zero because the path stays in the open disc. -/
theorem intervalIntegrable_norm_div_one_sub_norm_sq
    (hγ : ContinuousOn γ (uIcc a b)) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine hγ'.norm.div (continuousOn_const.sub (hγ.norm.pow 2)) fun t ht => ?_
  have hpos : (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := by nlinarith [norm_nonneg (γ t), hmem t ht]
  exact hpos.ne'

/-- The same integrability read against `deriv` rather than against the explicit derivative, the
two agreeing at the interior parameters and the two endpoints forming a null set. This is the
shape in which the integrability is asked for by `TauCeti.hyperbolicLength_add` and by the
comparison `TauCeti.densityLength_le_densityLength`. -/
theorem intervalIntegrable_norm_deriv_div_one_sub_norm_sq
    (hγ : ContinuousOn γ (uIcc a b)) (hγ' : ContinuousOn γ' (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    IntervalIntegrable (fun t => ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b :=
  (intervalIntegrable_norm_div_one_sub_norm_sq hγ hγ' hmem).congr_uIoo fun t ht => by
    rw [(hderiv t ht).deriv]

/-- **The hyperbolic length of a path depends only on its parameter interval.** Two paths that
agree inside the interval with endpoints `a` and `b` have the same hyperbolic length over it: at an
interior parameter they have the same germ, hence the same derivative, and the two endpoints form
a null set. -/
theorem hyperbolicLength_congr {δ : ℝ → ℂ} (hδ : EqOn δ γ (uIoo a b)) :
    hyperbolicLength δ a b = hyperbolicLength γ a b :=
  densityLength_congr hδ

/-- **Hyperbolic length is additive along the parameter interval**: the lengths of the two halves
of a path add up to the length of the whole, as soon as the density-weighted speed is integrable
over the whole. For a `C¹` path in the disc that hypothesis holds by continuity. -/
theorem hyperbolicLength_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hint : IntervalIntegrable (fun t => ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2))
      MeasureTheory.volume a c) :
    hyperbolicLength γ a b + hyperbolicLength γ b c = hyperbolicLength γ a c :=
  densityLength_add hab hbc (by simpa only [div_eq_inv_mul] using hint)

/-- **Hyperbolic length is invariant under affine reparametrisation.** Replacing the parameter `t`
by `s * t + d` for `s ≠ 0`, an orientation-preserving reparametrisation for `0 < s` and an
orientation-reversing one for `s < 0`, transports the parameter interval and leaves the length
unchanged: two affinely reparametrised copies of one path have the same hyperbolic length. For
instance `s = r`, `d = 0` reads the path of
`TauCeti.exists_hyperbolicLength_eq_hyperbolicDist`, defined on `[0, r]`, on the parameter
interval `[0, 1]` without changing its length. -/
theorem hyperbolicLength_comp_mul_add (γ : ℝ → ℂ) {s : ℝ} (hs : s ≠ 0) (d a b : ℝ) :
    hyperbolicLength (fun t => γ (s * t + d)) a b
      = hyperbolicLength γ (s * a + d) (s * b + d) :=
  densityLength_comp_mul_add _ γ hs d a b

/-- **Hyperbolic length is invariant under monotone reparametrisation.** Precomposing a path with
a map `φ` that is continuous on the parameter interval and has a nonnegative derivative inside it —
so that `φ` is monotone there — reparametrises the path and transports the parameter interval,
leaving the length unchanged. -/
theorem hyperbolicLength_comp_of_deriv_nonneg {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, 0 ≤ φ' t)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) :=
  densityLength_comp_of_deriv_nonneg hφ hderiv hsign hγ

/-- **Hyperbolic length is invariant under antitone reparametrisation.** The orientation-reversing
counterpart of `TauCeti.hyperbolicLength_comp_of_deriv_nonneg`: precomposing a path with a map `φ`
that is continuous on the parameter interval and has a nonpositive derivative inside it — so that
`φ` is antitone there — leaves the length unchanged, the parameter interval being transported with
its orientation reversed. Together the two lemmas say that hyperbolic length is a property of a
path rather than of its parametrisation. -/
theorem hyperbolicLength_comp_of_deriv_nonpos {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, φ' t ≤ 0)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    hyperbolicLength (γ ∘ φ) a b = hyperbolicLength γ (φ a) (φ b) :=
  densityLength_comp_of_deriv_nonpos hφ hderiv hsign hγ

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
  simp only [hyperbolicLength]
  refine densityLength_congr_of_eqOn fun t _ => ?_
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
  simp only [hyperbolicLength]
  refine densityLength_congr_of_eqOn fun t _ => ?_
  simp only [← Complex.star_def, deriv.star, norm_star]

/-- **Hyperbolic length is a Moebius invariant.** Post-composing a path in the disc with the
Moebius factor `z ↦ (z - c) / (1 - conj c * z)` leaves its hyperbolic length unchanged: this is
the infinitesimal Poincaré isometry
`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one` integrated along
the path. It is the tool that moves the starting point of a path to the origin.

Only the density-weighted speeds of the two paths are compared, and they agree at every interior
parameter, so this is `TauCeti.densityLength_congr_of_eqOn` and needs no integrability: the path
is asked for nothing beyond a derivative inside its parameter interval, and to stay in the disc
there, the two endpoints forming a null set — unlike the Schwarz--Pick estimate
`TauCeti.hyperbolicLength_comp_le` below, whose two integrands are only comparable. -/
theorem hyperbolicLength_unitDiscMoebiusFormula_comp (hc : ‖c‖ < 1)
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ uIoo a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  simp only [hyperbolicLength]
  refine densityLength_congr_of_eqOn fun t ht => ?_
  have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  have hcomp : HasDerivAt (fun s => (γ s - c) / (1 - (starRingEnd ℂ) c * γ s))
      (γ' t * ((1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2)) t := by
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).scomp t (hderiv t ht)
  -- the infinitesimal isometry, read at the explicit derivative of the Moebius factor
  have hkey : ‖(1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2‖
      / (1 - ‖(γ t - c) / (1 - (starRingEnd ℂ) c * γ t)‖ ^ 2) = 1 / (1 - ‖γ t‖ ^ 2) := by
    rw [← (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).deriv]
    exact norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one hc (hmem t ht)
  simp only [hcomp.deriv, (hderiv t ht).deriv]
  calc (1 - ‖(γ t - c) / (1 - (starRingEnd ℂ) c * γ t)‖ ^ 2)⁻¹
        * ‖γ' t * ((1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2)‖
      = ‖(1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2‖
          / (1 - ‖(γ t - c) / (1 - (starRingEnd ℂ) c * γ t)‖ ^ 2) * ‖γ' t‖ := by
        rw [norm_mul]; ring
    _ = 1 / (1 - ‖γ t‖ ^ 2) * ‖γ' t‖ := by rw [hkey]
    _ = (1 - ‖γ t‖ ^ 2)⁻¹ * ‖γ' t‖ := by rw [one_div]

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

/-- **Schwarz--Pick for the Poincaré length.** Post-composing a path in the open unit disc with a
holomorphic self-map of the disc does not increase its hyperbolic length. This is the infinitesimal
Schwarz--Pick inequality `TauCeti.norm_deriv_div_one_sub_norm_sq_le` integrated along the path, in
the same way as `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` integrates its equality
case; the path is asked to be `C¹` on its parameter interval, as in
`TauCeti.hyperbolicDist_le_hyperbolicLength`, so that both density-weighted speeds are
integrable, which is what `TauCeti.densityLength_le_densityLength` spends to turn the pointwise
comparison of the two integrands into a comparison of the two lengths. -/
theorem hyperbolicLength_comp_le {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (f ∘ γ) a b ≤ hyperbolicLength γ a b := by
  have hball : MapsTo γ (uIcc a b) (ball (0 : ℂ) 1) := fun t ht => mem_ball_zero_iff.mpr (hmem t ht)
  have hcomp : ∀ t ∈ uIoo a b, HasDerivAt (f ∘ γ) (γ' t * deriv f (γ t)) t := fun t ht =>
    hasDerivAt_comp_of_norm_lt_one hf (hmem t (uIoo_subset_uIcc_self ht)) (hderiv t ht)
  have hfmem : ∀ t ∈ uIcc a b, ‖(f ∘ γ) t‖ < 1 := fun t ht =>
    mem_ball_zero_iff.mp (hmaps (hball ht))
  -- the derivative of a holomorphic function is again holomorphic, hence continuous on the disc
  have hdf : ContinuousOn (fun t => deriv f (γ t)) (uIcc a b) :=
    ((hf.analyticOnNhd isOpen_ball).deriv.continuousOn).comp hγ hball
  -- the two integrands are continuous, and agree with `deriv` inside the parameter interval
  have hint1 : IntervalIntegrable (fun t => (1 - ‖(f ∘ γ) t‖ ^ 2)⁻¹ * ‖deriv (f ∘ γ) t‖)
      MeasureTheory.volume a b := by
    simpa only [div_eq_inv_mul] using intervalIntegrable_norm_deriv_div_one_sub_norm_sq
      (hf.continuousOn.comp hγ hball) (hγ'.mul hdf) hcomp hfmem
  have hint2 : IntervalIntegrable (fun t => (1 - ‖γ t‖ ^ 2)⁻¹ * ‖deriv γ t‖)
      MeasureTheory.volume a b := by
    simpa only [div_eq_inv_mul] using
      intervalIntegrable_norm_deriv_div_one_sub_norm_sq hγ hγ' hderiv hmem
  simp only [hyperbolicLength]
  refine densityLength_le_densityLength hint1 hint2 fun t ht => ?_
  rw [(hcomp t ht).deriv, (hderiv t ht).deriv, ← div_eq_inv_mul, ← div_eq_inv_mul]
  calc ‖γ' t * deriv f (γ t)‖ / (1 - ‖(f ∘ γ) t‖ ^ 2)
      = ‖γ' t‖ * (‖deriv f (γ t)‖ / (1 - ‖f (γ t)‖ ^ 2)) := by
        simp only [Function.comp_apply, norm_mul, mul_div_assoc]
    _ ≤ ‖γ' t‖ * (1 / (1 - ‖γ t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (norm_deriv_div_one_sub_norm_sq_le hf hmaps (hball (uIoo_subset_uIcc_self ht)))
          (norm_nonneg _)
    _ = ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := mul_one_div _ _

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
  rwa [hyperbolicLength_congr (δ := g ∘ (f ∘ γ)) fun t ht =>
    hgf (hball (uIoo_subset_uIcc_self ht))] at key

/-! ## The distance is a lower bound for the length -/

/-- **A path issued from the origin admits a real comparison function.** For a path `γ` with
`γ a = 0` there are real functions `ψ` and `ψ'` with `ψ a = 0` and `ψ b = ‖γ b‖`, dominated
pointwise by `‖γ‖` and `‖γ'‖`, with `ψ` continuous wherever `γ` is and `ψ'` its derivative
wherever `γ'` is that of `γ`. -/
private theorem exists_real_comparison_of_eq_zero {s u : Set ℝ} (hγ : ContinuousOn γ s)
    (hderiv : ∀ x ∈ u, HasDerivAt γ (γ' x) x) (h0 : γ a = 0) :
    ∃ ψ ψ' : ℝ → ℝ, ψ a = 0 ∧ ψ b = ‖γ b‖ ∧ (∀ x, |ψ x| ≤ ‖γ x‖) ∧
      (∀ x, |ψ' x| ≤ ‖γ' x‖) ∧ ContinuousOn ψ s ∧
      ∀ x ∈ u, HasDerivAt ψ (ψ' x) x := by
  -- Rotate by a unit `v` with `v * γ b = ‖γ b‖`, then take real parts; `γ` itself need not be
  -- differentiable in norm, but its real part is.
  obtain ⟨v, hvnorm, hvb⟩ := Complex.exists_norm_eq_mul_self (γ b)
  refine ⟨fun t => (v * γ t).re, fun t => (v * γ' t).re, by simp [h0],
    by simp only [← hvb, Complex.ofReal_re],
    fun t => (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul]),
    fun t => (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul]),
    Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hγ), fun t ht => ?_⟩
  simpa [Function.comp_def] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hderiv t ht).const_mul v)

/-- **A comparison function has hyperbolic speed at most that of the path.** At a point `t` where
`γ` lies inside the unit disc, if `|ψ t| ≤ ‖γ t‖` and the derivative of `ψ` at `t` is bounded in
absolute value by `‖γ' t‖`, then `Real.artanh ∘ ψ` moves at `t` at most at the
Poincaré-density-weighted speed of `γ`. -/
private theorem norm_deriv_artanh_le_of_abs_le {ψ : ℝ → ℝ} {d t : ℝ} (hψ : |ψ t| ≤ ‖γ t‖)
    (hd : |d| ≤ ‖γ' t‖) (hψd : HasDerivAt ψ d t) (hγd : HasDerivAt γ (γ' t) t) (ht : ‖γ t‖ < 1) :
    ‖deriv (fun s => Real.artanh (ψ s)) t‖ ≤ (1 - ‖γ t‖ ^ 2)⁻¹ * ‖deriv γ t‖ := by
  have hmem : ψ t ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (hψ.trans_lt ht)
  have hPpos : (0 : ℝ) < 1 - ψ t ^ 2 := by nlinarith [hmem.1, hmem.2]
  have hPQ : 1 - ‖γ t‖ ^ 2 ≤ 1 - ψ t ^ 2 := by
    nlinarith [hψ, abs_nonneg (ψ t), sq_abs (ψ t), norm_nonneg (γ t)]
  rw [hγd.deriv, ← div_eq_inv_mul, (hψd.artanh hmem).deriv, Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_pos hPpos, inv_mul_eq_div]
  gcongr
  nlinarith [norm_nonneg (γ t), ht]

/-- The lower bound for a path issued from the origin: its hyperbolic length is at least
`Real.artanh` of the Euclidean norm of its endpoint, which is the hyperbolic distance from the
origin to that endpoint. -/
private theorem artanh_norm_le_hyperbolicLength (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) (h0 : γ a = 0) :
    Real.artanh ‖γ b‖ ≤ hyperbolicLength γ a b := by
  have hγu : ContinuousOn γ (uIcc a b) := by rwa [uIcc_of_le hab]
  have hγ'u : ContinuousOn γ' (uIcc a b) := by rwa [uIcc_of_le hab]
  have hmemu : ∀ t ∈ uIcc a b, ‖γ t‖ < 1 := by rwa [uIcc_of_le hab]
  have hderivu : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t := by rwa [uIoo_of_le hab]
  -- the density-weighted speed in the shape `TauCeti.densityLength` integrates it
  have hint2 : IntervalIntegrable (fun t => (1 - ‖γ t‖ ^ 2)⁻¹ * ‖deriv γ t‖)
      MeasureTheory.volume a b := by
    simpa only [div_eq_inv_mul] using
      intervalIntegrable_norm_deriv_div_one_sub_norm_sq hγu hγ'u hderivu hmemu
  -- compare with a real function `ψ` rather than with `t ↦ ‖γ t‖`, which need not be differentiable
  obtain ⟨ψ, ψ', hψa, hψb, hψbound, hψ'bound, hψcont, hψderiv⟩ :=
    exists_real_comparison_of_eq_zero (b := b) hγ hderiv h0
  have hψmem : ∀ t ∈ Icc a b, ψ t ∈ Ioo (-1 : ℝ) 1 := fun t ht =>
    abs_lt.mp ((hψbound t).trans_lt (hmem t ht))
  -- `Real.artanh ∘ ψ` runs from `0` to `Real.artanh ‖γ b‖` with speed at most the
  -- density-weighted speed of `γ`, so the displacement bound applies to it.
  have hcont : ContinuousOn (fun t => Real.artanh (ψ t)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact Real.continuousOn_artanh.comp hψcont fun t ht => hψmem t ht
  have hdiff : DifferentiableOn ℝ (fun t => Real.artanh (ψ t)) (uIoo a b) := by
    rw [uIoo_of_le hab]
    exact fun t ht => ((hψderiv t ht).artanh
      (hψmem t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ uIoo a b,
      ‖deriv (fun s => Real.artanh (ψ s)) t‖ ≤ (1 - ‖γ t‖ ^ 2)⁻¹ * ‖deriv γ t‖ := by
    rw [uIoo_of_le hab]
    exact fun t ht => norm_deriv_artanh_le_of_abs_le (hψbound t) (hψ'bound t) (hψderiv t ht)
      (hderiv t ht) (hmem t (Ioo_subset_Icc_self ht))
  rw [hyperbolicLength]
  have key := norm_sub_le_densityLength (ρ := fun z : ℂ => (1 - ‖z‖ ^ 2)⁻¹) (γ := γ)
    hcont hdiff (.of_forall hbound) hint2
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
  have hderivu : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t := by rwa [uIoo_of_le hab]
  have hmemu : ∀ t ∈ uIoo a b, ‖γ t‖ < 1 := by
    rw [uIoo_of_le hab]
    exact fun t ht => hmem t (Ioo_subset_Icc_self ht)
  have key := artanh_norm_le_hyperbolicLength hab hσcont hσderiv hσ'cont hσmem hσa
  rw [hyperbolicLength_unitDiscMoebiusFormula_comp hc hderivu hmemu] at key
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
  have hρmem' : ∀ t ∈ uIoo (0 : ℝ) p, ‖u * (t : ℂ)‖ < 1 := by
    rw [uIoo_of_le hp0]
    exact fun t ht => hρmem t (Ioo_subset_Icc_self ht)
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
      (fun t _ => hρderiv t) hρmem',
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
