/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue

/-!
# Continuous logarithms on a set, and the Borsuk map of two points

A complex-valued function `g` **has a continuous logarithm on** a set `S` when some continuous
`h` satisfies `exp (h x) = g x` throughout `S`; this file introduces that predicate,
`TauCeti.HasContinuousLogOn`, and proves the two elementary facts about it that planar separation
arguments run on.

The predicate is the natural home of the classical *nonvanishing plus no winding* condition. It
implies `g` is continuous and zero-free on `S` but is strictly stronger, and unlike Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` — which produces a logarithm on a *simply connected
open* set — it makes sense, and is genuinely restrictive, on a set with no interior at all: a
compact `K ⊆ ℂ` such as a curve. That is exactly the case the separation theory needs, so the
existence statement has to become a predicate carrying its own algebra rather than a one-off
lemma. The algebra is that of a group homomorphism out of the zero-free continuous functions:
logarithms add under multiplication (`TauCeti.HasContinuousLogOn.mul`), negate under inversion
(`TauCeti.HasContinuousLogOn.inv`), restrict along inclusions, and exist outright when `g` avoids
the slit `Complex.slitPlane`ᶜ, where the principal branch works
(`TauCeti.hasContinuousLogOn_of_mapsTo_slitPlane`).

## Gluing along a connected overlap

The first substantial fact is that continuous logarithms glue: if `S` and `T` are closed, their
overlap `S ∩ T` is preconnected, and `g` has a continuous logarithm on each, then it has one on
`S ∪ T` (`TauCeti.HasContinuousLogOn.union`). Two logarithms of the same function differ by a
value of `Complex.exp ⁻¹' {1}`, that is by an integer multiple of `2 * π * I`, and on a
preconnected overlap that difference cannot move between two such multiples: the imaginary parts
of a preconnected set of them would have to fill the interval between, which contains the
half-step `2 * π * n + π`. So one logarithm can be shifted by a single constant to agree with the
other on the overlap, and the two then define one continuous function on the closed union. The
constancy step is isolated as `TauCeti.eq_of_isPreconnected_of_forall_exp_eq_one`.

## The Borsuk map

For `a b : ℂ` the **Borsuk map** of the pair is `z ↦ (z - a) / (z - b)`, defined and zero-free off
`{a, b}`. Its logarithms detect how a set sits between the two points: the main theorem here is
that if `b` lies in the connected component of `a` in the complement of a closed `K`, then the
Borsuk map has a continuous logarithm on `K`
(`TauCeti.hasContinuousLogOn_sub_div_sub`). Equivalently, in contrapositive form: a set on which
the Borsuk map admits no continuous logarithm *separates* `a` from `b`.

The proof is a connectedness argument on the second point, not a construction. Call `w`
*good* if `z ↦ (z - a) / (z - w)` has a continuous logarithm on `K`. The point `a` is good, its
Borsuk map being the constant `1`. Moving `w` by less than half the distance from `w` to `K`
multiplies the Borsuk map by `z ↦ (z - w) / (z - w')`, a function whose values lie within distance
`1` of `1` and hence in the slit plane, so that factor has a logarithm of its own
(`TauCeti.hasContinuousLogOn_sub_div_sub_of_norm_lt`) and goodness transfers — in both directions,
since the estimate is symmetric. So the good and the bad points of `Kᶜ` are both open, and the
component of `a` is preconnected, hence entirely good.

## What this settles, and what it does not

Only one implication of the classical criterion is proved here. Its converse — that a Borsuk map
with a continuous logarithm on a *compact* `K` forces `a` and `b` into one component of `Kᶜ` — is
a genuinely deeper statement, equivalent to a case of Alexander duality: it fails for the naive
reason one might hope to prove it, since a compact connected set can separate the plane while
containing no arc at all, so no argument through winding numbers of curves inside `K` can reach
it. Nothing below assumes it, and no statement is phrased so as to presume it.

## Roadmap role

**Plane separation for Jordan curves** is the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence. Two
statements of the development wait on it, and each is a separation statement about a pair of
points: `J ⊆ closure (filledHull J \ J)`, recorded in the roadmap section of
`TauCeti/Topology/FilledHull.lean` and consumed as a hypothesis by
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Inside.lean`; and
`frontier Ω ∩ closure A ∩ closure B ⊆ closure γ`, the input
`TauCeti/Analysis/Complex/Conformal/Crosscut/BoundarySplit.lean` names as missing before its
dichotomy `TauCeti.subset_or_subset_of_isPreconnected_frontier_image_sdiff` can be fed a boundary
arc.

The classical route to both runs through Janiszewski's theorem — two closed sets with connected
intersection, neither of which separates a pair of points, have a union that does not separate it
either — and Janiszewski is proved by translating "does not separate" into "the Borsuk map has a
continuous logarithm" and gluing the two logarithms over the connected intersection. This file
supplies that translation in the direction that holds without duality, together with the gluing;
what remains before Janiszewski is the converse direction described above.

The one statement below already phrased in the vocabulary of that development is
`TauCeti.mem_filledHull_or_mem_filledHull_of_not_hasContinuousLogOn`: a bounded closed set on which
the Borsuk map has no continuous logarithm encloses `a` or `b` in its filled hull. It reads the
criterion through `TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn` of
`TauCeti/Analysis/Normed/Module/FilledHull.lean`, so a source of logarithm obstructions becomes a
source of the enclosure hypothesis `Conformal/Crosscut/Inside.lean` consumes.

## Coordination with upstream Mathlib

Mathlib has continuous branches of the logarithm on simply connected open sets
(`Complex.exists_continuousOn_eqOn_exp_comp` of `Mathlib/Analysis/Complex/BranchLogRoot.lean`,
which layer L3 consumes), but no predicate for a logarithm on an arbitrary set, no gluing theorem
for logarithms, and no separation theory for the plane. Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. So this
file is new Lean formalization rather than a temporary shim, and it consumes no L0–L3 shim: its
only complex-analytic input is the principal branch `Complex.log` on `Complex.slitPlane`.

## Main results

* `TauCeti.HasContinuousLogOn` — the predicate, with `TauCeti.hasContinuousLogOn_iff` exposing it,
  and its closure properties `TauCeti.HasContinuousLogOn.mul`, `.inv`, `.div`, `.mono`, `.congr`.
* `TauCeti.hasContinuousLogOn_of_mapsTo_slitPlane` — a function landing in the slit plane has the
  principal logarithm.
* `TauCeti.eq_of_isPreconnected_of_forall_exp_eq_one` — a preconnected set of logarithms of `1` is
  a single point.
* `TauCeti.HasContinuousLogOn.union` — **gluing**: logarithms on two closed sets with preconnected
  overlap combine into one on the union.
* `TauCeti.hasContinuousLogOn_sub_div_sub_of_norm_lt` — the Borsuk map of two points closer to each
  other than to `K` has a logarithm on `K`.
* `TauCeti.hasContinuousLogOn_sub_div_sub` — **the criterion**: the Borsuk map of two points in one
  component of the complement of a closed set has a continuous logarithm on that set.
* `TauCeti.mem_filledHull_or_mem_filledHull_of_not_hasContinuousLogOn` — its separation-facing
  form: a bounded closed set admitting no such logarithm encloses one of the two points.

## References

* K. Borsuk, *Über Schnitte der euklidischen Räume*, Math. Ann. **106** (1932).
* S. Janiszewski, *Sur les coupures du plan faites par les continus*, Prace Mat.-Fiz. **26** (1913).
* R. B. Burckel, *An Introduction to Classical Complex Analysis I*, §4 (logarithms and separation).
* J. R. Munkres, *Topology*, §61–63 (the separation theorems of the plane).
-/

public section

namespace TauCeti

open Metric Set

open scoped Real

variable {X : Type*} [TopologicalSpace X] {g g' : X → ℂ} {S T : Set X}

/-! ## The predicate and its algebra -/

/-- `HasContinuousLogOn g S` asserts that the complex-valued function `g` admits a **continuous
logarithm** on the set `S`: some continuous `h` satisfies `exp (h x) = g x` for every `x ∈ S`.

On a simply connected open set this holds for every zero-free continuous `g`, by Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp`; on a general set — a compact subset of `ℂ`, say — it
is a genuine restriction, and it is that restriction which detects separation of the plane. -/
def HasContinuousLogOn (g : X → ℂ) (S : Set X) : Prop :=
  ∃ h : X → ℂ, ContinuousOn h S ∧ EqOn (fun x => Complex.exp (h x)) g S

/-- The defining property of `TauCeti.HasContinuousLogOn`, with the equality spelled out
pointwise. -/
theorem hasContinuousLogOn_iff :
    HasContinuousLogOn g S ↔
      ∃ h : X → ℂ, ContinuousOn h S ∧ ∀ x ∈ S, Complex.exp (h x) = g x :=
  ⟨fun ⟨h, hc, he⟩ => ⟨h, hc, fun _ hx => he hx⟩, fun ⟨h, hc, he⟩ => ⟨h, hc, fun _ hx => he _ hx⟩⟩

/-- A function with a continuous logarithm has no zero, the exponential having none. -/
theorem HasContinuousLogOn.ne_zero (h : HasContinuousLogOn g S) {x : X} (hx : x ∈ S) : g x ≠ 0 := by
  obtain ⟨u, -, hu⟩ := h
  rw [← hu hx]
  exact Complex.exp_ne_zero _

/-- A function with a continuous logarithm is itself continuous, being `exp` of one. -/
theorem HasContinuousLogOn.continuousOn (h : HasContinuousLogOn g S) : ContinuousOn g S := by
  obtain ⟨u, hc, hu⟩ := h
  exact (Complex.continuous_exp.comp_continuousOn hc).congr fun _ hx => (hu hx).symm

/-- Continuous logarithms restrict to subsets. -/
theorem HasContinuousLogOn.mono (h : HasContinuousLogOn g S) (hTS : T ⊆ S) :
    HasContinuousLogOn g T :=
  let ⟨u, hc, hu⟩ := h
  ⟨u, hc.mono hTS, hu.mono hTS⟩

/-- Having a continuous logarithm depends only on the values on the set. -/
theorem HasContinuousLogOn.congr (h : HasContinuousLogOn g S) (hg : EqOn g g' S) :
    HasContinuousLogOn g' S :=
  let ⟨u, hc, hu⟩ := h
  ⟨u, hc, hu.trans hg⟩

/-- A nonzero constant has a continuous logarithm, namely the constant principal logarithm. -/
theorem hasContinuousLogOn_const {c : ℂ} (hc : c ≠ 0) : HasContinuousLogOn (fun _ : X => c) S :=
  ⟨fun _ => Complex.log c, continuousOn_const, fun _ _ => Complex.exp_log hc⟩

/-- **Logarithms add under multiplication.** -/
theorem HasContinuousLogOn.mul (h : HasContinuousLogOn g S) (h' : HasContinuousLogOn g' S) :
    HasContinuousLogOn (fun x => g x * g' x) S := by
  obtain ⟨u, hc, hu⟩ := h
  obtain ⟨u', hc', hu'⟩ := h'
  exact ⟨fun x => u x + u' x, hc.add hc', fun x hx => by
    simp only [Complex.exp_add, hu hx, hu' hx]⟩

/-- **Logarithms negate under inversion.** -/
theorem HasContinuousLogOn.inv (h : HasContinuousLogOn g S) :
    HasContinuousLogOn (fun x => (g x)⁻¹) S := by
  obtain ⟨u, hc, hu⟩ := h
  exact ⟨fun x => -u x, hc.neg, fun x hx => by simp only [Complex.exp_neg, hu hx]⟩

/-- **Logarithms subtract under division.** -/
theorem HasContinuousLogOn.div (h : HasContinuousLogOn g S) (h' : HasContinuousLogOn g' S) :
    HasContinuousLogOn (fun x => g x / g' x) S :=
  (h.mul h'.inv).congr fun x _ => (div_eq_mul_inv (g x) (g' x)).symm

/-- **A function landing in the slit plane has the principal logarithm.** This is the only source
of logarithms that does not come from another logarithm, and everything below is built on it. -/
theorem hasContinuousLogOn_of_mapsTo_slitPlane (hg : ContinuousOn g S)
    (hS : ∀ x ∈ S, g x ∈ Complex.slitPlane) : HasContinuousLogOn g S :=
  ⟨fun x => Complex.log (g x), hg.clog hS, fun _ hx =>
    Complex.exp_log (Complex.slitPlane_ne_zero (hS _ hx))⟩

/-! ## Gluing along a connected overlap -/

/-- **A preconnected set of logarithms of `1` is a single point.** Every such logarithm is an
integer multiple of `2 * π * I`, so the set has all its real parts `0`, and its imaginary parts
form a preconnected subset of `ℝ` inside `2 * π * ℤ`. Two distinct multiples there would force the
half-step `2 * π * n + π` between them into the set as well, and that is no multiple of `2 * π`. -/
theorem eq_of_isPreconnected_of_forall_exp_eq_one {P : Set ℂ} (hP : IsPreconnected P)
    (h : ∀ w ∈ P, Complex.exp w = 1) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ P) (h₂ : w₂ ∈ P) : w₁ = w₂ := by
  have hform : ∀ w ∈ P, w.re = 0 ∧ ∃ n : ℤ, w.im = 2 * π * n := by
    intro w hw
    obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.mp (h w hw)
    exact ⟨by simp, n, by simp; ring⟩
  have him : IsPreconnected (Complex.im '' P) :=
    hP.image _ Complex.continuous_im.continuousOn
  -- the imaginary part cannot jump from one multiple of `2 * π` to another
  have key : ∀ v₁ ∈ P, ∀ v₂ ∈ P, v₁.im ≤ v₂.im → v₁.im = v₂.im := by
    intro v₁ hv₁ v₂ hv₂ hle
    by_contra hne
    obtain ⟨-, n₁, hn₁⟩ := hform v₁ hv₁
    obtain ⟨-, n₂, hn₂⟩ := hform v₂ hv₂
    have hlt : v₁.im < v₂.im := lt_of_le_of_ne hle hne
    have hn : (n₁ : ℝ) < n₂ := by
      rw [hn₁, hn₂] at hlt
      nlinarith [Real.pi_pos]
    have hn' : (n₁ : ℝ) + 1 ≤ n₂ := by
      exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast hn)
    have hmem : v₁.im + π ∈ Icc v₁.im v₂.im := by
      refine ⟨by linarith [Real.pi_pos], ?_⟩
      rw [hn₁, hn₂]
      rw [hn₁] at hle
      nlinarith [Real.pi_pos]
    obtain ⟨w, hwP, hw⟩ :=
      him.Icc_subset (mem_image_of_mem _ hv₁) (mem_image_of_mem _ hv₂) hmem
    obtain ⟨-, n, hn₀⟩ := hform w hwP
    rw [hn₀, hn₁] at hw
    have hcancel : π * (2 * (n : ℝ)) = π * (2 * (n₁ : ℝ) + 1) := by linarith
    have h2 : (2 * (n : ℝ)) = 2 * (n₁ : ℝ) + 1 := mul_left_cancel₀ Real.pi_ne_zero hcancel
    have : (2 * n : ℤ) = 2 * n₁ + 1 := by exact_mod_cast h2
    omega
  refine Complex.ext ?_ ?_
  · rw [(hform w₁ h₁).1, (hform w₂ h₂).1]
  · rcases le_total w₁.im w₂.im with hle | hle
    · exact key _ h₁ _ h₂ hle
    · exact (key _ h₂ _ h₁ hle).symm

/-- **Continuous logarithms glue along a preconnected overlap.** Two logarithms of `g` differ, on
the overlap, by a logarithm of `1`; that difference is constant there by
`TauCeti.eq_of_isPreconnected_of_forall_exp_eq_one`, so shifting one logarithm by the constant
makes the two agree on `S ∩ T` and define a single function, continuous on the union because both
pieces are closed.

The overlap is only asked to be preconnected, so the disjoint case is allowed: there the two
logarithms are glued unchanged. -/
theorem HasContinuousLogOn.union (hS : IsClosed S) (hT : IsClosed T)
    (hST : IsPreconnected (S ∩ T)) (h : HasContinuousLogOn g S) (h' : HasContinuousLogOn g T) :
    HasContinuousLogOn g (S ∪ T) := by
  classical
  obtain ⟨u, hu, hue⟩ := h
  obtain ⟨v, hv, hve⟩ := h'
  -- on the overlap the two logarithms differ by a logarithm of `1`
  have hdiff : ∀ x ∈ S ∩ T, Complex.exp (u x - v x) = 1 := by
    rintro x ⟨hxS, hxT⟩
    have h₁ : Complex.exp (u x) = g x := hue hxS
    have h₂ : Complex.exp (v x) = g x := hve hxT
    rw [Complex.exp_sub, h₁, h₂, div_self]
    rw [← h₂]
    exact Complex.exp_ne_zero _
  -- and that difference is a single constant
  obtain ⟨c, hc, hc1⟩ :
      ∃ c : ℂ, (∀ x ∈ S ∩ T, u x - v x = c) ∧ Complex.exp c = 1 := by
    rcases (S ∩ T).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · exact ⟨0, fun x hx => absurd hx (by simp [hempty]), Complex.exp_zero⟩
    refine ⟨u x₀ - v x₀, fun x hx => ?_, hdiff x₀ hx₀⟩
    refine eq_of_isPreconnected_of_forall_exp_eq_one
      (hST.image _ ((hu.mono inter_subset_left).sub (hv.mono inter_subset_right)))
      ?_ (mem_image_of_mem _ hx) (mem_image_of_mem _ hx₀)
    rintro w ⟨y, hy, rfl⟩
    exact hdiff y hy
  refine ⟨S.piecewise u fun x => v x + c, ?_, fun x hx => ?_⟩
  · refine ContinuousOn.union_of_isClosed ?_ ?_ hS hT
    · exact hu.congr fun x hx => S.piecewise_eq_of_mem _ _ hx
    · have hvc : ContinuousOn (fun x => v x + c) T := hv.add continuousOn_const
      refine hvc.congr fun x hx => ?_
      by_cases hxS : x ∈ S
      · rw [S.piecewise_eq_of_mem _ _ hxS]
        have := hc x ⟨hxS, hx⟩
        linear_combination this
      · exact S.piecewise_eq_of_notMem _ _ hxS
  · have key : Complex.exp (S.piecewise u (fun x => v x + c) x) = g x := by
      rcases hx with hx | hx
      · rw [S.piecewise_eq_of_mem _ _ hx]
        exact hue hx
      · by_cases hxS : x ∈ S
        · rw [S.piecewise_eq_of_mem _ _ hxS]
          exact hue hxS
        · rw [S.piecewise_eq_of_notMem _ _ hxS, Complex.exp_add, hc1, mul_one]
          exact hve hx
    exact key

/-! ## The Borsuk map of a pair of points -/

variable {K : Set ℂ} {a b w w' : ℂ}

/-- **The Borsuk map of two points nearer each other than the set has a logarithm there.** If every
`z ∈ K` is further from `w'` than `w` is, then `(z - w) / (z - w') = 1 + (w' - w) / (z - w')` lies
within distance `1` of `1`, hence in the slit plane, where the principal logarithm is available. -/
theorem hasContinuousLogOn_sub_div_sub_of_norm_lt (h : ∀ z ∈ K, ‖w - w'‖ < ‖z - w'‖) :
    HasContinuousLogOn (fun z => (z - w) / (z - w')) K := by
  have hne : ∀ z ∈ K, z - w' ≠ 0 := by
    intro z hz h0
    have := h z hz
    rw [h0, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  refine hasContinuousLogOn_of_mapsTo_slitPlane
    ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) hne)
    fun z hz => ?_
  have hz' : z - w' ≠ 0 := hne z hz
  have hpos : 0 < ‖z - w'‖ := norm_pos_iff.mpr hz'
  have hrw : (z - w) / (z - w') = 1 + (w' - w) / (z - w') := by
    field_simp
    ring
  rw [hrw]
  refine Complex.mem_slitPlane_of_norm_lt_one ?_
  rw [norm_div, div_lt_one hpos, norm_sub_rev]
  exact h z hz

/-- **The Borsuk-map criterion, sufficient direction.** If `b` lies in the connected component of
`a` in the complement of a closed set `K`, then the Borsuk map `z ↦ (z - a) / (z - b)` has a
continuous logarithm on `K`.

Contrapositively: a closed set carrying no continuous logarithm of the Borsuk map of `a` and `b`
separates the two points.

The proof moves the second point rather than constructing the logarithm. The set of points `w` of
`Kᶜ` for which `z ↦ (z - a) / (z - w)` has a logarithm on `K` is open, because displacing `w` by
less than half its distance to `K` multiplies the Borsuk map by a factor covered by
`TauCeti.hasContinuousLogOn_sub_div_sub_of_norm_lt`; the same estimate run backwards makes the
complementary set of `Kᶜ` open too. Since `a` itself is in the first set — its Borsuk map is the
constant `1` — and the component of `a` is preconnected, the component lies in it. -/
theorem hasContinuousLogOn_sub_div_sub (hK : IsClosed K) (hb : b ∈ connectedComponentIn Kᶜ a) :
    HasContinuousLogOn (fun z => (z - a) / (z - b)) K := by
  have ha : a ∈ Kᶜ := by
    by_contra hmem
    rw [connectedComponentIn_eq_empty hmem] at hb
    exact hb
  -- displacing the second point preserves the existence of a logarithm
  have step : ∀ w w' : ℂ, w ∉ K → (∀ z ∈ K, ‖w - w'‖ < ‖z - w'‖) →
      HasContinuousLogOn (fun z => (z - a) / (z - w)) K →
      HasContinuousLogOn (fun z => (z - a) / (z - w')) K := by
    intro w w' hwK hlt hlog
    refine (hlog.mul (hasContinuousLogOn_sub_div_sub_of_norm_lt hlt)).congr fun z hz => ?_
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr fun hzeq => hwK (hzeq ▸ hz)
    have hzw' : z - w' ≠ 0 := by
      intro h0
      have := hlt z hz
      rw [h0, norm_zero] at this
      exact absurd this (not_lt.mpr (norm_nonneg _))
    field_simp
  -- every point off `K` is at a positive distance from it
  have hradius : ∀ w ∉ K, ∃ ε > 0, ∀ z ∈ K, ε ≤ ‖z - w‖ := by
    intro w hw
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hK.isOpen_compl w hw
    refine ⟨ε, hε, fun z hz => le_of_not_gt fun hlt => ?_⟩
    exact hsub (by simpa [Metric.mem_ball, dist_eq_norm] using hlt) hz
  set G : Set ℂ := {w | w ∉ K ∧ HasContinuousLogOn (fun z => (z - a) / (z - w)) K} with hG
  set B : Set ℂ := {w | w ∉ K ∧ ¬ HasContinuousLogOn (fun z => (z - a) / (z - w)) K} with hB
  -- the displacement estimate, in the form both openness proofs use
  have hnear : ∀ w ∉ K, ∀ ε > 0, (∀ z ∈ K, ε ≤ ‖z - w‖) → ∀ w' ∈ ball w (ε / 2),
      w' ∉ K ∧ (∀ z ∈ K, ‖w - w'‖ < ‖z - w'‖) ∧ ∀ z ∈ K, ‖w' - w‖ < ‖z - w‖ := by
    intro w _ ε hε hεK w' hw'
    rw [Metric.mem_ball, dist_eq_norm] at hw'
    have hsymm : ‖w - w'‖ < ε / 2 := by rwa [norm_sub_rev]
    have hw'K : w' ∉ K := fun hz => absurd (hεK w' hz) (by linarith)
    refine ⟨hw'K, fun z hz => ?_, fun z hz => lt_of_lt_of_le (by linarith) (hεK z hz)⟩
    have htri : ‖z - w‖ ≤ ‖z - w'‖ + ‖w' - w‖ := by
      calc ‖z - w‖ = ‖z - w' + (w' - w)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - w'‖ + ‖w' - w‖ := norm_add_le _ _
    have := hεK z hz
    linarith
  have hGopen : IsOpen G := by
    rw [Metric.isOpen_iff]
    rintro w hw
    rw [hG, mem_ofPred_eq] at hw
    obtain ⟨ε, hε, hεK⟩ := hradius w hw.1
    refine ⟨ε / 2, by positivity, fun w' hw' => ?_⟩
    obtain ⟨hw'K, hfar, -⟩ := hnear w hw.1 ε hε hεK w' hw'
    exact ⟨hw'K, step w w' hw.1 hfar hw.2⟩
  have hBopen : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro w hw
    rw [hB, mem_ofPred_eq] at hw
    obtain ⟨ε, hε, hεK⟩ := hradius w hw.1
    refine ⟨ε / 2, by positivity, fun w' hw' => ?_⟩
    obtain ⟨hw'K, -, hback⟩ := hnear w hw.1 ε hε hεK w' hw'
    exact ⟨hw'K, fun hlog' => hw.2 (step w' w hw'K hback hlog')⟩
  have hsub : connectedComponentIn Kᶜ a ⊆ G := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hGopen hBopen ?_ ?_ ?_
    · rw [Set.disjoint_left]
      rintro x hx hx'
      rw [hG, mem_ofPred_eq] at hx
      rw [hB, mem_ofPred_eq] at hx'
      exact hx'.2 hx.2
    · intro x hx
      have hxK : x ∉ K := connectedComponentIn_subset _ _ hx
      by_cases hlog : HasContinuousLogOn (fun z => (z - a) / (z - x)) K
      · exact Or.inl ⟨hxK, hlog⟩
      · exact Or.inr ⟨hxK, hlog⟩
    · refine ⟨a, mem_connectedComponentIn ha, ha, (hasContinuousLogOn_const one_ne_zero).congr ?_⟩
      intro z hz
      have : z - a ≠ 0 := sub_ne_zero.mpr fun hzeq => ha (hzeq ▸ hz)
      simp [div_self this]
  exact (hsub hb).2

/-- **A bounded closed set with no continuous logarithm of a Borsuk map encloses one of the two
points.** This is `TauCeti.hasContinuousLogOn_sub_div_sub` read through
`TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn`: failure of the logarithm
puts `a` and `b` in different components of `Kᶜ`, and of two such points at most one can lie in the
unbounded component of a bounded set's complement.

It is the form in which an obstruction to a logarithm delivers the enclosure hypothesis of
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt`. -/
theorem mem_filledHull_or_mem_filledHull_of_not_hasContinuousLogOn (hK : IsClosed K)
    (hKb : Bornology.IsBounded K)
    (h : ¬ HasContinuousLogOn (fun z => (z - a) / (z - b)) K) :
    a ∈ filledHull K ∨ b ∈ filledHull K :=
  mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn
    (by rw [Complex.rank_real_complex]; norm_num) hKb fun hb =>
      h (hasContinuousLogOn_sub_div_sub hK hb)

end TauCeti

end
