/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Approximating a lower semicontinuous function from below

On a pseudometric space, an `ℝ≥0∞`-valued lower semicontinuous function is the pointwise supremum
of an increasing sequence of bounded Lipschitz functions. This file builds that sequence
explicitly, as the truncated inf-convolution

`lscApproxAux f n x = ⨅ y, ((f y ⊓ n).toReal + n * dist x y)`,

and packages it as a sequence in `Ω →ᵇ ℝ≥0`.

Monotone approximation from below by *bounded continuous* functions is what turns the monotone
convergence theorem into a lower semicontinuity statement for integrals against a varying measure,
which is why the target of the approximation is `Ω →ᵇ ℝ≥0` rather than merely a continuous
function: the weak topology on measures is defined by pairing with exactly these test functions.

## Main declarations

* `TauCeti.lscApproxAux`: the truncated inf-convolution, a real-valued function bounded by `n` and
  Lipschitz with constant `n`.
* `TauCeti.iSup_ofReal_lscApproxAux`: for lower semicontinuous `f`, the approximations increase
  pointwise to `f`.
* `TauCeti.lscApprox`: the same sequence bundled as bounded continuous `ℝ≥0`-valued functions.
* `TauCeti.LowerSemicontinuous.exists_boundedContinuous_monotone_iSup_eq`: the resulting
  interface, stating only that some monotone sequence of bounded continuous functions has
  pointwise supremum `f`.

## Implementation notes

The inf-convolution is taken of the truncation `f ⊓ n` rather than of `f` itself, so that the
`n`-th approximation is bounded by `n`; truncating is what allows infinite values of `f` to be
reached in the limit. The infimum is formed in `ℝ` (rather than in `ℝ≥0∞`) because the Lipschitz
estimate is then Mathlib's `LipschitzWith.of_le_add_mul`, and because bounded continuous functions
are the intended target. The construction is the one used for `LipschitzOnWith.extend_real`.
-/

public section

open Metric Set
open scoped BoundedContinuousFunction ENNReal NNReal

namespace TauCeti

variable {Ω : Type*} [PseudoMetricSpace Ω] {f : Ω → ℝ≥0∞} {n : ℕ} {x : Ω}

/-- The `n`-th truncated inf-convolution of `f : Ω → ℝ≥0∞` on a pseudometric space: the infimum
over `y` of `(f y ⊓ n).toReal + n * dist x y`. It is nonnegative, bounded by `n`, Lipschitz with
constant `n`, increasing in `n`, and, when `f` is lower semicontinuous, increases pointwise to
`f`. -/
noncomputable def lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : ℝ :=
  ⨅ y : Ω, ((f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y)

/-- The family whose infimum defines `TauCeti.lscApproxAux` is bounded below by `0`. -/
theorem bddBelow_range_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    BddBelow (range fun y : Ω ↦ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact add_nonneg ENNReal.toReal_nonneg (by positivity)

/-- The defining upper bound for `TauCeti.lscApproxAux`, one for each competitor `y`. -/
theorem lscApproxAux_le_add (f : Ω → ℝ≥0∞) (n : ℕ) (x y : Ω) :
    lscApproxAux f n x ≤ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y :=
  ciInf_le (bddBelow_range_lscApproxAux f n x) y

/-- A lower bound valid for every competitor `y` is a lower bound for
`TauCeti.lscApproxAux`. -/
theorem le_lscApproxAux {a : ℝ} (h : ∀ y, a ≤ (f y ⊓ (n : ℝ≥0∞)).toReal + n * dist x y) :
    a ≤ lscApproxAux f n x :=
  have : Nonempty Ω := ⟨x⟩
  le_ciInf h

/-- The approximations are nonnegative. -/
theorem lscApproxAux_nonneg (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : 0 ≤ lscApproxAux f n x :=
  le_lscApproxAux fun _ ↦ add_nonneg ENNReal.toReal_nonneg (by positivity)

/-- Taking `y = x` in the defining infimum bounds the approximation by the truncation of `f`
at `x`. -/
theorem lscApproxAux_le_toReal_inf (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    lscApproxAux f n x ≤ (f x ⊓ (n : ℝ≥0∞)).toReal := by
  simpa using lscApproxAux_le_add f n x x

/-- The `n`-th approximation is bounded by `n`. -/
theorem lscApproxAux_le_natCast (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) : lscApproxAux f n x ≤ n := by
  refine (lscApproxAux_le_toReal_inf f n x).trans ?_
  have h : (f x ⊓ (n : ℝ≥0∞)).toReal ≤ ((n : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top n) inf_le_right
  simpa using h

/-- Every approximation lies below `f`. -/
theorem ofReal_lscApproxAux_le (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    ENNReal.ofReal (lscApproxAux f n x) ≤ f x := by
  refine (ENNReal.ofReal_le_ofReal (lscApproxAux_le_toReal_inf f n x)).trans ?_
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right)]
  exact inf_le_left

/-- The `n`-th approximation is Lipschitz with constant `n`. -/
theorem lipschitzWith_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (lscApproxAux f n) := by
  refine LipschitzWith.of_le_add_mul _ fun x y ↦ ?_
  rw [← sub_le_iff_le_add]
  refine le_lscApproxAux fun z ↦ ?_
  rw [sub_le_iff_le_add]
  calc lscApproxAux f n x ≤ (f z ⊓ (n : ℝ≥0∞)).toReal + n * dist x z := lscApproxAux_le_add f n x z
    _ ≤ (f z ⊓ (n : ℝ≥0∞)).toReal + n * dist y z + (n : ℝ≥0) * dist x y := by
        push_cast
        rw [add_assoc, ← mul_add, add_comm (dist y z)]
        gcongr
        exact dist_triangle x y z

/-- The approximations are continuous. -/
theorem continuous_lscApproxAux (f : Ω → ℝ≥0∞) (n : ℕ) : Continuous (lscApproxAux f n) :=
  (lipschitzWith_lscApproxAux f n).continuous

/-- The approximations increase with `n`, both the truncation level and the Lipschitz constant
growing. -/
theorem monotone_lscApproxAux (f : Ω → ℝ≥0∞) (x : Ω) : Monotone fun n : ℕ ↦ lscApproxAux f n x := by
  refine monotone_nat_of_le_succ fun n ↦ le_lscApproxAux fun y ↦ ?_
  refine (lscApproxAux_le_add f n x y).trans ?_
  have h₁ : (f y ⊓ (n : ℝ≥0∞)).toReal ≤ (f y ⊓ ((n + 1 : ℕ) : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.natCast_ne_top (n + 1)) inf_le_right)
      (inf_le_inf_left _ (Nat.cast_le.2 (Nat.le_succ n)))
  have h₂ : (n : ℝ) * dist x y ≤ ((n + 1 : ℕ) : ℝ) * dist x y :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ n)) dist_nonneg
  linarith

/-- The truncated inf-convolutions of a lower semicontinuous `f : Ω → ℝ≥0∞` increase pointwise
to `f`. -/
theorem iSup_ofReal_lscApproxAux (hf : LowerSemicontinuous f) (x : Ω) :
    ⨆ n : ℕ, ENNReal.ofReal (lscApproxAux f n x) = f x := by
  refine le_antisymm (iSup_le fun n ↦ ofReal_lscApproxAux_le f n x) (le_of_forall_lt fun a ha ↦ ?_)
  obtain ⟨b, hab, hbf⟩ := exists_between ha
  refine hab.trans_le ?_
  -- `b` is a strict lower bound for `f` on a ball around `x`, and `b ≠ ∞`.
  have hb : b ≠ ∞ := (hbf.trans_le le_top).ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hf x b hbf)
  obtain ⟨n, hn⟩ := exists_nat_ge (max b.toReal (b.toReal / ε))
  have hnb : b.toReal ≤ n := (le_max_left _ _).trans hn
  have hne : b.toReal ≤ n * ε := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hn)
  have hbn : b ≤ (n : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal hnb
    rwa [ENNReal.ofReal_toReal hb, ENNReal.ofReal_natCast] at h
  have key : b.toReal ≤ lscApproxAux f n x := by
    refine le_lscApproxAux fun y ↦ ?_
    rcases lt_or_ge (dist x y) ε with hy | hy
    · have hby : b ≤ f y ⊓ (n : ℝ≥0∞) := le_inf (hball (by rwa [dist_comm])).le hbn
      have hne_top : f y ⊓ (n : ℝ≥0∞) ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right
      have h := ENNReal.toReal_mono hne_top hby
      have hd : (0 : ℝ) ≤ n * dist x y := by positivity
      linarith
    · have hεd : (n : ℝ) * ε ≤ n * dist x y :=
        mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg n)
      linarith [ENNReal.toReal_nonneg (a := f y ⊓ (n : ℝ≥0∞))]
  calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb).symm
    _ ≤ ENNReal.ofReal (lscApproxAux f n x) := ENNReal.ofReal_le_ofReal key
    _ ≤ ⨆ n : ℕ, ENNReal.ofReal (lscApproxAux f n x) :=
        le_iSup (fun n : ℕ ↦ ENNReal.ofReal (lscApproxAux f n x)) n

/-- The truncated inf-convolution of `f : Ω → ℝ≥0∞`, bundled as a bounded continuous
`ℝ≥0`-valued function. -/
@[expose] noncomputable def lscApprox (f : Ω → ℝ≥0∞) (n : ℕ) : Ω →ᵇ ℝ≥0 where
  toFun x := (lscApproxAux f n x).toNNReal
  continuous_toFun := continuous_real_toNNReal.comp (continuous_lscApproxAux f n)
  map_bounded' := by
    refine ⟨n, fun x y ↦ ?_⟩
    rw [NNReal.dist_eq, Real.coe_toNNReal _ (lscApproxAux_nonneg f n x),
      Real.coe_toNNReal _ (lscApproxAux_nonneg f n y), abs_sub_le_iff]
    constructor <;>
      linarith [lscApproxAux_nonneg f n x, lscApproxAux_nonneg f n y, lscApproxAux_le_natCast f n x,
        lscApproxAux_le_natCast f n y]

/-- The value of the bundled approximation, as a nonnegative real. -/
@[simp]
theorem lscApprox_apply (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    lscApprox f n x = (lscApproxAux f n x).toNNReal :=
  rfl

/-- The value of the bundled approximation, as an element of `ℝ≥0∞`. -/
theorem coe_lscApprox_apply (f : Ω → ℝ≥0∞) (n : ℕ) (x : Ω) :
    (lscApprox f n x : ℝ≥0∞) = ENNReal.ofReal (lscApproxAux f n x) :=
  rfl

/-- The bundled approximations increase pointwise with `n`. -/
theorem monotone_coe_lscApprox (f : Ω → ℝ≥0∞) :
    Monotone fun n : ℕ ↦ fun x ↦ ((lscApprox f n x : ℝ≥0) : ℝ≥0∞) := fun m n hmn x ↦ by
  simpa only [coe_lscApprox_apply] using
    ENNReal.ofReal_le_ofReal (monotone_lscApproxAux f x hmn)

/-- The bundled approximations of a lower semicontinuous `f` increase pointwise to `f`. -/
theorem iSup_coe_lscApprox (hf : LowerSemicontinuous f) (x : Ω) :
    ⨆ n : ℕ, ((lscApprox f n x : ℝ≥0) : ℝ≥0∞) = f x := by
  simpa only [coe_lscApprox_apply] using iSup_ofReal_lscApproxAux hf x

/-- On a pseudometric space, a lower semicontinuous `f : Ω → ℝ≥0∞` is the pointwise supremum of
an increasing sequence of bounded continuous `ℝ≥0`-valued functions. -/
theorem LowerSemicontinuous.exists_boundedContinuous_monotone_iSup_eq (hf : LowerSemicontinuous f) :
    ∃ g : ℕ → (Ω →ᵇ ℝ≥0), (Monotone fun n ↦ fun x ↦ ((g n x : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ x, ⨆ n, ((g n x : ℝ≥0) : ℝ≥0∞) = f x :=
  ⟨lscApprox f, monotone_coe_lscApprox f, iSup_coe_lscApprox hf⟩

end TauCeti
