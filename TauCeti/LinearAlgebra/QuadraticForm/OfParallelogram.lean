/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A function satisfying the parallelogram law is a quadratic form

Let `M` and `N` be additive commutative groups and `f : M → N` satisfy the **parallelogram law**

```
f (x + y) + f (x - y) = 2 • f x + 2 • f y.
```

Then `f` is a quadratic form: its polarisation `QuadraticMap.polar f x y = f (x + y) - f x - f y`
is biadditive, and `f (n • x) = n ^ 2 • f x`. This file proves that, and packages it as a
`QuadraticMap ℤ M N`. Both `f 0 = 0` and evenness of `f` come free from the law rather than being
assumed.

Mathlib has the converse direction — `QuadraticMap.polar_add_left` and friends read biadditivity
*off* a `QuadraticMap`, and `LinearMap.BilinMap.toQuadraticMap` builds one from a bilinear map —
but nothing in the other direction from the parallelogram law alone. Its `parallelogram_law` and
`parallelogram_law_with_norm` are statements about inner product spaces, and the Jordan–von Neumann
construction in `Analysis/InnerProductSpace/OfNorm.lean` recovers an inner product from a *norm* on
a real or complex space, using continuity. Neither applies to a function on a bare abelian group.

## The hypothesis is exactly the absence of `2`-torsion

`htwo : IsSMulRegular N 2` says that doubling is injective on `N`. It is sharp in both directions.

It is *not* `IsAddTorsionFree N`, which is strictly stronger and excludes codomains where the
conclusion holds: `IsSMulRegular (ZMod 3) 2` is true even though `ZMod 3` has `3`-torsion.

Nor can it be weakened away. With `M = N = ZMod 2` *every* function satisfies the parallelogram
law, because `x - y = x + y` and `2 • z = 0` there; the constant function `1` is then one that
satisfies it while failing even `f 0 = 0`, which every quadratic form obeys — and correspondingly
`¬ IsSMulRegular (ZMod 2) 2`.

For a torsion-free codomain it is one term: `smul_right_injective N two_ne_zero` supplies it for
`N = ℝ`, the canonical height's target, and for `N = ℤ`, the degree form's.

## Main results

* `TauCeti.QuadraticMap.map_zero_of_parallelogram`: `f 0 = 0`.
* `TauCeti.QuadraticMap.map_neg_of_parallelogram`: `f (-x) = f x`.
* `TauCeti.QuadraticMap.map_add_add_add_map_of_parallelogram`: the three-variable identity
  `f (x + y + z) + (f x + f y + f z) = f (x + y) + f (y + z) + f (z + x)`, stated exactly as
  `QuadraticMap.map_add_add_add_map`.
* `TauCeti.QuadraticMap.polar_add_left_of_parallelogram` and
  `polar_zsmul_left_of_parallelogram`: the polarisation is additive and `ℤ`-linear on the left.
* `TauCeti.QuadraticMap.map_zsmul_of_parallelogram`: `f (n • x) = n ^ 2 • f x` for `n : ℤ`.
* `TauCeti.QuadraticMap.ofParallelogram`: `f` as a `QuadraticMap ℤ M N`, with the polarisation as
  its companion bilinear map.

## Where this is used

Two constructions in arithmetic geometry arrive at a function *known to satisfy the parallelogram
law* and want it as a quadratic form.

The canonical height of an elliptic curve is one. It satisfies the parallelogram law exactly, and
its polarisation is the Néron–Tate height pairing **up to a factor of two**: by
`QuadraticMap.polar_self` the polarisation here has `polar f x x = 2 • f x`, whereas the pairing
whose Gram determinant on a basis of the free part of the Mordell–Weil group is the regulator is
normalised so that `⟨P, P⟩` is the height itself. A consumer wanting the regulator convention
halves this one; the choice is not made here, since halving is not available in a general abelian
group.

The degree form on `End E` is the other: its polarisation is the trace form, and non-negativity of
the degree gives the Hasse bound by Cauchy–Schwarz (Silverman, *The Arithmetic of Elliptic
Curves*, V.1.2).

Both take values in a torsion-free group — `ℝ` and `ℤ` respectively — so both satisfy the
hypothesis below with room to spare. Stated for a general abelian group so that neither carries
its own copy.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {f : M → N}
  (htwo : IsSMulRegular N (2 : ℕ))
  (hf : ∀ x y : M, f (x + y) + f (x - y) = 2 • f x + 2 • f y)

include htwo hf

-- The parallelogram law at `x = y = 0`.
/-- **A parallelogram-law function preserves zero.** -/
theorem map_zero_of_parallelogram : f 0 = 0 := by
  have h := hf 0 0
  simp only [add_zero, sub_zero] at h
  apply htwo
  linear_combination (norm := module) -h

-- The parallelogram law at `x = 0`.
/-- **A parallelogram-law function is even.** -/
theorem map_neg_of_parallelogram (x : M) : f (-x) = f x := by
  have h := hf 0 x
  rw [zero_add, zero_sub, map_zero_of_parallelogram htwo hf] at h
  linear_combination (norm := module) h

-- This is the substantive step: biadditivity of the polarisation below is a rearrangement of it.
-- Stated exactly as `QuadraticMap.map_add_add_add_map`, the same identity read off a quadratic
-- map instead of derived from the parallelogram law — `f (z + x)` included, which is what lets
-- `polar_add_left_iff.mpr` consume it with no reshaping at the use site.
/-- **The three-variable identity** satisfied by every quadratic form, in subtraction-free form. -/
theorem map_add_add_add_map_of_parallelogram (x y z : M) :
    f (x + y + z) + (f x + f y + f z) = f (x + y) + f (y + z) + f (z + x) := by
  -- `f (z + x)` is the goal's spelling but `f (x + z)` is what the instances below produce, and
  -- commutativity inside an argument of an opaque `f` is invisible to `abel`, `module` and
  -- `linear_combination`; pay for it once here rather than at every use site.
  rw [show z + x = x + z from by abel]
  -- Four instances of the law. `x + z - y` and `x - (y - z)` are the same point, which is what
  -- lets the two occurrences of `f` at that point cancel; halving at the end is the only place
  -- torsion-freeness is used.
  have p1 := hf (x + y) z
  have p2 := hf x (y - z)
  have p3 := hf y z
  have p4 := hf (x + z) y
  -- `f` is an arbitrary function, so `abel` cannot normalise *under* it: the arguments have to be
  -- rewritten explicitly before the four instances share syntactic subterms and can be combined.
  rw [show x + y - z = x + (y - z) by abel] at p1
  rw [show x - (y - z) = x + z - y by abel] at p2
  rw [show x + z + y = x + y + z by abel] at p4
  apply htwo
  linear_combination (norm := module) p1 + p4 - p2 - (2 : ℤ) • p3

-- Exactly how Mathlib proves `QuadraticMap.polar_add_left` from `map_add_add_add_map`.
/-- **The polarisation is additive in its left argument.** -/
theorem polar_add_left_of_parallelogram (x x' y : M) :
    polar f (x + x') y = polar f x y + polar f x' y :=
  polar_add_left_iff.mpr <| map_add_add_add_map_of_parallelogram htwo hf x x' y

-- No new content: an additive map between abelian groups is automatically `ℤ`-linear, so this is
-- `polar_add_left_of_parallelogram` transported. It is the last input `QuadraticMap.ofPolar` asks
-- for. Additivity on the *right* is not stated separately — it is `QuadraticMap.polar_add_right`
-- of the packaged `ofParallelogram` below.
/-- **The polarisation is `ℤ`-linear in its left argument.** -/
theorem polar_zsmul_left_of_parallelogram (a : ℤ) (x y : M) :
    polar f (a • x) y = a • polar f x y :=
  AddMonoidHom.map_zsmul
    (AddMonoidHom.mk' (polar f · y) fun p q ↦ polar_add_left_of_parallelogram htwo hf p q y) a x

-- The scalar on the right is an **integer** so that the induction step is a `ring` identity in
-- `ℤ`; over `ℕ` it would read `(n + 2) ^ 2 = 2 (n + 1) ^ 2 + 2 - n ^ 2`, and truncated
-- subtraction is not a ring.
/-- Quadraticity for a natural multiple: `f (n • x) = n ^ 2 • f x`. -/
private theorem map_nsmul_of_parallelogram (n : ℕ) (x : M) :
    f (n • x) = ((n : ℤ) * n) • f x := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using map_zero_of_parallelogram htwo hf
  | one => simp
  | more n ih ih' =>
    -- the parallelogram law at `((n + 1) • x, x)` expresses the value at `(n + 2) • x`
    have h := hf ((n + 1) • x) x
    -- again the arguments of `f`, not the ambient expression, are what must be reshaped
    rw [← succ_nsmul x (n + 1), show (n + 1) • x - x = n • x by
      rw [succ_nsmul, add_sub_cancel_right], ih, ih'] at h
    push_cast at h ⊢
    linear_combination (norm := module) h

-- Written `(n * n) • f x` rather than `n ^ 2 • f x` to match the `toFun_smul` field of
-- `QuadraticMap` syntactically. The negative case composes the natural one with evenness.
/-- **Quadraticity**: `f (n • x) = n ^ 2 • f x` for an integer `n`. -/
theorem map_zsmul_of_parallelogram (n : ℤ) (x : M) : f (n • x) = (n * n) • f x := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul, map_nsmul_of_parallelogram htwo hf]
  · rw [neg_zsmul, natCast_zsmul, map_neg_of_parallelogram htwo hf,
      map_nsmul_of_parallelogram htwo hf, neg_mul_neg]

-- Built with `QuadraticMap.ofPolar`, which asks for exactly the three facts above and assembles
-- the companion bilinear map itself, so no bilinear map is defined here.
/-- **A function satisfying the parallelogram law is a quadratic form.** Its companion bilinear
map is `QuadraticMap.polarBilin` of it, which is the polarisation. -/
def ofParallelogram : _root_.QuadraticMap ℤ M N :=
  .ofPolar f (map_zsmul_of_parallelogram htwo hf) (polar_add_left_of_parallelogram htwo hf)
    (polar_zsmul_left_of_parallelogram htwo hf)

-- Stated at the level of functions rather than only pointwise because `QuadraticMap.polar` takes
-- the function as its argument: this is the form that rewrites `polar ⇑(ofParallelogram htwo hf)`
-- into `polar f` and so reaches Mathlib's polar API.
/-- `ofParallelogram` coerces back to the function it was built from. -/
@[simp]
theorem coe_ofParallelogram : (ofParallelogram htwo hf : M → N) = f := by
  funext x
  simp [ofParallelogram]

/-- `ofParallelogram` evaluated at a point is the original function there. -/
@[simp]
theorem ofParallelogram_apply (x : M) : ofParallelogram htwo hf x = f x := by
  simp

end QuadraticMap

end TauCeti
