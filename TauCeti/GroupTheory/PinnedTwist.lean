/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Maps that permute a pinned family and raise its parameters

A Steinberg endomorphism of a pinned algebraic group is pinned down by a single equation on the
numbered simple root subgroups: it sends the `i`-th subgroup to the `σ i`-th one and raises the
parameter to a power,

```text
τ (x i t) = x (σ i) (t ^ q i).
```

This file studies that equation, `TauCeti.IsPinnedTwist x σ q τ`, on its own. Nothing is assumed
about the family `x`, the type it lands in, or the map `τ`: the whole content is how the data
`(σ, q)` behaves under composition and iteration, so the results are available before any pinned
group has been constructed.

The three Steinberg maps of the classification are three shapes of this equation. A field Frobenius
has `σ = 1` and constant `q`; a graph automorphism has `q = 1`; and a half-Frobenius has `σ` an
involution exchanging long and short nodes, with `q i * q (σ i)` the defining characteristic on
every node. The last is the case the main results are about: they compute the odd powers
`τ^[2 * m + 1]` of such a map, which is what the Suzuki and Ree constructions take, and record that
the square of that odd power raises every parameter to the `p ^ (2 * m + 1)`-th power.

## Main definitions

* `TauCeti.IsPinnedTwist`: the equation `τ (x i t) = x (σ i) (t ^ q i)` on a pinned family.

## Main results

* `TauCeti.IsPinnedTwist.comp` and `TauCeti.IsPinnedTwist.iterate`: composing multiplies the
  permutations and, along the orbit of `σ`, the exponents.
* `TauCeti.IsPinnedTwist.sq`: if `σ` is an involution and `q i * q (σ i) = p` for every `i`, then
  `τ^[2]` fixes every index and raises every parameter to the `p`-th power.
* `TauCeti.IsPinnedTwist.iterate_two_mul` and `TauCeti.IsPinnedTwist.iterate_two_mul_add_one`:
  under those hypotheses the even power `τ^[2 * m]` raises every parameter to the `p ^ m`-th power,
  and the odd power `τ^[2 * m + 1]` permutes by `σ` and raises the `i`-th parameter to the
  `p ^ m * q i`-th power.

## References

This is the general form of the odd-power step of milestone L2 of
`TauCetiRoadmap/CFSGStatement/README.md`, which defines the Suzuki--Ree Steinberg map as
`steinberg m = τ_X ^ (2 * m + 1)` for a special isogeny `τ_X` acting on the numbered simple root
subgroups by the displayed equation. The construction is standard; see R. W. Carter, *Simple Groups
of Lie Type*, and *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
<https://arxiv.org/abs/2108.06291>, for the formulation `τ ^ 2 = Frob_p`.
-/

public section

namespace TauCeti

variable {G R ι : Type*} [Monoid R]

/-- `IsPinnedTwist x σ q τ` says that the map `τ` carries the family `x` into itself, moving the
index `i` to `σ i` and raising the parameter to the `q i`-th power:

```text
τ (x i t) = x (σ i) (t ^ q i).
```

The intended reading is that `x` is a pinned family of root subgroup maps, `σ` a permutation of the
numbered simple roots, and `q` the exponent the map attaches to each of them. -/
def IsPinnedTwist (x : ι → R → G) (σ : Equiv.Perm ι) (q : ι → ℕ) (τ : G → G) : Prop :=
  ∀ (i : ι) (t : R), τ (x i t) = x (σ i) (t ^ q i)

namespace IsPinnedTwist

variable {x : ι → R → G} {σ σ' : Equiv.Perm ι} {q q' : ι → ℕ} {τ τ' : G → G} {p : ℕ}

theorem apply (h : IsPinnedTwist x σ q τ) (i : ι) (t : R) : τ (x i t) = x (σ i) (t ^ q i) :=
  h i t

/-- Replacing the permutation and the exponents of a pinned twist by equal ones. -/
theorem copy (h : IsPinnedTwist x σ q τ) (hσ : σ' = σ) (hq : ∀ i, q' i = q i) :
    IsPinnedTwist x σ' q' τ := by
  intro i t
  rw [hσ, hq i]
  exact h i t

/-- Composing two pinned twists composes their permutations and multiplies their exponents, the
second exponent being read at the index the first twist moved to. -/
theorem comp (h : IsPinnedTwist x σ q τ) (h' : IsPinnedTwist x σ' q' τ') :
    IsPinnedTwist x (σ' * σ) (fun i => q i * q' (σ i)) (τ' ∘ τ) := by
  intro i t
  rw [Function.comp_apply, h i t, h' (σ i) (t ^ q i), ← pow_mul, Equiv.Perm.mul_apply]

/-- The `k`-th iterate of a pinned twist moves an index `k` steps along the `σ`-orbit and raises
the parameter to the product of the exponents met on the way. -/
theorem iterate (h : IsPinnedTwist x σ q τ) (k : ℕ) :
    IsPinnedTwist x (σ ^ k) (fun i => ∏ j ∈ Finset.range k, q ((σ ^ j) i)) τ^[k] := by
  induction k with
  | zero => intro i t; simp
  | succ k ih =>
      rw [Function.iterate_succ]
      refine (h.comp ih).copy (pow_succ σ k) fun i => ?_
      -- Peel the first factor off the product; the remaining ones are read at `σ i` instead of
      -- at `i`, which is one step of the orbit.
      rw [Finset.prod_range_succ', pow_zero, Equiv.Perm.one_apply, mul_comm]
      exact congrArg (fun s => q i * s)
        (Finset.prod_congr rfl fun j _ => by rw [pow_succ, Equiv.Perm.mul_apply])

section Involutive

variable (hσ : ∀ i, σ (σ i) = i) (hq : ∀ i, q i * q (σ i) = p)
include hσ hq

/-- The square of a pinned twist whose permutation is an involution and whose exponents multiply to
`p` along that involution fixes every index and raises every parameter to the `p`-th power.

This is the relation `τ ^ 2 = Frob_p` characteristic of a half-Frobenius, read off the pinned
family alone: it is a consequence of the exponent convention rather than a further hypothesis. -/
theorem sq (h : IsPinnedTwist x σ q τ) : IsPinnedTwist x 1 (fun _ => p) τ^[2] := by
  intro i t
  rw [Function.iterate_succ_apply, Function.iterate_one, h i t, h (σ i) (t ^ q i), ← pow_mul,
    hq i, hσ i, Equiv.Perm.one_apply]

/-- An even power of such a pinned twist fixes every index and raises every parameter to the
`p ^ m`-th power. -/
theorem iterate_two_mul (h : IsPinnedTwist x σ q τ) (m : ℕ) :
    IsPinnedTwist x 1 (fun _ => p ^ m) τ^[2 * m] := by
  have key := (h.sq hσ hq).iterate m
  rw [← Function.iterate_mul] at key
  exact key.copy (one_pow m).symm fun _ => by simp

/-- An odd power of such a pinned twist permutes the indices by `σ` and raises the `i`-th parameter
to the `p ^ m * q i`-th power.

This is the Suzuki--Ree Steinberg map `τ ^ (2 * m + 1)`, whose exponents therefore still multiply
to `p ^ (2 * m + 1)` along `σ`. -/
theorem iterate_two_mul_add_one (h : IsPinnedTwist x σ q τ) (m : ℕ) :
    IsPinnedTwist x σ (fun i => p ^ m * q i) τ^[2 * m + 1] := by
  have key := h.comp (h.iterate_two_mul hσ hq m)
  rw [← Function.iterate_succ] at key
  exact key.copy (one_mul σ).symm fun i => mul_comm _ _

end Involutive

end IsPinnedTwist

end TauCeti
