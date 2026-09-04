/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Adjoin
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The automorphisms fixing the roots of unity

The `K`-automorphisms of `M` fixing `K(μ_m)` pointwise are exactly the kernel of the cyclotomic
character `IsPrimitiveRoot.autToPow`. No Galois, normality or separability hypothesis is needed —
only that `M` contains a primitive `m`-th root of unity — although when `M / K` is Galois this
subgroup is `Gal(M/K(μ_m))`, which is the reading the crossing argument uses.

## Main results

* `IsPrimitiveRoot.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow`

## References

The identification of `Gal(M/K(μ_m))` with the `G × 1` factor of a Galois splitting is due to the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0).
-/

public section

open IntermediateField

/-- **The fixers of `K(μ_m)` are the kernel of the cyclotomic character.**

Use it to move between a condition on `Gal(M/K(μ_m))` and one on the cyclotomic character, which
is the form a Galois splitting presents. -/
theorem IsPrimitiveRoot.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow
    {K M : Type*} [Field K] [Field M] [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = (hζ.autToPow K).ker := by
  ext x
  -- `K(μ_m) = K(ζ)`, so fixing the whole root-of-unity set is fixing the single generator.
  rw [MonoidHom.mem_ker, hζ.autToPow_eq_one_iff, ← hζ.adjoin_singleton_eq_adjoin_nth_roots,
    IntermediateField.mem_fixingSubgroup_iff]
  simp only [← AlgEquiv.smul_def]
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp [AlgEquiv.smul_def]
