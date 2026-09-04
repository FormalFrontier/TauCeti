/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Maps determined by their value on a primitive root

In a domain the `n`-th roots of unity are exactly the powers of a primitive one, so a ring
endomorphism is pinned down on all of them by its value on a single primitive `n`-th root: if it
raises that root to the `j`-th power, it raises every `n`-th root of unity to the `j`-th power.

The same principle characterises when the cyclotomic character `IsPrimitiveRoot.autToPow` is
trivial: it kills an automorphism exactly when that automorphism fixes the chosen primitive root,
because the character records nothing but the power the root is sent to.

## Main results

* `TauCeti.IsPrimitiveRoot.map_eq_pow`: a ring endomorphism sending a primitive `n`-th root of
  unity `ζ` to `ζ ^ j` sends every `n`-th root of unity `μ` to `μ ^ j`.
* `IsPrimitiveRoot.autToPow_eq_one_iff`: the cyclotomic character kills an automorphism exactly
  when it fixes the chosen primitive root.

## References

The characterisation of the cyclotomic character's kernel by its value on a chosen primitive root
is due to the Birkbeck--Brasca Chebotarev density project,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0).
-/

public section

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A ring homomorphism that raises one primitive `n`-th root of unity to the `j`-th power raises
every `n`-th root of unity to the `j`-th power, since the `n`-th roots of unity are exactly the
powers of a primitive one. -/
theorem IsPrimitiveRoot.map_eq_pow {n j : ℕ} [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (σ : R →+* R) (hσ : σ ζ = ζ ^ j) {μ : R} (hμ : μ ^ n = 1) : σ μ = μ ^ j := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm]

end TauCeti

/-- **The cyclotomic character detects fixing `ζ`.** `autToPow` sends `x` to `1` exactly when `x`
fixes the chosen primitive root, since `autToPow` is defined by the power `x` sends it to. -/
@[simp]
theorem _root_.IsPrimitiveRoot.autToPow_eq_one_iff {K M : Type*} [CommRing K] [CommRing M]
    [IsDomain M] [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (x : M ≃ₐ[K] M) : hζ.autToPow K x = 1 ↔ x ζ = ζ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) with hm | hm
  · -- `m = 1` forces `ζ = 1`, and `(ZMod 1)ˣ` is trivial, so both sides always hold
    have hζ1 : ζ = 1 := by simpa [← hm] using hζ.pow_eq_one
    have : Subsingleton (ZMod m)ˣ := by rw [← hm]; infer_instance
    exact ⟨fun _ ↦ by simp [hζ1], fun _ ↦ Subsingleton.elim _ _⟩
  · have : Fact (1 < m) := ⟨hm⟩
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h, Units.val_one, ZMod.val_one, pow_one] at hspec
      exact hspec.symm
    · have hspec := hζ.autToPow_spec (R := K) x
      rw [h] at hspec
      have hval : (hζ.autToPow K x : ZMod m).val = 1 :=
        hζ.pow_inj (ZMod.val_lt _) hm (by rw [hspec, pow_one])
      exact Units.ext (ZMod.val_injective m (by rw [hval, Units.val_one, ZMod.val_one]))
