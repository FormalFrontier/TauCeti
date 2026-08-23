/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Prime

/-!
# Hecke operators `T_n` on modular forms

For a positive integer `n`, the classical Hecke operator `T_n` at level `Γ₁(N)` is the slash
operator attached to the double coset

`Γ₁(N) · diag(1, n) · Γ₁(N)`.

The double coset and its slash operator already exist as `diagCosetGamma1 N n` and
`heckeSlashGamma1ModularFormEnd`; this file packages their composite under the uniform name
`heckeT_n`. The cusp-form operator `heckeT_n_cusp` uses the same double coset, so preservation of
cuspidality is inherited from the general slash construction rather than reproved.

The computation rules identify `T_p` at a prime with the single good-and-bad-prime formula from
`HeckeSlash/Prime.lean`. When `p ∣ N`, they identify it with the upper-triangular operator, the
operator modern sources call `U_p`. Thus the normalization is fixed by the abstract double coset
before the multiplicativity and prime-power recurrences are developed.

## Main definitions

* `HeckeRing.GL2.heckeT_n`: `T_n` on `M_k(Γ₁(N))`.
* `HeckeRing.GL2.heckeT_n_cusp`: `T_n` on `S_k(Γ₁(N))`.

## Main results

* `HeckeRing.GL2.coe_heckeT_n`, `HeckeRing.GL2.coe_heckeT_n_cusp`: the underlying slash sums.
* `HeckeRing.GL2.heckeT_n_one`, `HeckeRing.GL2.heckeT_n_cusp_one`: `T₁` is the identity.
* `HeckeRing.GL2.coe_heckeT_n_prime`, `HeckeRing.GL2.coe_heckeT_n_cusp_prime`: the classical
  formula for `T_p` at every prime.
* `HeckeRing.GL2.heckeT_n_eq_upperTri`, `HeckeRing.GL2.heckeT_n_cusp_eq_upperTri`: at a prime
  dividing the level, `T_p` is the upper-triangular operator.

## Provenance

The definition follows `heckeT_n` in the AINTLIB `LeanModularForms` project
(`HeckeRIngs/GL2/HeckeT_n.lean`, Chris Birkbeck, Apache-2.0, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`). That source assembles prime-power operators first;
here the already-constructed double-coset action gives the equivalent canonical definition
directly. No proof code is transcribed.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.2.1--5.2.2 and §5.3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- **The Hecke operator `T_n` on `M_k(Γ₁(N))`.** It is the slash operator of the canonical
double coset `Γ₁(N) · diag(1, n) · Γ₁(N)`.

The `NeZero n` binder records the classical convention that Hecke operators are indexed by
positive integers, and it is not optional: at `n = 0` the entry tuple `![1, 0]` fails the
positivity side condition of `natDiagGL`, which then returns its junk value `1`, so the double
coset degenerates to `Γ₁(N)` itself and the construction would silently be the identity operator
rather than `T₀`. The binder is `_`-named because only the *statements* below use it — the body
is the same slash operator either way, and it is the index that is being constrained. -/
noncomputable def heckeT_n (n : ℕ) [_hn : NeZero n] :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N n)

/-- **The Hecke operator `T_n` on `S_k(Γ₁(N))`.** This is the cusp-form operator attached to
the same double coset as `heckeT_n`; in particular, it records that `T_n` preserves
cuspidality. The index is nonzero for the reason explained on `heckeT_n`. -/
noncomputable def heckeT_n_cusp (n : ℕ) [_hn : NeZero n] :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N n)

/-- On underlying functions, `T_n` is the slash sum of its defining double coset. -/
@[simp] lemma coe_heckeT_n (n : ℕ) [NeZero n]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeT_n (N := N) k n f) = heckeSlashSum k (diagCosetGamma1 N n) f := by
  unfold heckeT_n
  rw [coe_heckeSlashGamma1ModularFormEnd]

/-- On underlying functions, the cusp-form `T_n` is the same slash sum. -/
@[simp] lemma coe_heckeT_n_cusp (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeT_n_cusp (N := N) k n f) = heckeSlashSum k (diagCosetGamma1 N n) f := by
  unfold heckeT_n_cusp
  rw [coe_heckeSlashGamma1CuspFormEnd]

/-- **The classical `T_p` formula on modular forms, at every prime.** -/
theorem coe_heckeT_n_prime (hp : p.Prime)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeT_n (N := N) k p (_hn := ⟨hp.ne_zero⟩) f) =
      heckeSlashUpperTri k p ⇑f + ⇑(diamondOpNat k p f) ∣[k] scaleRep p := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  unfold heckeT_n
  rw [coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp]

/-- **The classical `T_p` formula on cusp forms, at every prime.** -/
theorem coe_heckeT_n_cusp_prime (hp : p.Prime)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeT_n_cusp (N := N) k p (_hn := ⟨hp.ne_zero⟩) f) =
      heckeSlashUpperTri k p ⇑f + ⇑(diamondOpCuspNat k p f) ∣[k] scaleRep p := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  unfold heckeT_n_cusp
  rw [coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp]

/-- At a positive index dividing the level, `T_p` is the upper-triangular operator. This is the
operator modern sources denote by `U_p`. -/
theorem heckeT_n_eq_upperTri (hpN : p ∣ N) :
    heckeT_n (N := N) k p
      (_hn := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩) =
      heckeSlashUpperTriModularFormEnd k hpN := by
  let _ : NeZero p := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩
  unfold heckeT_n
  rw [heckeSlashGamma1ModularFormEnd_diagCosetGamma1 k hpN]

/-- At a positive index dividing the level, the cusp-form `T_p` is the upper-triangular
operator. -/
theorem heckeT_n_cusp_eq_upperTri (hpN : p ∣ N) :
    heckeT_n_cusp (N := N) k p
      (_hn := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩) =
      heckeSlashUpperTriCuspFormEnd k hpN := by
  let _ : NeZero p := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩
  unfold heckeT_n_cusp
  rw [heckeSlashGamma1CuspFormEnd_diagCosetGamma1 k hpN]

/-- The first Hecke operator on modular forms is the identity. -/
@[simp] theorem heckeT_n_one : heckeT_n (N := N) k 1 = 1 := by
  rw [heckeT_n_eq_upperTri k (one_dvd N)]
  ext f τ
  simp

/-- The first Hecke operator on cusp forms is the identity. -/
@[simp] theorem heckeT_n_cusp_one : heckeT_n_cusp (N := N) k 1 = 1 := by
  rw [heckeT_n_cusp_eq_upperTri k (one_dvd N)]
  ext f τ
  simp

end HeckeRing.GL2

end
