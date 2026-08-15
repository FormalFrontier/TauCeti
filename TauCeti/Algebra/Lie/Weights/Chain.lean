/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.Chain

public section

/-!
# Bounds on weight-space chains

This file records two bounds for weight spaces along an integral line. In a Noetherian module,
only finitely many weights occur, so sufficiently far in either direction the corresponding
generalized weight spaces vanish.

## Main results

* `TauCeti.exists_lt_genWeightSpace_zsmul_add_eq_bot`: sufficiently far forward along a nonzero
  direction, the generalized weight space vanishes.
* `TauCeti.exists_genWeightSpace_zsmul_add_eq_bot_lt`: the corresponding backward bound.
-/

namespace TauCeti

open LieModule

universe u v w

variable {R : Type u} {L : Type v} {M : Type w} [CommRing R] [IsDomain R] [IsAddTorsionFree R]
  [LieRing L] [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [Module.IsTorsionFree R M] [IsNoetherian R M]

variable (M) in
/-- Far enough along a nonzero direction `a`, the weight spaces `M_{k • a + χ}` vanish: a
Noetherian module has only finitely many weights. -/
theorem exists_lt_genWeightSpace_zsmul_add_eq_bot {a : L → R} (ha : a ≠ 0) (χ : L → R) (b : ℤ) :
    ∃ q : ℤ, b < q ∧ genWeightSpace M (q • a + χ) = ⊥ := by
  obtain ⟨n, hn₁, hn₂⟩ :=
    ((Filter.eventually_gt_atTop b.toNat).and
      (eventually_genWeightSpace_smul_add_eq_bot M a χ ha)).exists
  exact ⟨(n : ℤ), lt_of_le_of_lt (Int.self_le_toNat b) (by exact_mod_cast hn₁),
    by rwa [natCast_zsmul]⟩

variable (M) in
/-- The mirror of `TauCeti.exists_lt_genWeightSpace_zsmul_add_eq_bot`: the weight spaces
`M_{k • a + χ}` also vanish far enough back along `a`. -/
theorem exists_genWeightSpace_zsmul_add_eq_bot_lt {a : L → R} (ha : a ≠ 0) (χ : L → R) (b : ℤ) :
    ∃ p : ℤ, p < b ∧ genWeightSpace M (p • a + χ) = ⊥ := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_lt_genWeightSpace_zsmul_add_eq_bot M (a := -a) (neg_ne_zero.2 ha) χ (-b)
  exact ⟨-q, by omega, by rwa [neg_smul, ← smul_neg]⟩

end TauCeti
