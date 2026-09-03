/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Coset

/-!
# The diagonal elements of the `Γ₀(N)` Hecke ring

`Gamma0/Diagonal/Coset.lean` builds the double coset `Γ₀(N)·diag(a)·Γ₀(N)` as a `HeckeCoset`.
This file turns it into an element of the Hecke ring `𝕋 (Δ₀(N)) (Γ₀(N))` — the level-`N`
analogue of `diagElem` — with the coprimality guard applied once so that the vanishing case is
stated in a single place rather than at each generator.

`Coset.lean` holds the coset layer and this file the ring-element layer, so the two of
`Coset.lean`'s three consumers that want only cosets (`Gamma1/UpperTriCosets.lean` and
`UpperTriangularDelta0.lean`) stop there. Keeping the element here rather than in
`PrimePower.lean` means a consumer wanting only the general diagonal element does not import
the prime-power recurrence.

## Main definitions

* `HeckeRing.GL2.diagElemGamma0`: the class of `Γ₀(N)·diag(a)·Γ₀(N)` in the Hecke ring, or `0`
  when the head entry shares a factor with the level or some entry is not positive.

## Main results

* `HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime`, `_of_not_coprime`, `_of_not_pos`: the
  three branches of the definition.
* `HeckeRing.GL2.diagElemGamma0_one`, `_one_one`: the identity normal forms, at the constant
  tuple and at the vector literal `![1, 1]`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The level-`N` diagonal element of the Hecke ring, `0` unless the head entry `a 0` is
coprime to the level.

Inside the coprime branch the value still depends on the tuple, and the three cases are worth
keeping straight:

* `¬ Nat.Coprime (a 0) N` — the element is `0` (`diagElemGamma0_of_not_coprime`);
* some entry not positive — the element is `0` (`diagElemGamma0_of_not_pos`);
* every entry positive and the head coprime to the level — the class of `Γ₀(N)·diag(a)·Γ₀(N)`,
  the intended case.

The coprimality guard is what `Δ₀(N)`-membership needs, and putting it here rather than at each
generator means the vanishing case is stated once. Positivity is guarded alongside it so that
both degenerate branches take the single junk value `0`, matching `heckeTDiag` at level one
(`GL2/Basic.lean`), whose guard is likewise a positivity-and-condition conjunction. This is
the level-`N` analogue of `diagElem`. -/
noncomputable def diagElemGamma0 (a : Fin 2 → ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  if h : (∀ i, 0 < a i) ∧ Nat.Coprime (a 0) N then
    HeckeCosetModule.single ℤ (diagCosetGamma0 N a fun _ ↦ h.2) 1
  else 0

/-- Defining equation in the nondegenerate branch: the element is the class of the double
coset. Both guards are needed — positivity as well as coprimality — since either failing
sends the element to `0`. -/
lemma diagElemGamma0_of_pos_of_coprime {a : Fin 2 → ℕ} (hpos : ∀ i, 0 < a i)
    (h : Nat.Coprime (a 0) N) :
    diagElemGamma0 N a = HeckeCosetModule.single ℤ (diagCosetGamma0 N a fun _ ↦ h) 1 := by
  rw [diagElemGamma0, dite_eq_left_of_eq_true (eq_true ⟨hpos, h⟩)]

/-- The diagonal element vanishes when the head entry shares a factor with the level. -/
@[simp]
theorem diagElemGamma0_of_not_coprime {a : Fin 2 → ℕ} (h : ¬ Nat.Coprime (a 0) N) :
    diagElemGamma0 N a = 0 := by
  rw [diagElemGamma0, dite_eq_right_of_eq_false (eq_false fun hc ↦ h hc.2)]

/-- The diagonal element vanishes when some entry fails to be positive. The underlying
`natDiagGL` would degenerate to the identity matrix there, so the value is a junk convention
rather than a membership fact; `0` is the same convention `heckeTDiag` uses at level one. -/
@[simp]
theorem diagElemGamma0_of_not_pos {a : Fin 2 → ℕ} (ha : ¬ ∀ i, 0 < a i) :
    diagElemGamma0 N a = 0 := by
  rw [diagElemGamma0, dite_eq_right_of_eq_false (eq_false fun hc ↦ ha hc.1)]

/-- **The identity normal form at the all-ones tuple**, mirroring `diagCosetGamma0_one`:
`diag(1, 1)` is the identity matrix, so its class is the ring identity. This is the case both
generators in `Diagonal/PrimePower.lean` reduce to at argument `1`. -/
@[simp] lemma diagElemGamma0_one : diagElemGamma0 N (fun _ ↦ 1) = 1 := by
  rw [diagElemGamma0_of_pos_of_coprime N (fun _ ↦ Nat.one_pos) (Nat.coprime_one_left N),
    diagCosetGamma0_one]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- **The identity at the vector literal `![1, 1]`**: the same fact as `diagElemGamma0_one`, at
the tuple spelling rather than the constant function. The two are equal but not syntactically
so, and `![1, 1]` is the spelling the generators of `Diagonal/PrimePower.lean` reduce to. -/
@[simp] lemma diagElemGamma0_one_one : diagElemGamma0 N ![1, 1] = 1 := by
  have hconst : (![1, 1] : Fin 2 → ℕ) = fun _ ↦ 1 := by
    ext i
    fin_cases i <;> rfl
  rw [hconst]
  exact diagElemGamma0_one N

end HeckeRing.GL2

end
