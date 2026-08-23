/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Powers of a subring scalar acting on a submodule

Let `S` be a subring of a commutative ring `A`, `M` an `A`-module and `M₀` an `S`-submodule of
`M`. This file collects the elementary facts about the family `rⁿ • M₀`, for `r : S`, in
Mathlib's pointwise action on submodules.

The family is written out as `rⁿ • M₀` rather than wrapped in a definition of its own:
`Submodule.mem_smul_pointwise_iff_exists` already characterises membership and
`Submodule.smul_le_self_of_tower` already gives the shrinking, so a wrapper would only oblige
this file to restate both.

## Main results

* `Submodule.pow_smul_mem_pow_smul`: the ambient-scalar bridge — an element of `M₀` scaled by
  `sⁿ : A` lands in `⟨s, _⟩ⁿ • M₀`, so a consumer speaking `A` needs no coercion plumbing.
* `Submodule.pow_smul_antitone`: the family is antitone in the exponent.
* `Submodule.pow_add_smul_mem`: `M₀` absorbs further powers of a scalar drawn from `S`.
-/

public section

open scoped Pointwise

namespace Submodule

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- **The ambient-scalar bridge.** Membership in `rⁿ • M₀` is stated in Mathlib's terms with the
subring scalar `r : S`, while a caller typically holds the ambient `s : A`. This is the crossing,
so the coercion plumbing is done once here.

Only this direction holds: the converse would need multiplication by `sⁿ` to be injective.

Not `@[simp]`: the left-hand side is already reducible by
`Submodule.mem_smul_pointwise_iff_exists`, so simp would rather rewrite it than close it, and the
simpNF linter says so. This is a bridge to apply, not a normalisation. -/
theorem pow_smul_mem_pow_smul {S : Subring A} (M₀ : Submodule S M) {s : A} (hs0 : s ∈ S) {y : M}
    (hy : y ∈ M₀) (n : ℕ) : s ^ n • y ∈ (⟨s, hs0⟩ : S) ^ n • M₀ :=
  Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr
    ⟨y, hy, by rw [Subring.smul_def]; push_cast; rfl⟩

/-- **The family `rⁿ • M₀` is antitone in `n`.** Raising the exponent multiplies by a further
`r`, and `Submodule.smul_le_self_of_tower` says that shrinks the submodule. -/
theorem pow_smul_antitone {S : Subring A} (M₀ : Submodule S M) {r : S} :
    Antitone fun n : ℕ ↦ r ^ n • M₀ := by
  intro i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  calc r ^ (i + d) • M₀ = r ^ i • (r ^ d • M₀) := by rw [pow_add, mul_smul]
    _ ≤ r ^ i • M₀ := smul_mono_right _ (M₀.smul_le_self_of_tower _)

/-- **A submodule over a subring absorbs further powers of a scalar from that subring**: raising
the exponent cannot leave `M₀`, because the extra factor is itself a scalar from `S`. -/
theorem pow_add_smul_mem {S : Subring A} (M₀ : Submodule S M) {s : A} (hs0 : s ∈ S)
    (j k : ℕ) (z : M) (hz : s ^ k • z ∈ M₀) : s ^ (j + k) • z ∈ M₀ := by
  have he : s ^ (j + k) • z = (⟨s, hs0⟩ : S) ^ j • (s ^ k • z) := by
    rw [Subring.smul_def, ← smul_assoc, smul_eq_mul]
    congr 1
    push_cast
    rw [pow_add]
  rw [he]; exact M₀.smul_mem _ hz

/-- **Scaling into `sⁿ • M₀`.** If `c` factors as `s ^ (n + k) • b` with `b : S`, and `s ^ k • m`
already lies in `M₀`, then `c • m` lies in `sⁿ • M₀`.

This is the step that both a submodules-basis `smul` condition and a module-filter-basis
`smul_right'` axiom reduce to, which is why it is stated once here rather than inline at each. -/
theorem smul_mem_pow_smul {S : Subring A} (M₀ : Submodule S M) {s : A} (hs0 : s ∈ S) {b : A}
    (hb : b ∈ S) {c : A} {m : M} {n k : ℕ} (hcb : s ^ (n + k) • b = c)
    (hk : s ^ k • m ∈ M₀) : c • m ∈ (⟨s, hs0⟩ : S) ^ n • M₀ := by
  have hmem : (⟨b, hb⟩ : S) • (s ^ k • m) ∈ M₀ := M₀.smul_mem _ hk
  have he : c • m = ((⟨s, hs0⟩ : S) ^ n) • ((⟨b, hb⟩ : S) • (s ^ k • m)) := by
    have hscal : ((⟨s, hs0⟩ : S) ^ n • (⟨b, hb⟩ : S)) • (s ^ k) = c := by
      simp only [Subring.smul_def, smul_eq_mul]
      push_cast
      rw [← hcb, smul_eq_mul, pow_add]
      exact mul_right_comm _ _ _
    rw [← smul_assoc, ← smul_assoc, hscal]
  rw [he]
  exact Submodule.smul_mem_pointwise_smul _ _ _ hmem

end Submodule
