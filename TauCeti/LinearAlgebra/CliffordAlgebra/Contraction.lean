/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Contraction against the `ℤ/2`-grading

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance as the operator
by which an anisotropic vector orthogonal to a polarization acts on a spinor module.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so the statement is `contractLeft d ⁻¹` of `evenOdd Q (i + 1)` rather than of `evenOdd Q
(i - 1)`; the two are literally equal.

## Main results

* `TauCeti.CliffordAlgebra.map_contractLeft_evenOdd_le` and
  `TauCeti.CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**, in
  submodule and in membership form.
* `TauCeti.CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti.CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- Contracting a product of at most `n` generators lands in the parity opposite to `n`. This is
the graded statement on a single power of `range (ι Q)`; `map_contractLeft_evenOdd_le` assembles
the powers into the two halves of the grading. -/
private theorem contractLeft_mem_evenOdd_pow (d : Module.Dual R M) {n : ℕ}
    {x : CliffordAlgebra Q} (hx : x ∈ LinearMap.range (ι Q) ^ n) :
    contractLeft d x ∈ evenOdd Q ((n : ZMod 2) + 1) := by
  have hpow : ∀ (m : ℕ) (y : CliffordAlgebra Q), y ∈ LinearMap.range (ι Q) ^ m →
      y ∈ evenOdd Q (m : ZMod 2) := fun m y hy =>
    Submodule.mem_iSup_of_mem (⟨m, rfl⟩ : {k : ℕ // (k : ZMod 2) = (m : ZMod 2)}) hy
  have hsucc : ∀ c : ZMod 2, c + 1 + 1 = c := by decide
  have hmul : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    -- In `ZMod 2` the index of the successor step collapses back to the index of `x`.
    have hind : ((i.succ : ℕ) : ZMod 2) + 1 = ((i : ℕ) : ZMod 2) := by
      push_cast; exact hsucc _
    rw [contractLeft_ι_mul, hind]
    refine sub_mem (Submodule.smul_mem _ _ (hpow i x hx)) ?_
    simpa only [hmul] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q a) ih

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem map_contractLeft_evenOdd_le (d : Module.Dual R M) (i : ZMod 2) :
    (evenOdd Q i).map (contractLeft d) ≤ evenOdd Q (i + 1) := by
  rw [evenOdd, Submodule.map_iSup]
  refine iSup_le fun n => ?_
  rintro _ ⟨y, hy, rfl⟩
  simpa only [n.2] using contractLeft_mem_evenOdd_pow d hy

/-- **Contraction shifts the parity**, in membership form. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) :=
  map_contractLeft_evenOdd_le d i ⟨x, hx, rfl⟩

end TauCeti.CliffordAlgebra
