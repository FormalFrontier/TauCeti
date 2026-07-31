/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction

public section

/-!
# The determinant form preserved by the special linear group

This file applies the determinant transformation law to matrices of determinant one, giving the
invariant alternating form required for the standard representation of `SL(n, k)`.

## Main results

* `TauCeti.detRowAlternating_stdSLRep` states the invariance of the determinant form under the
  standard representation of the special linear group.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 0, “The subgroups and the extra invariants”.
-/

namespace TauCeti

open _root_.Matrix

universe u

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The standard action of `SL(n, k)` preserves the standard-basis determinant form.

This is deliberately not a `simp` lemma: `stdSLRep_apply` already rewrites `stdSLRep k n g` to
`Matrix.mulVecLin ↑g`, so the left-hand side here is not in `simp` normal form and the rewrite
could never fire. Use `TauCeti.Matrix.detRowAlternating_mulVec` for the `simp`-normal statement. -/
theorem detRowAlternating_stdSLRep (g : Matrix.SpecialLinearGroup (Fin n) k)
    (v : Fin n → Fin n → k) :
    Matrix.detRowAlternating (fun i => stdSLRep k n g (v i)) =
      Matrix.detRowAlternating v := by
  simpa only [stdSLRep_apply_apply, g.det_coe, one_mul] using
    Matrix.detRowAlternating_mulVec k (ι := Fin n) (g : Matrix (Fin n) (Fin n) k) v

end CommRing

end TauCeti
