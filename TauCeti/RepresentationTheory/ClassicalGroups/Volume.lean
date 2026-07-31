/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction

public section

/-!
# The determinant form preserved by the special linear group

This file applies the determinant transformation law to matrices of determinant one, giving the
invariant alternating form required for the standard representation of `SL(n, k)`.

The same computation, read on the top exterior power rather than on the determinant form, says
that the volume element `e₁ ∧ ⋯ ∧ eₙ` of `⋀[k]^n (Fin n → k)` is an invariant vector: the top
exterior power of the standard representation of `SL(n, k)` is the trivial one-dimensional
representation. (The volume *form* is the alternating covector `Matrix.detRowAlternating`; the
volume element is the multivector dual to it.)

## Main definitions

* `TauCeti.topExtPowerSLEquivTrivial` identifies the top exterior power of the standard
  representation of the special linear group with the trivial representation.

## Main results

* `TauCeti.detRowAlternating_stdSLRep` states the invariance of the determinant form under the
  standard representation of the special linear group.
* `TauCeti.stdSLRep_exteriorPower_self_apply` says the special linear group acts trivially on the
  top exterior power.

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

/-- The special linear group acts trivially on the top exterior power of the standard
representation: a matrix acts there by its determinant, which is one. -/
theorem stdSLRep_exteriorPower_self_apply (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (stdSLRep k n).exteriorPower n g = LinearMap.id := by
  rw [Representation.exteriorPower_apply, stdSLRep_apply, ← Matrix.toLin'_apply',
    exteriorPower.map_eq_det_smul (Pi.basisFun k (Fin n)), LinearMap.det_toLin', g.det_coe,
    one_smul]

/-- **The volume element is invariant**: the top exterior power of the standard representation of
`SL(n, k)` is the trivial one-dimensional representation. -/
noncomputable def topExtPowerSLEquivTrivial :
    ((stdSLRep k n).exteriorPower n).Equiv
      (Representation.trivial k (Matrix.SpecialLinearGroup (Fin n) k) k) :=
  .mk (exteriorPower.topEquiv (Pi.basisFun k (Fin n))) fun g ↦ by
    rw [stdSLRep_exteriorPower_self_apply]
    simp

/-- The underlying linear equivalence of `TauCeti.topExtPowerSLEquivTrivial` is the top-degree
identification of the exterior power with the scalars. -/
@[simp]
theorem topExtPowerSLEquivTrivial_toLinearEquiv :
    (topExtPowerSLEquivTrivial k n).toLinearEquiv =
      exteriorPower.topEquiv (Pi.basisFun k (Fin n)) :=
  (rfl)

/-- The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
@[simp]
theorem topExtPowerSLEquivTrivial_apply_ιMulti (v : Fin n → (Fin n → k)) :
    topExtPowerSLEquivTrivial k n (exteriorPower.ιMulti k n v) = (Matrix.of v).det := by
  simp [topExtPowerSLEquivTrivial, ← Pi.basisFun_det_apply]

end CommRing

end TauCeti
