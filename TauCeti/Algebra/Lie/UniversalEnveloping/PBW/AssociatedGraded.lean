/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AssociatedGraded
public import TauCeti.Algebra.Lie.UniversalEnveloping.Filtration

/-!
# The associated-graded algebra of the PBW filtration

This file specializes the associated-graded construction for a word filtration to the canonical
Lie map into `UniversalEnvelopingAlgebra R L`. Its degree-`k` piece is the quotient of PBW words of
length at most `k` by words of length at most `k - 1`, and multiplication is induced by
multiplication in the enveloping algebra.

The defining enveloping-algebra relation lowers the commutator of two generators from degree two
to degree one. Consequently, its next use is to show that the degree-one leading symbols commute
and hence induce an algebra map from `SymmetricAlgebra R L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.PBWGradedPiece`: the degree-`k` PBW quotient.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGraded`: the direct sum of the PBW quotients.
* `TauCeti.UniversalEnvelopingAlgebra.pbwGradedMul`: multiplication of homogeneous PBW classes.
* `TauCeti.UniversalEnvelopingAlgebra.pbwGradedOne` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwGradedAlgebraMap₀`: the unit and scalar classes in degree
  zero.

## Roadmap

This is the associated-graded-algebra prerequisite for the pinned associated-graded map from
`SymmetricAlgebra R L` in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

open scoped DirectSum

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra.wordFiltration

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ιU" =>
  (LieHom.toLinearMap (_root_.UniversalEnvelopingAlgebra.ι R) : L →ₗ[R] U)

/-- The preceding PBW filtration step, viewed inside the current step. -/
abbrev pbwFiltrationPreviousRestricted (k : ℕ) : Submodule R (pbwFiltration R L k) :=
  previousRestricted ιU k

/-- Membership in the restricted preceding PBW step is ambient membership in the preceding
step. -/
theorem mem_pbwFiltrationPreviousRestricted_iff (k : ℕ) (x : pbwFiltration R L k) :
    x ∈ pbwFiltrationPreviousRestricted R L k ↔
      (x : U) ∈ pbwFiltrationPrevious R L k :=
  mem_previousRestricted_iff ιU k x

/-- The restricted preceding PBW filtration is trivial in degree zero. -/
theorem pbwFiltrationPreviousRestricted_zero :
    pbwFiltrationPreviousRestricted R L 0 = ⊥ :=
  previousRestricted_zero ιU

/-- In successor degree, the restricted preceding PBW filtration is the previous step viewed
inside the current step. -/
theorem pbwFiltrationPreviousRestricted_succ (k : ℕ) :
    pbwFiltrationPreviousRestricted R L (k + 1) =
      Submodule.comap (pbwFiltration R L (k + 1)).subtype (pbwFiltration R L k) :=
  previousRestricted_succ ιU k

/-- The degree-`k` quotient of the PBW filtration by its preceding step. -/
abbrev PBWGradedPiece (k : ℕ) : Type max u v :=
  GradedPiece ιU k

/-- The direct sum of the homogeneous quotients of the PBW filtration. It inherits its ring and
`R`-algebra structures from the generic associated-graded construction. -/
abbrev pbwAssociatedGraded : Type max u v :=
  associatedGraded ιU

/-- Multiplication of two homogeneous PBW filtration quotients. -/
noncomputable abbrev pbwGradedMul (i j : ℕ) :
    PBWGradedPiece (R := R) (L := L) i →ₗ[R]
      PBWGradedPiece (R := R) (L := L) j →ₗ[R]
        PBWGradedPiece (R := R) (L := L) (i + j) :=
  gradedMul ιU i j

/-- On quotient representatives, homogeneous PBW multiplication is induced by multiplication in
the universal enveloping algebra. -/
theorem pbwGradedMul_apply_mk (i j : ℕ) (x : pbwFiltration R L i)
    (y : pbwFiltration R L j) :
    pbwGradedMul R L i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (⟨(x : U) * y, mul_mem_pbwFiltration R L x.property y.property⟩ :
          pbwFiltration R L (i + j)) :=
  gradedMul_apply_mk ιU i j x y

/-- The degree-zero unit class of the PBW associated graded algebra. -/
noncomputable abbrev pbwGradedOne : PBWGradedPiece (R := R) (L := L) 0 :=
  gradedOne ιU

/-- The degree-zero class of a scalar in the PBW associated graded algebra. -/
noncomputable abbrev pbwGradedAlgebraMap₀ :
    R →+ PBWGradedPiece (R := R) (L := L) 0 :=
  gradedAlgebraMap₀ ιU

/-- A scalar class multiplied by a homogeneous PBW class is scalar multiplication. -/
theorem pbwGradedAlgebraMap₀_mul (r : R) (k : ℕ)
    (x : PBWGradedPiece (R := R) (L := L) k) :
    cast (congrArg (PBWGradedPiece (R := R) (L := L)) (Nat.zero_add k))
      (pbwGradedMul (R := R) (L := L) 0 k
        (pbwGradedAlgebraMap₀ (R := R) (L := L) r) x) = r • x :=
  gradedAlgebraMap₀_mul ιU r k x

/-- A homogeneous PBW class multiplied by a scalar class is scalar multiplication. -/
theorem pbwGradedMul_algebraMap₀ (r : R) (k : ℕ)
    (x : PBWGradedPiece (R := R) (L := L) k) :
    pbwGradedMul (R := R) (L := L) k 0 x
      (pbwGradedAlgebraMap₀ (R := R) (L := L) r) = r • x :=
  gradedMul_algebraMap₀ ιU r k x

end TauCeti.UniversalEnvelopingAlgebra
