/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange

/-!
# Base change and adjoint semisimple affine groups

An adjoint semisimple affine group has trivial scheme-theoretic center. Formation of the center
commutes with extension of the ground field, and field extensions are faithfully flat, so
adjointness is unchanged by scalar extension whenever the base-changed group is supplied with
its semisimple structure.

The semisimplicity hypothesis on the base-changed object is explicit. Its construction is a
separate structure theorem: this file proves that no further argument about the center is needed
once that hypothesis is available. The result concerns the full center scheme, not only its
points over either field.

## Main declaration

* `TauCeti.adjointSemisimpleCommHopfAlgProperty.baseChange_iff`: adjointness of a semisimple
  affine group is equivalent to adjointness after a field extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k and 21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This supplies the scalar-extension compatibility needed for adjoint forms in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. It is the center-theoretic
input to comparing adjoint forms and their root data over an algebraic closure.
-/

public section

namespace TauCeti

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

namespace adjointSemisimpleCommHopfAlgProperty

/-- Adjointness is preserved and reflected by a field extension.

The proof that the base-changed finite-type Hopf algebra is semisimple is kept as an explicit
hypothesis, since preservation of semisimplicity is logically separate from the center
calculation. -/
theorem baseChange_iff
    (H : SemisimpleCommHopfAlgCat.{u} k)
    (hsemisimple : semisimpleCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H.obj)) :
    adjointSemisimpleCommHopfAlgProperty K
        ⟨FiniteTypeCommHopfAlgCat.baseChange (K := K) H.obj, hsemisimple⟩ ↔
      adjointSemisimpleCommHopfAlgProperty k H := by
  rw [adjointSemisimpleCommHopfAlgProperty_iff,
    adjointSemisimpleCommHopfAlgProperty_iff]
  exact CommHopfAlgCat.centerDefiningIdeal_baseChange_eq_augmentation_iff H.obj.obj

end adjointSemisimpleCommHopfAlgProperty

end

end TauCeti
