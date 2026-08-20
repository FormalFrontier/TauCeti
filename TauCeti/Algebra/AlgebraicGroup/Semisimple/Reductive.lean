/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable

/-!
# Semisimple affine groups are reductive

Every smooth connected normal unipotent closed subgroup of a semisimple affine group has solvable
geometric points. It is therefore trivial by semisimplicity, which is precisely the defining
normal-subgroup condition for reductivity.

## Main declaration

* `TauCeti.semisimpleCommHopfAlgProperty.reductive`: every semisimple finite-type commutative Hopf
  algebra is reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 21.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

This is a structural implication in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every semisimple finite-type affine group over a field is reductive. -/
theorem reductive (hH : semisimpleCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H := by
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨hH.smooth, hH.geometricallyConnected, ?_⟩
  intro I hnormal hconnected hunipotent
  rw [smoothUnipotentCommHopfAlgProperty_iff] at hunipotent
  apply hH.eq_augmentation I hnormal hconnected hunipotent.1
  apply geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact hunipotent.2

end semisimpleCommHopfAlgProperty

end

end TauCeti
