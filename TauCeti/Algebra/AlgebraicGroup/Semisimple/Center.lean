/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic

/-!
# Central closed subgroups of semisimple affine groups

Let `H` be the coordinate Hopf algebra of a semisimple affine group over a field `k`. This file
proves that every smooth geometrically connected central closed subgroup of the geometric fibre
is trivial.

A central Hopf ideal is normal, and its quotient coordinate Hopf algebra is cocommutative.
Consequently the represented subgroup has a commutative, hence solvable, group of geometric
points. The defining universal property of semisimplicity then identifies its defining ideal with
the augmentation ideal.

The theorem deliberately retains smoothness. In positive characteristic a semisimple group can
have a non-smooth connected central subgroup scheme, such as an infinitesimal subgroup of its
centre, so removing that hypothesis would be false. The result is the central-subgroup input for
the finite-centre and adjoint-form steps: once a smooth connected central subgroup has been
constructed, no separate solvability argument is needed to show that it is trivial.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.eq_augmentation_of_isCentral`: every smooth
  geometrically connected central closed subgroup of a semisimple group's geometric fibre is
  trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.10 and 21.15.
* T. A. Springer, *Linear Algebraic Groups*, §8.1.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap. It is
the central-subgroup triviality step used in proving that the centre of a semisimple group is
finite and in constructing its adjoint form.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A smooth geometrically connected central closed subgroup of a semisimple affine group's
geometric fibre is trivial.**

The Hopf ideal `I` cuts out the subgroup contravariantly. Thus triviality is the equality of `I`
with the augmentation ideal. Centrality supplies both normality and cocommutativity of the
quotient; the latter makes its geometric point group commutative and therefore solvable. -/
theorem eq_augmentation_of_isCentral
    (hH : semisimpleCommHopfAlgProperty k H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    (hI : I.IsCentral)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj)
    (hsmooth : Algebra.Smooth (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I)) :
    I = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  apply hH.eq_augmentation I hI.isNormal hconnected hsmooth
  let _ : Coalgebra.IsCocomm (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) :=
    hI.isCocomm_quotient
  exact geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm
    (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj

end semisimpleCommHopfAlgProperty

end


end TauCeti
