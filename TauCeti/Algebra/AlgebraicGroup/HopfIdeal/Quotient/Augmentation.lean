/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# The quotient by the augmentation ideal

A Hopf ideal in the coordinate Hopf algebra of an affine group cuts out a closed subgroup, and
the augmentation ideal cuts out the identity subgroup. This file records the corresponding
identification of coordinate rings: the quotient of a finite-type commutative Hopf algebra by
its augmentation ideal is the base field, which is the coordinate ring of the trivial affine
group.

The identification is the first isomorphism theorem for Hopf ideals. The augmentation ideal is
by definition the kernel Hopf ideal of the counit, and the counit is surjective because the unit
splits it, so the kernel quotient equivalence applies verbatim.

## Main declaration

* `TauCeti.HopfIdeal.quotientAugmentationIso`: the quotient by the augmentation ideal is the
  trivial finite-type Hopf algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), around Proposition 4.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- The quotient by the augmentation ideal is the trivial finite-type Hopf algebra. -/
def quotientAugmentationIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.quotient H (augmentation k H) ≅
      FiniteTypeCommHopfAlgCat.of k k := by
  rw [augmentation_def]
  exact ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    kerLiftBialgEquiv (Bialgebra.counitBialgHom k H) Bialgebra.counit_surjective

/-- The quotient map followed by the quotient-augmentation isomorphism is the counit. -/
@[simp]
theorem mkQuotient_comp_quotientAugmentationIso_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.mkQuotient H (augmentation k H) ≫
        (quotientAugmentationIso H).hom =
      FiniteTypeCommHopfAlgCat.ofHom (Bialgebra.counitBialgHom k H) := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  ext

end HopfIdeal

end

end TauCeti
