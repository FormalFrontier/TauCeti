/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# The augmentation Hopf ideal

The augmentation ideal of a Hopf algebra is the kernel of its counit. The counit is split
by the unit, hence surjective, so the kernel Hopf ideal machinery of
`TauCeti.Algebra.HopfAlgebra.Kernel` applies directly and no Sweedler-decomposition
argument is needed.

This is the fundamental example of a Hopf ideal: the quotient by it is the base ring, and
its image under a morphism into a commutative Hopf algebra cuts out the kernel of the
induced morphism of affine group schemes (`TauCeti.CommHopfAlgCat.kernelHopfIdeal`).

## Main declarations

* `TauCeti.HopfIdeal.augmentation`: the augmentation ideal as a Hopf ideal.
* `TauCeti.HopfIdeal.mem_augmentation` and `TauCeti.HopfIdeal.augmentation_toIdeal`:
  characteristic API.

## References

Waterhouse, *Introduction to Affine Group Schemes*, §2.1; Milne, *Algebraic Groups*,
around Proposition 4.1, where the augmentation ideal cuts out the identity section.
-/

public section

namespace TauCeti

namespace HopfIdeal

universe u v

variable (R : Type u) (H : Type v) [CommRing R] [Ring H] [HopfAlgebra R H]

/-- The augmentation Hopf ideal of a Hopf algebra: the kernel of the counit, which is
surjective since the unit splits it (`Bialgebra.counit_surjective`).

The ring hypotheses come from the kernel Hopf ideal construction, whose coideal condition
uses tensor-kernel exactness. -/
noncomputable def augmentation : HopfIdeal R H :=
  ker (Bialgebra.counitBialgHom R H) Bialgebra.counit_surjective

/-- `augmentation` is the kernel Hopf ideal of the counit. -/
theorem augmentation_def :
    augmentation R H = ker (Bialgebra.counitBialgHom R H) Bialgebra.counit_surjective := by
  -- `augmentation` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ker (Bialgebra.counitBialgHom R H) Bialgebra.counit_surjective = _
  rfl

/-- Membership in the augmentation ideal is vanishing of the counit. -/
@[simp]
theorem mem_augmentation {x : H} :
    x ∈ augmentation R H ↔ Coalgebra.counit (R := R) x = 0 :=
  mem_ker _ _

/-- The underlying ideal of the augmentation Hopf ideal is the kernel of the counit
algebra homomorphism. -/
@[simp]
theorem augmentation_toIdeal :
    (augmentation R H).toIdeal = RingHom.ker (Bialgebra.counitAlgHom R H) := by
  ext x
  rw [mem_toIdeal, mem_augmentation, RingHom.mem_ker]
  exact Iff.rfl

end HopfIdeal

end TauCeti
