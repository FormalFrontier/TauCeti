/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.Basic

/-!
# Finite flatness of the center of the special linear group

For a positive integer `n`, the center of `SLₙ` is the finite diagonalizable group `μₙ`.
The preceding center calculation identifies its coordinate Hopf algebra with the group algebra
`k[Multiplicative (ZMod n)]`. The standard group-algebra basis therefore makes this coordinate
ring finite free of rank `n` over `k`.

This file transports the standard group-algebra basis across
`SpecialLinear.centerCoordinateIsoGroupAlgebra` to the represented center of `SLₙ`. It follows
that the center coordinate ring is finite free and faithfully flat of rank `n`. In particular,
the structure morphism from that center to the trivial group is a central isogeny. This is the
finite-kernel input for the standard central isogeny from `SLₙ` to its adjoint form.

No reducedness or smoothness assertion is made: when the characteristic divides `n`, `μₙ` is
finite flat but nonreduced, exactly as the group-scheme statement requires.

## Main declarations

* `TauCeti.SpecialLinear.moduleFinite_centerCoordinate`: the represented center of `SLₙ` is
  finite over the ground field.
* `TauCeti.SpecialLinear.moduleFaithfullyFlat_centerCoordinate`: it is faithfully flat.
* `TauCeti.SpecialLinear.finrank_centerCoordinate`: its rank is `n`.
* `TauCeti.SpecialLinear.isCentralIsogeny_centerStructureMorphism`: the center's structure
  morphism is a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 2.4 and 5.49, and §21.4.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 3.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap: it
supplies the finite flat center needed for the `SLₙ` central-isogeny and adjoint-form example.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace SpecialLinear

variable {k : Type u} [Field k] (n : ℕ)

-- This is kept private because the public API records the resulting intrinsic module properties.
private noncomputable def centerCoordinateLinearEquiv (hn : 0 < n) :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) ≃ₗ[k]
      MonoidAlgebra k (Multiplicative (ZMod n)) :=
  LinearEquiv.ofBijective
    (centerCoordinateIsoGroupAlgebra n hn).hom.hom.toLinearMap
    (ConcreteCategory.bijective_of_isIso (centerCoordinateIsoGroupAlgebra n hn).hom)

/-- The represented center coordinate algebra of `SLₙ` is a free module over the ground field. -/
theorem moduleFree_centerCoordinate (hn : 0 < n) :
    Module.Free k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) := by
  let _ : Module.Free k (MonoidAlgebra k (Multiplicative (ZMod n))) := by
    infer_instance
  exact Module.Free.of_equiv (centerCoordinateLinearEquiv n hn).symm

/-- The represented center coordinate algebra of `SLₙ` is finite as a module over the ground
field. -/
theorem moduleFinite_centerCoordinate (hn : 0 < n) :
    Module.Finite k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let _ : Module.Finite k (MonoidAlgebra k (Multiplicative (ZMod n))) := by
    infer_instance
  exact Module.Finite.equiv (centerCoordinateLinearEquiv n hn).symm

/-- The represented center coordinate algebra of `SLₙ` is a finite-type algebra over the ground
field. -/
theorem finiteType_centerCoordinate (hn : 0 < n) :
    Algebra.FiniteType k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) := by
  exact (moduleFinite_centerCoordinate n hn).finiteType

/-- The represented center coordinate algebra of `SLₙ` is faithfully flat over the ground
field. -/
theorem moduleFaithfullyFlat_centerCoordinate (hn : 0 < n) :
    Module.FaithfullyFlat k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let _ : Module.FaithfullyFlat k (MonoidAlgebra k (Multiplicative (ZMod n))) := by
    infer_instance
  exact Module.FaithfullyFlat.of_linearEquiv k
    (MonoidAlgebra k (Multiplicative (ZMod n))) (centerCoordinateLinearEquiv n hn)

/-- The represented center coordinate algebra of `SLₙ` has rank `n` over the ground field. -/
theorem finrank_centerCoordinate (hn : 0 < n) :
    Module.finrank k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) = n := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [(centerCoordinateLinearEquiv n hn).finrank_eq,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod n)) k)]
  simp

/-- The structure morphism from the represented center of `SLₙ` to the trivial group is a
central isogeny. The kernel is the center itself, identified with the finite flat group `μₙ`. -/
theorem isCentralIsogeny_centerStructureMorphism (hn : 0 < n) :
    CommHopfAlgCat.IsCentralIsogeny
      (CommHopfAlgCat.ofHom
        (Bialgebra.unitBialgHom k
          (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
            (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))))) := by
  let _ : Module.Finite k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) :=
    moduleFinite_centerCoordinate n hn
  let _ : Module.FaithfullyFlat k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) :=
    moduleFaithfullyFlat_centerCoordinate n hn
  let _ : Coalgebra.IsCocomm k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))) :=
    (CommHopfAlgCat.isCentral_centerDefiningIdeal
      (coordinateHopfAlgebra k n)).isCocomm_quotient
  exact CommHopfAlgCat.isCentralIsogeny_unit_of_isCocomm
    (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)))

end SpecialLinear

end

end TauCeti
