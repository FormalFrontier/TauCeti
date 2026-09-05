/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Augmentation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Existence of maximal tori

Every finite-type affine group over a field has a maximal torus, and more precisely every torus
closed subgroup is contained in a maximal one. The argument is the standard dimension count: tori
are smooth and connected, so a torus of maximal Lie dimension among those containing a given one
cannot be enlarged.

Two ingredients make the count work. The identity subgroup, cut out by the augmentation ideal, is
the rank-zero split torus, so the family of tori is never empty; for a group with no nontrivial
torus the maximal torus obtained is the identity subgroup. And the Lie dimensions of closed
subgroups are bounded by the Lie dimension of the ambient group, so a maximal-dimensional torus
exists.

No conjugacy statement is proved here: even over an algebraically closed field, conjugacy of
maximal tori is a separate theorem. Likewise, the maximal torus produced is maximal among tori
defined over the ground field, which is a priori weaker than maximality after base change to an
algebraic closure; comparing the two is again a separate theorem.

## Main declarations

* `TauCeti.HopfIdeal.torusCommHopfAlgProperty_quotient_augmentation`: the identity subgroup of a
  finite-type affine group is a torus.
* `TauCeti.HopfIdeal.exists_isMaximalTorus_le`: every torus closed subgroup is contained in a
  maximal torus.
* `TauCeti.HopfIdeal.exists_isMaximalTorus`: every finite-type affine group over a field has a
  maximal torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), §17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.4.
* T. A. Springer, *Linear Algebraic Groups*, §6.3.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k]

namespace HopfIdeal

/-- The identity subgroup of a finite-type affine group is a torus.

Contravariantly, the augmentation ideal cuts out the identity subgroup, and the quotient by it is
the base field, the coordinate ring of the rank-zero split torus. -/
theorem torusCommHopfAlgProperty_quotient_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (augmentation k H)) :=
  splitTorusCommHopfAlgProperty.torus k _
    ((splitTorusCommHopfAlgProperty k).prop_of_iso (quotientAugmentationIso H).symm
      (splitTorusCommHopfAlgProperty_trivial k))

variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **Every torus closed subgroup is contained in a maximal torus.**

Because Hopf ideals reverse inclusion of closed subgroups, the conclusion `J ≤ I` says that the
maximal torus cut out by `J` contains the torus cut out by `I`. -/
theorem exists_isMaximalTorus_le {I : HopfIdeal k H}
    (hI : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    ∃ J : HopfIdeal k H, J ≤ I ∧ IsMaximalTorus k H.obj J := by
  obtain ⟨J, ⟨⟨hJ, hJI⟩, hJmin⟩⟩ :=
    exists_minimal_of_smooth_of_connected
      (fun J : HopfIdeal k H ↦
        torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H J) ∧ J ≤ I)
      (fun ⟨hJ, _⟩ ↦ torusCommHopfAlgProperty.smooth k _ hJ)
      (fun ⟨hJ, _⟩ ↦ geometricallyConnectedCommHopfAlgProperty.connectedSpace k _
        (torusCommHopfAlgProperty.geometricallyConnected k _ hJ))
      ⟨I, hI, le_rfl⟩
  refine ⟨J, hJI, ?_⟩
  exact (isMaximalTorus_iff k H.obj J).mpr
    ⟨hJ, fun K hK hKJ ↦ hJmin ⟨hK, hKJ.trans hJI⟩ hKJ⟩

/-- **Every finite-type affine group over a field has a maximal torus.**

The identity subgroup is a torus, so the previous theorem applies to it. The maximal torus
produced may well be the identity subgroup, for instance for a unipotent group. -/
theorem exists_isMaximalTorus : ∃ J : HopfIdeal k H, IsMaximalTorus k H.obj J :=
  let ⟨J, _, hJ⟩ :=
    exists_isMaximalTorus_le H (torusCommHopfAlgProperty_quotient_augmentation H)
  ⟨J, hJ⟩

end HopfIdeal

end

end TauCeti
