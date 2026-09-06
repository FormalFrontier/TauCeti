/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Dimension

/-!
# Existence of Borel subgroups

A Borel subgroup of an affine algebraic group over an algebraically closed field is a maximal
smooth, geometrically connected, geometrically solvable closed subgroup. This file proves existence
by maximizing Lie dimension. More precisely, every Borel candidate is contained in a maximal one.
Applying this on the geometric fibre of a group over an arbitrary field constructs a Borel subgroup
there.

The identity subgroup makes the family of candidates nonempty. For the relative statement, a
candidate containing a prescribed one is again a nonempty family. Lie dimensions of closed
subgroups are bounded by the ambient Lie dimension, and equality of Lie dimensions detects
equality for an inclusion of smooth connected closed subgroups. This is exactly the general
maximal-dimension argument in `HopfIdeal.exists_minimal_of_smooth_of_connected`.

The resulting Borel lives over the algebraic closure. It need not descend to the original field:
the existence of a Borel defined over a non-algebraically-closed field is an additional condition
on the group. No conjugacy statement is proved here.

## Main declarations

* `TauCeti.HopfIdeal.exists_minimal_isBorelCandidate_le`: every Borel candidate is contained in
  a maximal Borel candidate.
* `TauCeti.HopfIdeal.exists_minimal_isBorelCandidate`: every finite-type affine group over a
  field has a maximal Borel candidate.
* `TauCeti.HopfIdeal.exists_geometricBorel`: the geometric fibre of every finite-type affine
  group has a Borel subgroup.
* `TauCeti.HopfIdeal.torusCommHopfAlgProperty.isBorelCandidate`: every torus is a Borel candidate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.6 and §17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* T. A. Springer, *Linear Algebraic Groups*, §6.2.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- A solvable-radical candidate is in particular a Borel candidate after forgetting normality. -/
theorem IsSolvableRadicalCandidate.isBorelCandidate
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : IsSolvableRadicalCandidate H I) : IsBorelCandidate k H I :=
  IsBorelCandidate.mk
    ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
    hI.geometricallyConnected hI.geometricallySolvable

/-- The identity subgroup is a Borel candidate. -/
theorem isBorelCandidate_augmentation (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsBorelCandidate k H (augmentation k H) :=
  (isSolvableRadicalCandidate_augmentation H).isBorelCandidate

/-- **Every smooth, geometrically connected, geometrically solvable closed subgroup is contained
in a maximal one.**

In Hopf-ideal order the inequality `J ≤ I` says that the closed subgroup cut out by `J` contains
the one cut out by `I`. Thus the returned minimal Borel candidate is a maximal smooth,
geometrically connected, geometrically solvable subgroup containing the prescribed candidate. -/
theorem exists_minimal_isBorelCandidate_le
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {I : HopfIdeal k H}
    (hI : IsBorelCandidate k H I) :
    ∃ J : HopfIdeal k H, J ≤ I ∧ Minimal (IsBorelCandidate k H) J := by
  obtain ⟨J, ⟨⟨hJ, hJI⟩, hJmin⟩⟩ :=
    exists_minimal_of_smooth_of_connected
      (fun J : HopfIdeal k H ↦ IsBorelCandidate k H J ∧ J ≤ I)
      (fun hJ ↦ hJ.1.smooth)
      (fun hJ ↦ geometricallyConnectedCommHopfAlgProperty.connectedSpace k _
        hJ.1.geometricallyConnected)
      ⟨I, hI, le_rfl⟩
  refine ⟨J, hJI, hJ, fun K hK hKJ ↦ ?_⟩
  exact hJmin ⟨hK, hKJ.trans hJI⟩ hKJ

/-- **Every finite-type affine group over a field has a maximal smooth geometrically connected
geometrically solvable closed subgroup.**

Over an algebraically closed field this is a Borel subgroup. Over a general field it is only
maximal among candidates defined over that field; `exists_geometricBorel` below applies the result
after extension to an algebraic closure. -/
theorem exists_minimal_isBorelCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ∃ I : HopfIdeal k H, Minimal (IsBorelCandidate k H) I := by
  obtain ⟨I, _, hI⟩ := exists_minimal_isBorelCandidate_le H
    (isBorelCandidate_augmentation H)
  exact ⟨I, hI⟩

/-- **The geometric fibre of every finite-type affine group has a Borel subgroup.**

The conclusion is stated directly on the base-changed coordinate Hopf algebra. Since the base
field there is algebraically closed, `IsBorelOverAlgClosed` is precisely minimality among smooth,
geometrically connected, geometrically solvable closed subgroups. -/
theorem exists_geometricBorel (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
    ∃ I : HopfIdeal K H', IsBorelOverAlgClosed K H' I := by
  obtain ⟨I, hI⟩ := exists_minimal_isBorelCandidate
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
  exact ⟨I, (isBorelOverAlgClosed_iff _ _ _).mpr ⟨inferInstance, hI⟩⟩

/-- Every torus closed subgroup is a Borel candidate. -/
theorem torusCommHopfAlgProperty.isBorelCandidate
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    IsBorelCandidate k H I := by
  let _ : Coalgebra.IsCocomm k (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
    hI.isCocomm k (FiniteTypeCommHopfAlgCat.quotient H I)
  exact IsBorelCandidate.mk hI.smooth hI.geometricallyConnected
    (geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)

end HopfIdeal

end

end TauCeti
