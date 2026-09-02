/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced

/-!
# Base change of the solvable radical

Let `H` be a finite-type commutative Hopf algebra over a field `k`. Extension to a field `K`
sends every connected normal smooth solvable closed subgroup of the affine group represented by
`H` to another such subgroup. In particular, the base change of the solvable radical is contained
in the solvable radical formed after base change.

In coordinate rings, closed-subgroup containment reverses the order on defining ideals, so the
conclusion is

```text
  solvableRadicalDefiningIdeal (K ⊗[k] H) ≤
    baseChangeHopfIdeal (solvableRadicalDefiningIdeal H).
```

The four candidate conditions use their corresponding base-change theorems. The quotient by a
base-changed ideal is identified with the base change of the original quotient by
`CommHopfAlgCat.quotientBaseChangeIso`; finite-type Nullstellensatz makes the universal
derived-word defect nilpotent, so that condition also survives arbitrary field extension.

Equality requires descent of an arbitrary radical candidate over `K` and is not asserted here.

## Main declarations

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.baseChange`: scalar extension preserves
  solvable-radical candidates.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_baseChange_le`: the base-changed
  solvable radical is contained in the radical after base change.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This advances the scalar-extension compatibility of the radical in Layer 6, "Reductive and
semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Base change of a solvable-radical candidate is again a solvable-radical candidate. -/
theorem baseChange (hI : IsSolvableRadicalCandidate H I) :
    IsSolvableRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine IsSolvableRadicalCandidate.mk
    (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI.isNormal) ?_ ?_ ?_
  · apply (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso.symm
    exact geometricallyConnectedCommHopfAlgProperty.baseChange k K _ hI.geometricallyConnected
  · rw [← smoothCommHopfAlgProperty_iff]
    apply (smoothCommHopfAlgProperty K).prop_of_iso qIso.symm
    rw [smoothCommHopfAlgProperty_iff]
    exact @Algebra.Smooth.baseChange k _
      (FiniteTypeCommHopfAlgCat.quotient H I) K _ _ _ _ hI.smooth
  · apply (geometricallySolvablePointsCommHopfAlgProperty K).prop_of_iso qIso.symm
    exact geometricallySolvablePointsCommHopfAlgProperty.baseChange
      (CommHopfAlgCat.quotient H.obj I) hI.geometricallySolvable

end HopfIdeal.IsSolvableRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The solvable radical after base change contains the base change of the original solvable
radical.

The displayed inequality is between defining Hopf ideals, hence has the opposite direction from
the corresponding inclusion of represented closed subgroups. -/
theorem solvableRadicalDefiningIdeal_baseChange_le
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalDefiningIdeal (baseChange (K := K) H) ≤
      CommHopfAlgCat.baseChangeHopfIdeal (K := K)
        (solvableRadicalDefiningIdeal H) :=
  solvableRadicalDefiningIdeal_le _ _
    (HopfIdeal.IsSolvableRadicalCandidate.baseChange
      (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H))

end FiniteTypeCommHopfAlgCat

end

end TauCeti
