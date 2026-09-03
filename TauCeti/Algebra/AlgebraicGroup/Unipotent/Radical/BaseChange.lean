/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Base change of the unipotent radical

Let `H` be a finite-type commutative Hopf algebra over a field `k`. Extension to a field `K`
sends every connected normal smooth unipotent closed subgroup of the affine group represented by
`H` to another such subgroup. In particular, the base change of the unipotent radical is contained
in the unipotent radical formed after base change.

In coordinate rings, closed-subgroup containment reverses the order on defining ideals, so the
conclusion is

```text
  unipotentRadicalDefiningIdeal (K ⊗[k] H) ≤
    baseChangeHopfIdeal (unipotentRadicalDefiningIdeal H).
```

Normality and geometric connectedness survive base change directly. The quotient by a
base-changed ideal is identified with the base change of the original quotient, where smooth
geometric unipotence follows from the universal coefficient-matrix argument.

Equality requires descent of an arbitrary radical candidate over `K` and is not asserted here.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.baseChange`: scalar extension preserves
  unipotent-radical candidates.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_le`: the
  base-changed unipotent radical is contained in the radical after base change.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This advances scalar-extension compatibility for the unipotent radical in Layer 5 of the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Base change of a unipotent-radical candidate is again a unipotent-radical candidate. -/
theorem baseChange (hI : IsUnipotentRadicalCandidate H I) :
    IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine IsUnipotentRadicalCandidate.mk
    (CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI.isNormal) ?_ ?_
  · apply (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso.symm
    exact geometricallyConnectedCommHopfAlgProperty.baseChange k K _ hI.geometricallyConnected
  · have hbase := smoothUnipotentCommHopfAlgProperty.baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient H I) hI.smoothUnipotent
    exact (smoothUnipotentCommHopfAlgProperty K).prop_of_iso
      (CategoryTheory.ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K) qIso.symm) hbase

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The unipotent radical after base change contains the base change of the original unipotent
radical.

The displayed inequality is between defining Hopf ideals, hence has the opposite direction from
the corresponding inclusion of represented closed subgroups. -/
theorem unipotentRadicalDefiningIdeal_baseChange_le
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) ≤
      CommHopfAlgCat.baseChangeHopfIdeal (K := K)
        (unipotentRadicalDefiningIdeal H) :=
  unipotentRadicalDefiningIdeal_le _ _
    (HopfIdeal.IsUnipotentRadicalCandidate.baseChange
      (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H))

end FiniteTypeCommHopfAlgCat

end

end TauCeti
