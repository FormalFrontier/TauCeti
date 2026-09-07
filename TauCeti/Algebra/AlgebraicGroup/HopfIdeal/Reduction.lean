/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction

/-!
# The reduced quotient of an affine group

This file packages the quotient by the generic nilradical Hopf ideal from
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction` as a commutative Hopf-algebra object and records
that its underlying coordinate ring is reduced.

## Main declarations

* `TauCeti.HopfIdeal.isReduced_quotient_reduction`: the resulting quotient is reduced.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), §1.f.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v

variable (R : Type u) [CommRing R] [IsReduced R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

/-- The quotient by the reduction Hopf ideal has reduced coordinate ring. -/
theorem isReduced_quotient_reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (reduction R H)) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, reduction_toIdeal]
  exact Ideal.radical_isRadical ⊥

end TauCeti.HopfIdeal
