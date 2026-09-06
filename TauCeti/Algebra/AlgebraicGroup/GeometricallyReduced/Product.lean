/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product

/-!
# Geometric reducedness of products of affine groups

The coordinate algebra of a direct product of affine groups is the tensor product of their
coordinate algebras. For affine groups of finite type over a field, geometric reducedness is
equivalent to smoothness, and smoothness is preserved by products. It follows that the tensor
product of two geometrically reduced coordinate Hopf algebras of finite type is geometrically
reduced.

Over an algebraically closed field, a reduced affine group of finite type is smooth. Thus the
ordinary tensor product of two reduced coordinate algebras is reduced. In particular, the tensor
square of a reduced closed subgroup remains reduced, as required when its defining ideal is
transported through comultiplication.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlgProperty.tensorProduct`: finite-type geometrically
  reduced affine groups are closed under direct products.
* `TauCeti.CommHopfAlgCat.isReduced_tensorProduct_of_isAlgClosed`: over an algebraically closed
  field, the tensor product of two reduced finite-type coordinate Hopf algebras is reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace geometricallyReducedCommHopfAlgProperty

variable {k : Type u} [Field k]

/-- The tensor product of two finite-type geometrically reduced commutative Hopf algebras is
geometrically reduced. Contravariantly, direct products of geometrically reduced affine groups of
finite type are geometrically reduced. -/
theorem tensorProduct (H K : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] [Algebra.FiniteType k K]
    (hH : geometricallyReducedCommHopfAlgProperty k H)
    (hK : geometricallyReducedCommHopfAlgProperty k K) :
    geometricallyReducedCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  let _ : Algebra.FiniteType k (H ⊗[k] K) :=
    FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) H K
  rw [← smoothCommHopfAlgProperty_iff_geometricallyReduced] at hH hK ⊢
  exact smoothCommHopfAlgProperty.tensorProduct H K hH hK

end geometricallyReducedCommHopfAlgProperty

namespace CommHopfAlgCat

/-- Over an algebraically closed field, the tensor product of two reduced finite-type coordinate
Hopf algebras is reduced. -/
theorem isReduced_tensorProduct_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] (H K : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] [Algebra.FiniteType k K] [IsReduced H] [IsReduced K] :
    IsReduced (H ⊗[k] K) := by
  have hH : geometricallyReducedCommHopfAlgProperty k H :=
    (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k H).2 inferInstance
  have hK : geometricallyReducedCommHopfAlgProperty k K :=
    (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k K).2 inferInstance
  exact (geometricallyReducedCommHopfAlgProperty.tensorProduct H K hH hK).isReduced

end CommHopfAlgCat

end

end TauCeti
