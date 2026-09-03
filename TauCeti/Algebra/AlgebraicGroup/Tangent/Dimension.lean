/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Dimensions of tangent Lie algebras

For an affine monoid over a field, the tangent Lie algebra is the linear dual of the
augmentation cotangent space. This file records the resulting equality of their `Module.finrank`
values and shows that the tangent Lie algebra of a finite-type affine monoid is finite-dimensional.
Without a finiteness hypothesis, this equality uses Mathlib's convention that the `finrank` of an
infinite-dimensional space is zero.

When the cotangent space is finite-dimensional, tangent vectors with values in an extension field
`K` are the scalar extension of base-field tangent vectors; projectivity is automatic over a
field. Consequently their dimension over `K` is the dimension of the original tangent space over
`k`:

```text
dim_K Lie(G)(K) = dim_k Lie(G)(k).
```

This is the base-change dimension tool needed before geometric dimension and smoothness arguments
in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `Derivation.finrank_eq_finrank_cotangentSpace`: tangent and cotangent `finrank` values
  agree.
* `Derivation.instFiniteDimensionalDerivationCounitAlgebra`: tangent spaces with
  coefficient-field values are finite-dimensional when the augmentation cotangent space is.
* `Derivation.finrank_tangent_baseChange`: tangent dimension is invariant under extension
  of the coefficient field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 12.
-/

public section

universe u v w

open scoped TensorProduct

namespace Derivation

open TauCeti

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]

/-- The augmentation cotangent space and tangent Lie algebra at the identity have the same
`Module.finrank` over the base field. Without a finiteness hypothesis, this is an equality in
Mathlib's finite-rank convention, where infinite-dimensional spaces have `finrank` zero. -/
@[simp]
theorem finrank_eq_finrank_cotangentSpace :
    Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
      Module.finrank k (Bialgebra.CotangentSpace k H) :=
  (cotangentLinearEquiv (R := k) (A := H) (B := k)).finrank_eq.symm.trans
    Subspace.dual_finrank_eq

variable {K : Type w} [Field K] [Algebra k K]

/-- Tangent vectors with values in an extension field are finite-dimensional when the
augmentation cotangent space is finite-dimensional. -/
noncomputable instance instFiniteDimensionalDerivationCounitAlgebra
    [Module.Finite k (Bialgebra.CotangentSpace k H)] :
    FiniteDimensional K
      (Derivation k H (Bialgebra.CounitAlgebra k H K)) := by
  let _ : Module.Projective k (Bialgebra.CotangentSpace k H) :=
    Module.projective_of_isSemisimpleRing _ _
  exact Module.Finite.equiv
    (tangentScalarExtensionEquiv (R := k) (A := H) (B := K))

/-- **Tangent dimension is invariant under extension of the coefficient field.**

Here `Derivation k H (CounitAlgebra k H K)` is the `K`-valued tangent space of the affine
monoid represented by `H`. Finite-dimensionality gives its canonical scalar-extension
description, since modules over a field are projective. -/
@[simp]
theorem finrank_tangent_baseChange
    [Module.Finite k (Bialgebra.CotangentSpace k H)] :
    Module.finrank K
        (Derivation k H (Bialgebra.CounitAlgebra k H K)) =
      Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let _ : Module.Projective k (Bialgebra.CotangentSpace k H) :=
    Module.projective_of_isSemisimpleRing _ _
  calc
    Module.finrank K
          (Derivation k H (Bialgebra.CounitAlgebra k H K)) =
        Module.finrank K
          (K ⊗[k] Module.Dual k (Bialgebra.CotangentSpace k H)) :=
      (tangentScalarExtensionEquiv (R := k) (A := H) (B := K)).finrank_eq.symm
    _ = Module.finrank k (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
      Module.finrank_baseChange
    _ = Module.finrank k
          (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
      (cotangentLinearEquiv (R := k) (A := H) (B := k)).finrank_eq

end Derivation
