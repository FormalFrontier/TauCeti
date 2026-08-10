/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Dimensions of tangent Lie algebras

For an affine group over a field, the tangent Lie algebra is the linear dual of the
augmentation cotangent space. This file records the resulting equality of dimensions and shows
that the tangent Lie algebra of a finite-type affine group is finite-dimensional.

When the cotangent space is finite projective, tangent vectors with values in an extension field
`K` are the scalar extension of base-field tangent vectors. Consequently their dimension over
`K` is the dimension of the original tangent space over `k`:

```text
dim_K Lie(G)(K) = dim_k Lie(G)(k).
```

This is the base-change dimension tool needed before geometric dimension and smoothness arguments
in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Derivation.finrank_eq_finrank_cotangentSpace`: tangent and cotangent dimensions agree.
* `TauCeti.Bialgebra.instFiniteDimensionalDerivationCounitAlgebra`: finite-type affine groups
  have finite-dimensional tangent Lie algebras.
* `TauCeti.Derivation.finrank_tangent_baseChange`: tangent dimension is invariant under extension
  of the coefficient field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 12.
-/

public section

namespace TauCeti

universe u v w

open scoped TensorProduct

namespace Derivation

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]

/-- The tangent Lie algebra at the identity and the augmentation cotangent space have the same
dimension over the base field. -/
theorem finrank_eq_finrank_cotangentSpace :
    Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
      Module.finrank k (Bialgebra.CotangentSpace k H) :=
  (cotangentLinearEquiv (R := k) (A := H) (B := k)).finrank_eq.symm.trans
    Subspace.dual_finrank_eq

end Derivation

namespace Bialgebra

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]

/-- The tangent Lie algebra of a finite-type affine monoid over a field is finite-dimensional. -/
noncomputable instance instFiniteDimensionalDerivationCounitAlgebra
    [Algebra.FiniteType k H] :
    FiniteDimensional k
      (Derivation k H (CounitAlgebra k H k)) :=
  Module.Finite.equiv
    (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k))

end Bialgebra

namespace Derivation

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable {K : Type w} [Field K] [Algebra k K]

/-- Tangent vectors with values in an extension field are finite-dimensional when the
augmentation cotangent space is finite projective. -/
noncomputable instance instFiniteDimensionalCounitAlgebraBaseChange
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Projective k (Bialgebra.CotangentSpace k H)] :
    FiniteDimensional K
      (Derivation k H (Bialgebra.CounitAlgebra k H K)) :=
  Module.Finite.equiv
    (tangentScalarExtensionEquiv (R := k) (A := H) (B := K))

/-- **Tangent dimension is invariant under extension of the coefficient field.**

Here `Derivation k H (CounitAlgebra k H K)` is the `K`-valued tangent space of the affine
monoid represented by `H`. The finite-projective hypotheses give its canonical scalar-extension
description. -/
theorem finrank_tangent_baseChange
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Projective k (Bialgebra.CotangentSpace k H)] :
    Module.finrank K
        (Derivation k H (Bialgebra.CounitAlgebra k H K)) =
      Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
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

end TauCeti
