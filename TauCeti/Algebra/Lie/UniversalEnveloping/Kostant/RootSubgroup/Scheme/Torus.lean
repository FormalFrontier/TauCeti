/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeightTorus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic

/-!
# The Kostant weight torus as a group-scheme morphism

A finite weight basis `b : Basis (Fin n) ℤ M` of a Kostant-stable lattice gives a diagonal action
of the split torus `𝔾ₘ^κ` on every scalar extension of `M`. The pointwise action is
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints`, and its matrix in the base-changed basis
is `TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix`.

The same weight function defines the group-scheme morphism

```text
TauCeti.GeneralLinear.weightTorus wt : 𝔾ₘ^κ → GL_n.
```

This file identifies that represented morphism on scheme-valued points with the Kostant action.
Thus the torus constructed from the weight lattice is not merely a natural family of abstract
linear automorphisms: it is the `A`-point action of one explicit morphism over `ℤ`. Together with
the pointwise conjugation theorem in `RootSubgroup/Torus/Basic.lean`, this supplies the split-torus
side of the pinning interface in Layer 9 of the ReductiveGroups roadmap.

No faithfulness or maximality is claimed for an arbitrary weight function. Those properties
require the particular weights furnished by the Chevalley root datum.

## Main result

* `TauCeti.UniversalEnvelopingAlgebra.schemePointsMulEquiv_weightTorus_eq_kostantTorusMatrix`:
  composing a scheme-valued torus point with the represented weight torus gives the matrix of the
  existing Kostant torus action.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §§4.4 and 7.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe v

variable {κ : Type} [Fintype κ]
variable {V : Type v} [AddCommGroup V]
variable (M : AddSubgroup V)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

variable (A : Type) [CommRing A] [Algebra ℤ A]

/-- Scheme-valued points of the represented weight torus are exactly the matrices of the
pointwise Kostant torus action in the given weight basis. -/
theorem schemePointsMulEquiv_weightTorus_eq_kostantTorusMatrix
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (GeneralLinear.weightTorus (R := ℤ) wt).hom.hom) =
      kostantTorusMatrix M b wt
        (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) p) := by
  rw [GeneralLinear.schemePointsMulEquiv_weightTorus, kostantTorusMatrix_apply]

end TauCeti.UniversalEnvelopingAlgebra
