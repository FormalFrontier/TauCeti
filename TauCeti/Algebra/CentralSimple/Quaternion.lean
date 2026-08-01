/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.Opposite` is imported publicly: it supplies
-- `TauCeti.Algebra.tensorOpAlgEquivMatrix`, of which everything below is an instance, and it
-- re-exports `TauCeti.Algebra.CentralSimple.Degree` (hence `TauCeti.Algebra.deg`) together with
-- the `⊗[ℝ]` notation and the matrix algebras, which is why none of those is imported again here.
public import TauCeti.Algebra.CentralSimple.Opposite
-- `TauCeti.Algebra.Central.Quaternion` is imported publicly for two reasons: `ℍ[ℝ]` occurs in every
-- statement below, and it is the instance `TauCeti.Quaternion.instIsCentral` proved there that puts
-- `ℍ[ℝ]` in the scope of the opposite isomorphism at all. It re-exports
-- `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation, quaternion conjugation
-- `Quaternion.starAe`, and `Quaternion.finrank_eq_four`.
public import TauCeti.Algebra.Central.Quaternion
-- `Mathlib.Data.Real.Basic` is imported publicly because the field structure on `ℝ` is what makes
-- the statements below typecheck.
public import Mathlib.Data.Real.Basic

/-!
# The tensor square of the real quaternions is `M₄(ℝ)`

The real quaternions `ℍ[ℝ]` are a central division algebra of dimension `4` over `ℝ`, hence a
central simple `ℝ`-algebra of degree `2`. This file runs the opposite isomorphism of
`TauCeti/Algebra/CentralSimple/Opposite.lean` on them, in the two forms

`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`  and
`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.

The second follows from the first because quaternion conjugation is an `ℝ`-algebra isomorphism
`ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (Mathlib's `Quaternion.starAe`): the quaternions are their own opposite. So
the Brauer class of `ℍ[ℝ]` is its own inverse.

That class is not the identity: `TauCeti.Quaternion.isEmpty_algEquiv_matrix` says `ℍ[ℝ]` is not
isomorphic to any matrix algebra of size at least two, and the only such candidate in dimension `4`
is `Matrix (Fin 2) (Fin 2) ℝ`. The two facts together say that the class of `ℍ[ℝ]` has order exactly
two, which is the content of `BrauerGroup ℝ ≃ ℤ/2` that does not need the classification of real
division algebras. That classification, and with it the statement that the class of `ℍ[ℝ]`
generates, is a separate long-term target and is not proved here.

The matrix size is `4` and not `2`: it is the **dimension** `Module.finrank ℝ ℍ[ℝ] = 4` of the
algebra, not its degree `TauCeti.Algebra.deg ℝ ℍ[ℝ] = 2`. Squaring the degree is exactly what taking
the tensor product with the opposite algebra does, and
`TauCeti.Quaternion.deg_tensorProduct_self` records it.

## Main results

* `TauCeti.Quaternion.tensorMulOppositeAlgEquivMatrix`:
  `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.
* `TauCeti.Quaternion.tensorSelfAlgEquivMatrix`: `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`,
  the roadmap's worked example.
* `TauCeti.Quaternion.deg_tensorProduct_self`: the tensor square has degree `4`.

## References

This is the `ℍ[ℝ] ⊗_ℝ ℍ[ℝ] ≃ M₄(ℝ)` half of the Hamilton-quaternion worked example of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `quaternion_tensor_self`; the centrality half is
`TauCeti/Algebra/Central/Quaternion.lean`. See P. Gille, T. Szamuely, *Central Simple Algebras and
Galois Cohomology*, CUP (2006), §1.1 and §2.1.
-/

public section

open scoped Quaternion TensorProduct

namespace TauCeti

namespace Quaternion

/-- **`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`**: the opposite isomorphism at the real
quaternions. All three hypotheses of `TauCeti.Algebra.tensorOpAlgEquivMatrix` are found by instance
search -- `Algebra.IsCentral ℝ ℍ[ℝ]` from `TauCeti.Quaternion.instIsCentral`, `IsSimpleRing ℍ[ℝ]`
because a division ring is simple, and `FiniteDimensional ℝ ℍ[ℝ]` -- so only the dimension
`Quaternion.finrank_eq_four` has to be supplied. -/
noncomputable def tensorMulOppositeAlgEquivMatrix :
    ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  Algebra.tensorOpAlgEquivMatrix ℝ ℍ[ℝ] _root_.Quaternion.finrank_eq_four

/-- **`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.** Quaternion conjugation is an `ℝ`-algebra
isomorphism `ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (`Quaternion.starAe`), so the tensor square of `ℍ[ℝ]` is its tensor
product with its own opposite, which `TauCeti.Quaternion.tensorMulOppositeAlgEquivMatrix` splits.

In Brauer-group language: the class of `ℍ[ℝ]` is its own inverse. It is not the identity class, by
`TauCeti.Quaternion.isEmpty_algEquiv_matrix`, so it has order exactly two. -/
noncomputable def tensorSelfAlgEquivMatrix :
    ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (A₁ := ℍ[ℝ])) _root_.Quaternion.starAe).trans
    tensorMulOppositeAlgEquivMatrix

/-- The tensor square of the real quaternions has degree `4`: tensoring a central simple algebra
with its opposite squares the degree, and `TauCeti.Algebra.deg ℝ ℍ[ℝ] = 2`.

The proof is the multiplicativity of the degree, so this is an independent check on the matrix size
in `TauCeti.Quaternion.tensorSelfAlgEquivMatrix`: `4` really is `2 · 2`, and not the degree `2` of
either factor. Not a `simp` lemma, because `TauCeti.Algebra.deg_tensorProduct` already rewrites the
left-hand side to `TauCeti.Algebra.deg ℝ ℍ[ℝ] * TauCeti.Algebra.deg ℝ ℍ[ℝ]`. -/
theorem deg_tensorProduct_self : Algebra.deg ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) = 4 := by
  have h : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [_root_.Quaternion.finrank_eq_four]; norm_num)
  rw [Algebra.deg_tensorProduct, h]

/-- The tensor square is split, but `ℍ[ℝ]` itself is not: the only matrix algebra over `ℝ` of
dimension `4` is `Matrix (Fin 2) (Fin 2) ℝ`, and `ℍ[ℝ]` is a division algebra, so no isomorphism
exists. This is the second half of "the Brauer class of `ℍ[ℝ]` has order exactly two". -/
example : IsEmpty (ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  isEmpty_algEquiv_matrix ℝ (Fin 2)

end Quaternion

end TauCeti
