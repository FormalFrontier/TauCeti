/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite

/-!
# Finite-dimensional comodules generating a finite-type algebra-coalgebra

Let `C` be a coalgebra over a field which is also finitely generated as an algebra. Choose a
finite algebra-generating set and place it in a finite-dimensional subcoalgebra `D` using the
fundamental theorem of coalgebras. The regular coaction restricts to `D`, and every element of
`D` is a matrix coefficient of this restricted comodule: pair it with the restriction of the
counit. Consequently, the matrix coefficients of one finite-dimensional subcomodule generate
the whole algebra `C`.

For a commutative Hopf algebra, this is the finite-dimensional construction at the heart of the
affine-group embedding theorem. After choosing a basis, its coefficient matrix defines a map to
`GLₙ`; the faithful-representation criterion identifies generation by its coefficients with a
closed immersion.

## Main declaration

* `TauCeti.Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top`:
  a finite-type algebra-coalgebra over a field has a finite-dimensional subcomodule whose matrix
  coefficients generate the whole algebra.

## References

This is the standard proof of the embedding theorem's finite-dimensional representation step;
see J. S. Milne, *Algebraic Groups* (2017), Proposition 4.7 and Theorem 4.9. It advances Layer 1,
"Embedding theorem (hard)", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u v

namespace Comodule

variable {k : Type u} {C : Type v}
variable [Field k] [Semiring C] [Algebra k C] [Coalgebra k C]

/-- A finite-type algebra-coalgebra over a field has a module-finite subcomodule of its regular
comodule whose matrix coefficients generate the whole algebra. Over the field `k`, module-finite
is finite-dimensional. -/
theorem exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top
    [Algebra.FiniteType k C] :
    let _ : Ring C := Algebra.semiringToRing k
    ∃ M : Subcomodule k C C, Module.Finite k M.toSubmodule ∧
      matrixCoefficientSubalgebra (R := k) (C := C) (M := M) = ⊤ := by
  let _ : Ring C := Algebra.semiringToRing k
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k C).out
  obtain ⟨D, hDfinite, hsD⟩ :=
    Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
      (k := k) (C := C) (s : Set C) s.finite_toSet
  let : Module.Finite k D.toSubmodule := hDfinite
  refine ⟨D.toRegularSubcomodule, D.toRegularSubcomodule_finite, top_unique ?_⟩
  rw [← hs]
  exact Algebra.adjoin_le fun c hc =>
    Subcoalgebra.le_matrixCoefficientSubalgebra_toRegularSubcomodule D (hsD hc)

end Comodule

end TauCeti
