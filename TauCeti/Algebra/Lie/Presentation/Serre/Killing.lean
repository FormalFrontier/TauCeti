/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Base
public import TauCeti.Algebra.Lie.Presentation.Serre.Basis

/-!
# Serre systems in a split semisimple Lie algebra

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `b` be a base of the root
system of `(L, H)`. Mathlib's `LieAlgebra.exists_basis_of_base` supplies a
`LieAlgebra.Basis b.support H` whose Cartan matrix is `b.cartanMatrix` and whose Cartan generators
are the simple coroots. The general basis theorem `TauCeti.isSerreSystem_lieBasis` then shows that
its generators form a Serre system.

Consequently `L` is a quotient of the Serre algebra of the transposed Cartan matrix of `b`, by a
homomorphism sending `Hᵢ` to the simple coroot `αᵢ∨`. The transpose reconciles the conventions:
`TauCeti.IsSerreSystem` states `⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ`, while
`RootPairing.Base.cartanMatrix i j` is `⟨αᵢ, αⱼ∨⟩`.

## Main results

* `TauCeti.exists_isSerreSystem_of_base`: a root-system base determines raising and lowering
  families that generate `L` and form a Serre system.
* `TauCeti.exists_surjective_serreLift_of_base`: `L` is a quotient of the corresponding Serre
  algebra by a map sending the Cartan generators to the simple coroots.

## References

* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI
* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §18.1

## Roadmap

The Serre presentation is the explicit carrier of the split semisimple Lie algebra whose Chevalley
basis and Kostant `ℤ`-form build the Chevalley--Demazure group scheme, Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed in turn by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing
open scoped Matrix

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **A split semisimple Lie algebra carries a Serre system for its Cartan matrix**, whose
raising and lowering families generate it. -/
theorem exists_isSerreSystem_of_base (b : (rootSystem H).Base) :
    ∃ e f : ↥b.support → L,
      IsSerreSystem K b.cartanMatrixᵀ (fun i ↦ (((rootSystem H).coroot i : H) : L)) e f ∧
        LieSubalgebra.lieSpan K L (Set.range e ∪ Set.range f) = ⊤ := by
  obtain ⟨B, hA, hh⟩ := exists_basis_of_base b
  refine ⟨B.e, B.f, ?_, B.span_ef⟩
  rw [← hA]
  have hH : B.h = fun i : ↥b.support ↦
      (((rootSystem H).coroot (i : H.root) : H) : L) := funext hh
  rw [← hH]
  exact isSerreSystem_lieBasis B

open scoped Classical in
/-- **A split semisimple Lie algebra is a quotient of the Serre algebra of its Cartan matrix**,
by a homomorphism sending the generator `Hᵢ` to the simple coroot `αᵢ∨`. -/
theorem exists_surjective_serreLift_of_base (b : (rootSystem H).Base) :
    ∃ φ : Matrix.ToLieAlgebra K b.cartanMatrixᵀ →ₗ⁅K⁆ L, Function.Surjective φ ∧
      ∀ i, φ (serreH K b.cartanMatrixᵀ i) = (((rootSystem H).coroot i : H) : L) := by
  obtain ⟨e, f, hS, hspan⟩ := exists_isSerreSystem_of_base b
  exact ⟨serreLift hS, serreLift_surjective hS hspan, fun i ↦ serreLift_serreH hS i⟩

end TauCeti
