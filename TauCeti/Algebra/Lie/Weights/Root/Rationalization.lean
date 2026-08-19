/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Subalgebra.Rationalization
public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice

/-!
# Rationalizing the Chevalley Lie lattice

A Chevalley system supplies the integral root--coroot Lie lattice
`IsChevalleySystem.chevalleyLieLattice`. Its underlying integer module is finite and free, and its
rational span is the whole ambient Lie algebra. This file packages those facts as a full lattice
instance and applies the generic Lie-lattice rationalization theorem to obtain

```text
ℚ ⊗[ℤ] hx.chevalleyLieLattice ≃ₗ⁅ℚ⁆ L.
```

It also selects a finite basis of the integral lattice, indexed by the dimension of `L`. This is
the basis shape required by the matrix-coordinate and Kostant root-subgroup constructions. The
basis is not claimed to be an additional root-vector normalization: all pinned mathematical data
remain in the Chevalley system and in the named root and coroot generators.

## Main declarations

* `TauCeti.IsChevalleySystem.instIsLatticeChevalleyLieLattice`: the root--coroot Lie lattice is a
  full integral lattice.
* `TauCeti.IsChevalleySystem.chevalleyLieLatticeRationalization`: its scalar extension recovers
  the ambient rational Lie algebra as a Lie algebra.
* `TauCeti.IsChevalleySystem.chevalleyLieLatticeFinBasis`: a finite basis indexed by
  `Fin (finrank ℚ L)` for use in matrix constructions.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the Chevalley-basis and generic-fibre part of the explicit pinned
Chevalley--Demazure construction in Layer 9 of the `ReductiveGroups` roadmap. That construction is
the declared input to milestone L0 of the `CFSGStatement` roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra.IsKilling ℚ L]
  [FiniteDimensional ℚ L]
  {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℚ H L]
  {ω : L ≃ₗ⁅ℚ⁆ L} {x : Weight ℚ H L → L}

namespace IsChevalleySystem

variable (hx : IsChevalleySystem ω x)

include hx

/-- The Chevalley root--coroot Lie lattice is a full integral lattice in the ambient rational Lie
algebra. -/
instance instIsLatticeChevalleyLieLattice :
    hx.chevalleyLieLattice.toSubmodule.IsLattice ℚ where
  fg := by
    rw [hx.chevalleyLieLattice_toSubmodule, rootCorootSpan_eq_span_generators]
    exact Submodule.fg_span (finite_rootCorootGenerators x)
  span_eq_top := hx.span_chevalleyLieLattice_eq_top

/-- The scalar extension of the Chevalley Lie lattice recovers the ambient rational Lie algebra,
including its Lie bracket. -/
noncomputable def chevalleyLieLatticeRationalization :
    ℚ ⊗[ℤ] hx.chevalleyLieLattice ≃ₗ⁅ℚ⁆ L :=
  LieSubalgebra.rationalizationEquiv hx.chevalleyLieLattice

/-- On pure tensors, the Chevalley-lattice rationalization is the ambient scalar action. -/
@[simp]
theorem chevalleyLieLatticeRationalization_tmul (q : ℚ) (z : hx.chevalleyLieLattice) :
    hx.chevalleyLieLatticeRationalization (q ⊗ₜ[ℤ] z) = q • (z : L) :=
  by
    rw [chevalleyLieLatticeRationalization]
    exact LieSubalgebra.rationalizationEquiv_tmul hx.chevalleyLieLattice q z

/-- The inverse Chevalley-lattice rationalization sends an integral vector to its unit pure
tensor. -/
@[simp]
theorem chevalleyLieLatticeRationalization_symm_coe (z : hx.chevalleyLieLattice) :
    hx.chevalleyLieLatticeRationalization.symm (z : L) = 1 ⊗ₜ[ℤ] z :=
  by
    rw [chevalleyLieLatticeRationalization]
    exact LieSubalgebra.rationalizationEquiv_symm_coe hx.chevalleyLieLattice z

/-- A finite basis of the Chevalley Lie lattice indexed by the dimension of the ambient rational
Lie algebra.

This is an arbitrary module basis of the already pinned root--coroot lattice. It is intended for
matrix coordinates; it does not replace or renormalize the Chevalley system's named root vectors
and coroots. -/
noncomputable def chevalleyLieLatticeFinBasis :
    Module.Basis (Fin (Module.finrank ℚ L)) ℤ hx.chevalleyLieLattice :=
  Module.finBasisOfFinrankEq ℤ hx.chevalleyLieLattice
    (Submodule.IsLattice.finrank_eq_finrank hx.chevalleyLieLattice.toSubmodule)

end IsChevalleySystem

end TauCeti
