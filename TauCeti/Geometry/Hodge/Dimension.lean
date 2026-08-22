/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.LinearAlgebra.Dimension.BaseChange
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Hodge numbers

The `p`-th **Hodge number** of a weight-`n` Hodge structure is the dimension
`h^{p,n-p} = dim_ℂ H^{p,n-p}` of its `p`-th Hodge component. This file records the two facts that
make the family of Hodge numbers a numerical invariant of the structure:

* **Hodge symmetry**, `h^{p,q} = h^{q,p}`: the conjugation carries `H^{p,n-p}` onto `H^{n-p,p}`.
  It is only conjugate-linear, so it is not an isomorphism of complex vector spaces; it is an
  isomorphism of the underlying *real* vector spaces
  (`TauCeti.Hodge.HodgeStructureOn.pieceConjEquiv`, in `TauCeti/Geometry/Hodge/Structure.lean`),
  and the two dimensions over `ℂ` are both half of the common dimension over `ℝ`.
* **The Hodge numbers partition the dimension**, `∑ᶠ p, h^{p,n-p} = dim_ℂ V_ℂ`: only finitely many
  Hodge components are nonzero because the filtration is bounded, and they decompose `V_ℂ` as an
  internal direct sum.

For a Hodge structure carried on a lattice, `dim_ℂ V_ℂ` is in turn the rank of the lattice.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.hodgeNumber`: the Hodge number `h^{p,n-p}`.
* `TauCeti.Hodge.HodgeStructureOn.finite_setOf_hodgeNumber_ne_zero`: only finitely many Hodge
  numbers are nonzero.
* `TauCeti.Hodge.HodgeStructureOn.hodgeNumber_symm`: Hodge symmetry.
* `TauCeti.Hodge.HodgeStructureOn.finsum_hodgeNumber_eq_finrank`: the Hodge numbers sum to the
  dimension.
* `TauCeti.Hodge.finsum_hodgeNumber_eq_finrank_lattice`: the Hodge numbers of a Hodge structure
  carried on a lattice sum to the rank of that lattice.
* `TauCeti.Hodge.HodgeType`: a weight and a symmetric, finitely supported family of Hodge numbers.
* `TauCeti.Hodge.HodgeStructureOn.hodgeType`: the Hodge type of a Hodge structure.

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6, and Peters–Steenbrink, *Mixed Hodge
Structures*, §2. This is the numerical layer of Layer L3 of
`TauCetiRoadmap/HodgeStructures/README.md`. The signature of `HodgeType` is adapted from the
roadmap's formal companion `HodgeStructures/Suggested.lean`.
-/

public section

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The `p`-th **Hodge number** `h^{p,n-p}` of a weight-`n` Hodge structure: the complex dimension
of its `p`-th Hodge component.

This follows the convention of `Module.finrank`, so an infinite-dimensional component has Hodge
number `0`; the statements that read the Hodge numbers as a dimension count, such as
`finsum_hodgeNumber_eq_finrank`, therefore assume the ambient space is finite-dimensional. -/
noncomputable def hodgeNumber (hs : HodgeStructureOn W ω n) (p : ℤ) : ℕ :=
  Module.finrank ℂ (hs.piece p)

/-- The Hodge number is the dimension of the Hodge component. -/
theorem hodgeNumber_def (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.hodgeNumber p = Module.finrank ℂ (hs.piece p) :=
  (rfl)

/-- Only finitely many Hodge numbers are nonzero. -/
theorem finite_setOf_hodgeNumber_ne_zero (hs : HodgeStructureOn W ω n) :
    {p | hs.hodgeNumber p ≠ 0}.Finite := by
  refine hs.finite_setOf_piece_ne_bot.subset fun p hp hbot ↦ hp ?_
  rw [hodgeNumber_def, hbot, finrank_bot]

/-- **Hodge symmetry**: `h^{p,q} = h^{q,p}`, where `q = n - p`. -/
theorem hodgeNumber_symm (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.hodgeNumber p = hs.hodgeNumber (n - p) := by
  have h := (hs.pieceConjEquiv p).finrank_eq
  rw [finrank_real_of_complex, finrank_real_of_complex] at h
  simp only [hodgeNumber_def]
  omega

/-- **The Hodge numbers partition the dimension**: the Hodge numbers of a weight-`n` Hodge
structure on a finite-dimensional complex vector space sum to its dimension. -/
theorem finsum_hodgeNumber_eq_finrank (hs : HodgeStructureOn W ω n) [FiniteDimensional ℂ W] :
    ∑ᶠ p, hs.hodgeNumber p = Module.finrank ℂ W :=
  finsum_finrank_eq_finrank_of_isInternal hs.isInternal_piece hs.finite_setOf_piece_ne_bot

end HodgeStructureOn

/-- The numerical type of a pure Hodge structure: a weight, Hodge numbers `h` of finite support,
and the **Hodge symmetry** `h p = h (weight - p)`.

The symmetry is not an extra restriction on the types that occur, since conjugation exchanges the
Hodge components `H^{p,q}` and `H^{q,p}` of any Hodge structure; it excludes the asymmetric
families of numbers that no Hodge structure realizes. -/
@[ext]
structure HodgeType where
  /-- The weight of the Hodge structures of this type. -/
  weight : ℤ
  /-- The prescribed Hodge numbers. -/
  h : ℤ → ℕ
  /-- All but finitely many Hodge numbers vanish. -/
  finite_support : {p | h p ≠ 0}.Finite
  /-- Hodge symmetry: `h^{p,q} = h^{q,p}`. -/
  symm : ∀ p, h p = h (weight - p)

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The Hodge type of a Hodge structure: its weight together with its own Hodge numbers.

Both axioms of `HodgeType` hold for any Hodge structure: the support is finite because the Hodge
filtration is bounded, and the symmetry is Hodge symmetry. Following the convention of
`Module.finrank`, an infinite-dimensional Hodge component contributes the Hodge number `0`; the
statements reading these numbers as a dimension count, such as
`HodgeStructureOn.finsum_hodgeNumber_eq_finrank`, assume finite-dimensionality separately. -/
noncomputable def hodgeType (hs : HodgeStructureOn W ω n) : HodgeType where
  weight := n
  h := hs.hodgeNumber
  finite_support := hs.finite_setOf_hodgeNumber_ne_zero
  symm := hs.hodgeNumber_symm

@[simp]
theorem hodgeType_weight (hs : HodgeStructureOn W ω n) : hs.hodgeType.weight = n :=
  (rfl)

@[simp]
theorem hodgeType_h (hs : HodgeStructureOn W ω n) : hs.hodgeType.h = hs.hodgeNumber :=
  (rfl)

end HodgeStructureOn

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- **The Hodge numbers of a Hodge structure on a lattice partition the rank of the lattice.** -/
theorem finsum_hodgeNumber_eq_finrank_lattice [Module.Free ℤ V] [Module.Finite ℤ V]
    {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} (hs : HodgeStructure hℂ n) :
    ∑ᶠ p, hs.hodgeNumber p = Module.finrank ℤ V := by
  have := finite_of_isBaseChange hℂ
  rw [HodgeStructureOn.finsum_hodgeNumber_eq_finrank hs, finrank_of_isBaseChange hℂ]

end TauCeti.Hodge
