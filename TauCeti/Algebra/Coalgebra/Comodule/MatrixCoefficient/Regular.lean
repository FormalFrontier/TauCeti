/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.Regular
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.RegularSubcomodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Matrix coefficients of the regular comodule

This file records that the regular right comodule has enough matrix coefficients to recover
the whole coalgebra, and likewise that the coefficients of its restriction to a subcoalgebra
recover that subcoalgebra. The key coefficient is the counit: for the regular comodule, the
matrix coefficient attached to `Coalgebra.counit` and a vector `c` is exactly `c`.

This is a small Layer 1 prerequisite for the reductive-groups roadmap's faithful
representation criterion, where faithfulness is detected by whether matrix coefficients
generate the coordinate Hopf algebra. It proves that the regular representation satisfies
that generated-coefficient condition.

## Main declarations

* `TauCeti.Comodule.regular_matrixCoefficientSet_eq_univ`: every element of a coalgebra is a
  matrix coefficient of the regular comodule.
* `TauCeti.Comodule.regular_matrixCoefficientSubmodule_eq_top`: regular coefficients span the
  whole coalgebra.
* `TauCeti.Comodule.regular_matrixCoefficientSubalgebra_eq_top`: for a bialgebra or algebra
  coalgebra, regular coefficients generate the whole algebra.
* `TauCeti.Subcoalgebra.le_matrixCoefficientSubalgebra_toRegularSubcomodule`: a subcoalgebra is
  contained in the coefficient algebra of its restricted regular comodule.

## References

This is the standard observation that the regular comodule's coefficient space is the whole
coalgebra; see Sweedler, *Hopf Algebras*, Chapter 2. It uses the existing Tau Ceti matrix
coefficient API and Mathlib's counit law for coalgebras.
-/

public section

namespace TauCeti

namespace Comodule

universe u v

variable {R : Type u} {C : Type v}
variable [CommSemiring R]

section Coalgebra

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Every element of a coalgebra is a matrix coefficient of the regular comodule.

The element `c` is obtained by pairing `c` with the counit functional. -/
theorem mem_regular_matrixCoefficientSet (c : C) :
    c ∈ matrixCoefficientSet (R := R) (C := C) (M := C) := by
  rw [mem_matrixCoefficientSet_iff]
  exact ⟨Coalgebra.counit (R := R) (A := C), c, matrixCoefficient_counit_self (R := R) c⟩

/-- The matrix coefficient set of the regular comodule is the whole coalgebra. -/
@[simp]
theorem regular_matrixCoefficientSet_eq_univ :
    matrixCoefficientSet (R := R) (C := C) (M := C) = Set.univ := by
  ext c
  exact ⟨fun _ => Set.mem_univ c, fun _ => mem_regular_matrixCoefficientSet (R := R) (C := C) c⟩

/-- A submodule contains all regular-comodule matrix coefficients iff it is top. -/
theorem regular_matrixCoefficientSubmodule_le_iff_eq_top {P : Submodule R C} :
    matrixCoefficientSubmodule (R := R) (C := C) (M := C) ≤ P ↔ P = ⊤ := by
  constructor
  · intro hP
    rw [eq_top_iff]
    intro c _
    rw [← matrixCoefficient_counit_self (R := R) c]
    exact hP (matrixCoefficient_mem_submodule (R := R) (C := C)
      (Coalgebra.counit (R := R) (A := C)) c)
  · intro hP
    rw [hP]
    exact le_top

/-- The regular comodule's matrix coefficients span the whole coalgebra. -/
@[simp]
theorem regular_matrixCoefficientSubmodule_eq_top :
    matrixCoefficientSubmodule (R := R) (C := C) (M := C) = ⊤ := by
  rw [matrixCoefficientSubmodule, regular_matrixCoefficientSet_eq_univ]
  exact Submodule.span_univ

/-- Every element of the bundled regular comodule's coalgebra is a matrix coefficient. -/
theorem mem_regularObj_matrixCoefficientSet (c : ComoduleCat.regular R C) :
    c ∈ matrixCoefficientSet (R := R) (C := C) (M := ComoduleCat.regular R C) :=
  mem_regular_matrixCoefficientSet (R := R) (C := C) c

/-- The bundled regular comodule's matrix coefficient set is the whole coalgebra. -/
theorem regularObj_matrixCoefficientSet_eq_univ :
    matrixCoefficientSet (R := R) (C := C) (M := ComoduleCat.regular R C) = Set.univ :=
  regular_matrixCoefficientSet_eq_univ (R := R) (C := C)

/-- The bundled regular comodule's matrix coefficients span the whole coalgebra. -/
theorem regularObj_matrixCoefficientSubmodule_eq_top :
    matrixCoefficientSubmodule (R := R) (C := C) (M := ComoduleCat.regular R C) = ⊤ :=
  regular_matrixCoefficientSubmodule_eq_top (R := R) (C := C)

end Coalgebra

section Algebra

variable [Semiring C] [Algebra R C] [Coalgebra R C]

/-- A subalgebra contains all regular-comodule matrix coefficients iff it is top. -/
theorem regular_matrixCoefficientSubalgebra_le_iff_eq_top {S : Subalgebra R C} :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := C) ≤ S ↔ S = ⊤ := by
  constructor
  · intro hS
    rw [eq_top_iff]
    intro c _
    rw [← matrixCoefficient_counit_self (R := R) c]
    exact hS (matrixCoefficient_mem_subalgebra
      (R := R) (C := C) (M := C) (Coalgebra.counit (R := R) (A := C)) c)
  · intro hS
    rw [hS]
    exact le_top

/-- The regular comodule's matrix coefficients generate the whole ambient algebra. -/
@[simp]
theorem regular_matrixCoefficientSubalgebra_eq_top :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := C) = ⊤ :=
  matrixCoefficientSubalgebra_eq_top_of_submodule_eq_top
    (regular_matrixCoefficientSubmodule_eq_top (R := R) (C := C))

/-- The bundled regular comodule's matrix coefficients generate the whole ambient algebra. -/
theorem regularObj_matrixCoefficientSubalgebra_eq_top :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := ComoduleCat.regular R C) = ⊤ :=
  regular_matrixCoefficientSubalgebra_eq_top (R := R) (C := C)

end Algebra

end Comodule

namespace Subcoalgebra

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [Semiring C] [Algebra R C] [Coalgebra R C] [Module.Flat R C]

/-- A subcoalgebra lies in the algebra generated by the matrix coefficients of its restricted
regular comodule.

For `c ∈ D`, use `c` as a vector in `D` and restrict the coalgebra counit to `D`. The resulting
matrix coefficient is `c` by the counit law for the regular comodule. -/
theorem le_matrixCoefficientSubalgebra_toRegularSubcomodule (D : Subcoalgebra R C) :
    D.toSubmodule ≤
      (Comodule.matrixCoefficientSubalgebra
        (R := R) (C := C) (M := D.toRegularSubcomodule)).toSubmodule := by
  intro c hc
  let d : D.toRegularSubcomodule := ⟨c, hc⟩
  let phi : Module.Dual R D.toRegularSubcomodule :=
    (Coalgebra.counit (R := R) (A := C)).comp
      (Subcomodule.subtype D.toRegularSubcomodule).toLinearMap
  have hcoeff : Comodule.matrixCoefficient (R := R) (C := C) phi d = c := by
    rw [← Comodule.matrixCoefficient_map
      (Subcomodule.subtype D.toRegularSubcomodule)
      (Coalgebra.counit (R := R) (A := C)) d]
    simpa only [Subcomodule.subtype_apply, d] using
      Comodule.matrixCoefficient_counit_self (R := R) c
  rw [← hcoeff]
  exact Comodule.matrixCoefficient_mem_subalgebra (R := R) (C := C) phi d

end Subcoalgebra

end TauCeti
