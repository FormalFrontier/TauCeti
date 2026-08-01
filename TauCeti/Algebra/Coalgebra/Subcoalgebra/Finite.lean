/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Finite subcoalgebras containing a given element

This file proves the elementwise fundamental theorem of coalgebras over a principal ideal
domain: if the coalgebra is free as a module, then each of its elements belongs to a finite
subcoalgebra. Over a field the freeness hypothesis is automatic, so every coalgebra element
belongs to a finite-dimensional subcoalgebra.

The finite regular subcomodule containing the element need not itself be a subcoalgebra. Instead,
we equip its subtype with the induced comodule structure and take its matrix-coefficient
subcoalgebra. The counit matrix coefficient recovers the original element.

## Main declarations

* `TauCeti.Subcoalgebra.exists_finite_subcoalgebra_mem`: the PID result for a coalgebra that is
  free as a module.
* `TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem`: the field specialization.

## References

See Sweedler, *Hopf Algebras*, Chapter 2; Milne, *Algebraic Groups*, Proposition 4.7 and
Section 9d; and Hazewinkel, "Cofree coalgebras and multivariable recursiveness", Theorem 8.4.
-/

public section

namespace TauCeti

universe u v

namespace Subcoalgebra

variable {R : Type u} {C : Type v}

/-- If `C` is a coalgebra that is free as a module over a commutative principal ideal domain,
then every element of `C` belongs to a subcoalgebra that is finite as a module. -/
theorem exists_finite_subcoalgebra_mem [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C] (c : C) :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D := by
  letI : Module.Flat R C := Module.Flat.of_free
  obtain ⟨N, hNfinite, hcN⟩ :=
    Subcomodule.exists_finite_subcomodule_mem (R := R) (C := C) (M := C) c
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  letI : Module.Finite R N := hNfinite
  letI : Module.IsTorsionFree R N :=
    N.toSubmodule.instIsTorsionFree
  letI : Module.Free R N :=
    Module.free_of_finite_type_torsion_free' (R := R) (M := N)
  let D := Comodule.matrixCoefficientSubcoalgebra (R := R) (C := C) (M := N)
  refine ⟨D, inferInstance, ?_⟩
  let n : N := ⟨c, hcN⟩
  have hn := Comodule.matrixCoefficient_mem_subcoalgebra (R := R) (C := C) (M := N)
    ((Coalgebra.counit (R := R) (A := C)).comp (Subcomodule.subtype N).toLinearMap) n
  have hcoeff :
      Comodule.matrixCoefficient (R := R) (C := C)
          ((Coalgebra.counit (R := R) (A := C)).comp
            (Subcomodule.subtype N).toLinearMap) n = c := by
    rw [← Comodule.matrixCoefficient_map (R := R) (C := C)
      (Subcomodule.subtype N) (Coalgebra.counit (R := R) (A := C)) n]
    simp [n]
  rw [hcoeff] at hn
  exact hn

/-- Every element of a coalgebra over a field belongs to a finite-dimensional subcoalgebra. -/
theorem exists_finiteDimensional_subcoalgebra_mem {k : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] (c : C) :
    ∃ D : Subcoalgebra k C, FiniteDimensional k D.toSubmodule ∧ c ∈ D :=
  exists_finite_subcoalgebra_mem (R := k) (C := C) c

end Subcoalgebra

end TauCeti
