/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegralLattice
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-!
# The integral lattice in the spinor module

For a polarized rational quadratic space, the spinor module is the exterior algebra of the first
isotropic summand. A basis `b` of that summand gives it the coordinate integral lattice
`TauCeti.ExteriorAlgebra.integralLattice b`.

This file packages the Clifford elements whose spin action preserves that lattice as a subring.
The two primitive kinds of Clifford generator used in the Fock model belong to it: a basis vector
of the first isotropic summand acts by exterior multiplication (creation), and its polar-dual
vector in the second summand acts by contraction by the corresponding coordinate (annihilation).
Consequently every integral noncommutative polynomial in creation and annihilation operators
preserves the spinor lattice. This is the integrality mechanism used when the type-`B` and type-`D`
Chevalley root generators are written as quadratic combinations of those operators.

No claim about those Chevalley generators is made here: identifying the orthogonal matrix model
and its numbered root vectors with these quadratic Clifford elements is the next carrier-specific
step.

## Main definition and results

* `TauCeti.SpinPolarizationData.integralSpinActionSubring`: the Clifford elements whose action
  preserves the coordinate integral lattice.
* `TauCeti.SpinPolarizationData.integralSpinAction`: their induced integral representation on
  that lattice.
* `TauCeti.SpinPolarizationData.ι_basis_mem_integralSpinActionSubring`: creation operators are
  integral.
* `TauCeti.SpinPolarizationData.ι_dualVector_mem_integralSpinActionSubring`: annihilation
  operators are integral.

## Roadmap

This supplies the shared integral-spinor-lattice prerequisite for the full-weight type-`B` and
type-`D` Chevalley carriers in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Those carriers
are consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, §20.1.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {Q : QuadraticForm ℚ V} (P : SpinPolarizationData Q)
variable {ι : Type v} [LinearOrder ι] (b : Module.Basis ι ℚ P.W)

/-- The subring of the Clifford algebra consisting of the elements whose spin action preserves
the coordinate integral lattice in the spinor module. -/
def integralSpinActionSubring : Subring (CliffordAlgebra Q) where
  carrier := {c | Set.MapsTo (spinAction Q P c)
    (TauCeti.ExteriorAlgebra.integralLattice b)
    (TauCeti.ExteriorAlgebra.integralLattice b)}
  zero_mem' x hx := by
    rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  one_mem' x hx := by
    rw [map_one, Module.End.one_apply]
    exact hx
  add_mem' {c d} hc hd x hx := by
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hc hx) (hd hx)
  neg_mem' {c} hc x hx := by
    rw [map_neg, LinearMap.neg_apply]
    exact neg_mem (hc hx)
  mul_mem' {c d} hc hd x hx := by
    rw [map_mul, Module.End.mul_apply]
    exact hc (hd hx)

/-- Membership in the integral-action subring means precisely that the spin action preserves the
coordinate integral lattice. -/
@[simp]
theorem mem_integralSpinActionSubring {c : CliffordAlgebra Q} :
    c ∈ P.integralSpinActionSubring b ↔
      Set.MapsTo (spinAction Q P c)
        (TauCeti.ExteriorAlgebra.integralLattice b)
        (TauCeti.ExteriorAlgebra.integralLattice b) :=
  Iff.rfl

/-- The integral representation obtained by restricting the spin action to the Clifford elements
that preserve the coordinate integral lattice. -/
noncomputable def integralSpinAction :
    P.integralSpinActionSubring b →+*
      Module.End ℤ (TauCeti.ExteriorAlgebra.integralLattice b) where
  toFun c :=
    { toFun := fun x =>
        ⟨spinAction Q P (c : CliffordAlgebra Q) x,
          c.property x.property⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun z x => Subtype.ext
        (map_zsmul (spinAction Q P (c : CliffordAlgebra Q)) z
          (x : ExteriorAlgebra ℚ P.W)) }
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' := fun c d => LinearMap.ext fun x => Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_add' := fun c d => LinearMap.ext fun x => Subtype.ext (by simp)

/-- The ambient value of the integral spin action is the original rational spin action. -/
@[simp]
theorem coe_integralSpinAction_apply (c : P.integralSpinActionSubring b)
    (x : TauCeti.ExteriorAlgebra.integralLattice b) :
    ((P.integralSpinAction b c x : TauCeti.ExteriorAlgebra.integralLattice b) :
        ExteriorAlgebra ℚ P.W) =
      spinAction Q P (c : CliffordAlgebra Q) (x : ExteriorAlgebra ℚ P.W) :=
  by
    rw [integralSpinAction]
    rfl

/-- A basis vector in the first isotropic summand acts integrally on the spinor lattice: its
Clifford action is exterior multiplication by that basis vector. -/
theorem ι_basis_mem_integralSpinActionSubring (i : ι) :
    CliffordAlgebra.ι Q (b i : V) ∈ P.integralSpinActionSubring b := by
  rw [mem_integralSpinActionSubring]
  intro x hx
  rw [spinAction_ι_wedge]
  exact TauCeti.ExteriorAlgebra.ι_basis_mul_mem_integralLattice b i hx

/-- The polar-dual basis vector in the second isotropic summand acts integrally on the spinor
lattice: its Clifford action is contraction by the corresponding basis coordinate. -/
theorem ι_dualVector_mem_integralSpinActionSubring (i : ι) :
    CliffordAlgebra.ι Q (P.dualVector b i : V) ∈ P.integralSpinActionSubring b := by
  rw [mem_integralSpinActionSubring]
  intro x hx
  rw [spinAction_ι_contract, P.pairingEquiv_dualVector]
  exact TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice b i hx

end TauCeti.SpinPolarizationData
