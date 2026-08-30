/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `invertibleTwo` supplies the `Invertible (2 : ℚ)` argument of `diagonalBivector`.
public import Mathlib.Algebra.CharP.Invertible
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegralLattice
-- Re-exports `TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction`, which supplies the
-- spin action itself.
public import TauCeti.RepresentationTheory.Spin.Weight

/-!
# The integral lattice in the spinor module

For a polarized rational quadratic space, the spinor module is the exterior algebra of the first
isotropic summand. A basis `b` of that summand gives it the coordinate integral lattice
`TauCeti.ExteriorAlgebra.integralLattice b`.

This file packages the Clifford elements whose spin action preserves that lattice as a subring.
The three primitive kinds of Clifford generator used in the Fock model belong to it: a basis
vector of the first isotropic summand acts by exterior multiplication (creation), its polar-dual
vector in the second summand acts by contraction by the corresponding coordinate (annihilation),
and a vector of the orthogonal remainder with integral coordinate acts by that integer times the
grade involution. Consequently every integral noncommutative polynomial in those operators
preserves the spinor lattice. This is the integrality mechanism used when the type-`B` and type-`D`
Chevalley root generators are written as quadratic combinations of them.

The Cartan direction is different: a coroot is not such a product, so the two combinations of
diagonal bivectors that an orthogonal coroot realizes -- twice one of them and a difference of two
-- are shown integral by their action on the exterior basis instead.

The identification of the orthogonal matrix model and its numbered root vectors with these
quadratic Clifford elements is carrier-specific and happens elsewhere; for type `B` it is
`TauCeti/RepresentationTheory/Spin/Polarization/TypeB/RootGenerators.lean`.

## Main definition and results

* `TauCeti.SpinPolarizationData.integralSpinActionSubring`: the Clifford elements whose action
  preserves the coordinate integral lattice.
* `TauCeti.SpinPolarizationData.integralSpinAction`: their induced integral representation on
  that lattice.
* `TauCeti.SpinPolarizationData.ι_basis_mem_integralSpinActionSubring`: creation operators are
  integral.
* `TauCeti.SpinPolarizationData.ι_dualVector_mem_integralSpinActionSubring`: annihilation
  operators are integral.
* `TauCeti.SpinPolarizationData.ι_line_mem_integralSpinActionSubring` and
  `TauCeti.SpinPolarizationData.ι_line_mem_integralSpinActionSubring_of_norm_one`: a remainder
  vector with integral coordinate is integral, which is the third primitive generator of an odd
  polarization; unit quadratic norm is one way to know the coordinate is integral.
* `TauCeti.SpinPolarizationData.mem_integralSpinActionSubring_of_forall_basis`: integrality may be
  checked on the exterior basis alone.
* `TauCeti.SpinPolarizationData.diagonalBivector_sub_diagonalBivector_mem_integralSpinActionSubring`
  and `TauCeti.SpinPolarizationData.two_smul_diagonalBivector_mem_integralSpinActionSubring`: the
  two combinations of diagonal bivectors realized by an orthogonal coroot are integral.

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

/-- **Integrality is checked on the exterior basis.** The coordinate lattice is spanned by the
exterior basis, so a Clifford element that carries every basis vector into the lattice preserves
it. -/
theorem mem_integralSpinActionSubring_of_forall_basis {c : CliffordAlgebra Q}
    (h : ∀ s : Finset ι, spinAction Q P c (b.ExteriorAlgebra s) ∈
      TauCeti.ExteriorAlgebra.integralLattice b) :
    c ∈ P.integralSpinActionSubring b := by
  rw [mem_integralSpinActionSubring]
  intro x hx
  exact TauCeti.ExteriorAlgebra.map_mem_integralLattice b
    ((spinAction Q P c).restrictScalars ℤ) h hx

/-- A vector of the orthogonal remainder with integral coordinate acts integrally on the spinor
lattice: its Clifford action is that integer times the grade involution. This is the third
primitive generator entering the odd, type-`B` polarization, alongside the creation and
annihilation operators of the two isotropic summands. -/
theorem ι_line_mem_integralSpinActionSubring (w : P.line) (m : ℤ)
    (hm : P.lineCoordinate w = (m : ℚ)) :
    CliffordAlgebra.ι Q (w : V) ∈ P.integralSpinActionSubring b := by
  rw [mem_integralSpinActionSubring]
  intro x hx
  rw [spinAction_ι_lineOperator, hm, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ m (TauCeti.ExteriorAlgebra.involute_mem_integralLattice b hx)

/-- **A remainder vector of unit quadratic norm acts integrally on the spinor lattice**: its
coordinate squares to `1`, hence is `±1`. -/
theorem ι_line_mem_integralSpinActionSubring_of_norm_one (w : P.line) (hw : Q (w : V) = 1) :
    CliffordAlgebra.ι Q (w : V) ∈ P.integralSpinActionSubring b := by
  have hsq : P.lineCoordinate w * P.lineCoordinate w = 1 := by rw [P.lineCoordinate_sq, hw]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact P.ι_line_mem_integralSpinActionSubring b w 1 (by simpa using h)
  · exact P.ι_line_mem_integralSpinActionSubring b w (-1) (by simpa using h)

/-! ### The two Cartan combinations -/

/-- **Twice a diagonal bivector preserves the coordinate integral lattice**, acting on the
exterior basis by `±1`. This is the combination realized by the short coroot of an odd orthogonal
Lie algebra: the spinor weights are half-integral, so only their doubles are integral. -/
theorem two_smul_diagonalBivector_mem_integralSpinActionSubring (i : ι) :
    (2 : ℚ) • P.diagonalBivector b i ∈ P.integralSpinActionSubring b := by
  apply P.mem_integralSpinActionSubring_of_forall_basis b
  intro s
  rw [P.spinAction_two_smul_diagonalBivector_basis b i s]
  have hb := TauCeti.ExteriorAlgebra.basis_mem_integralLattice b s
  split_ifs
  · rw [one_smul]
    exact hb
  · rw [neg_one_smul]
    exact neg_mem hb

/-- **A difference of two diagonal bivectors preserves the coordinate integral lattice**, acting
on the exterior basis by `0` or `±1`. This is the combination realized by the long coroot of an
orthogonal Lie algebra: the two half-integral weights differ by an integer. -/
theorem diagonalBivector_sub_diagonalBivector_mem_integralSpinActionSubring (i j : ι) :
    P.diagonalBivector b i - P.diagonalBivector b j ∈ P.integralSpinActionSubring b := by
  apply P.mem_integralSpinActionSubring_of_forall_basis b
  intro s
  rw [P.spinAction_diagonalBivector_sub_diagonalBivector_basis b i j s]
  have hhalf : (⅟(2 : ℚ)) = 2⁻¹ := invOf_eq_inv 2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, spinWeight ℚ s i - spinWeight ℚ s j = (m : ℚ) := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact ⟨0, by simp [spinWeight_of_mem hi, spinWeight_of_mem hj]⟩
    · exact ⟨1, by rw [spinWeight_of_mem hi, spinWeight_of_notMem hj, hhalf]; norm_num⟩
    · exact ⟨-1, by rw [spinWeight_of_notMem hi, spinWeight_of_mem hj, hhalf]; norm_num⟩
    · exact ⟨0, by simp [spinWeight_of_notMem hi, spinWeight_of_notMem hj]⟩
  rw [hm, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ m (TauCeti.ExteriorAlgebra.basis_mem_integralLattice b s)

end TauCeti.SpinPolarizationData
