/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import TauCeti.LinearAlgebra.BilinearForm.DualLattice
public import TauCeti.Algebra.Module.Lattice

/-!
# Duals of integral lattices

For an integral lattice `L` in a rational vector space with nondegenerate form, its dual carrier
is the submodule

```text
Lᵛ = {x | B(x, y) ∈ ℤ for every y ∈ L}.
```

This file keeps the dual as a submodule of the same rational ambient space.  It is not packaged as
an `IntegralLattice`: the restriction of the form to `Lᵛ` need not be integral.  For example,
the dual of the rank-one lattice of Gram matrix `(2)` has Gram matrix `(1 / 2)`.

Mathlib proves that the dual of the integral span of a rational basis is the integral span of the
bilinear dual basis.  Applying that result to the basis supplied by `Submodule.IsLattice` proves
that `Lᵛ` is again a full lattice.  It also identifies the natural pairing map
`Lᵛ → Module.Dual ℤ L` as an equivalence and proves reflexivity `(Lᵛ)ᵛ = L`.

## Main declarations

* `TauCeti.IntegralLattice.dualCarrier`: the dual lattice as a submodule of the common ambient
  rational vector space.
* `TauCeti.IntegralLattice.dualCarrier_def`: the defining equation
  `L.dualCarrier = L.form.dualSubmodule L.carrier`.
* `TauCeti.IntegralLattice.le_dualCarrier`: the inclusion `L.carrier ≤ L.dualCarrier`.
* `TauCeti.IntegralLattice.instIsLatticeDualCarrier`: the dual carrier is a full lattice.
* `TauCeti.IntegralLattice.finrank_dualCarrier`: the dual carrier has the same rank as the ambient
  rational space.
* `TauCeti.IntegralLattice.dualPairing`: the pairing of a dual-lattice vector with a lattice vector,
  valued in `ℤ`.
* `TauCeti.IntegralLattice.dualPairingEquiv`: the perfect integral pairing
  `Lᵛ ≃ Module.Dual ℤ L`.
* `TauCeti.IntegralLattice.dualBasisElem`: embedding of a bilinear dual-basis vector into the dual
  carrier.
* `TauCeti.IntegralLattice.dualCarrierBasis`: the dual basis of `L.dualCarrier` corresponding to a
  chosen basis of `L.carrier`.
* `TauCeti.IntegralLattice.dualSubmodule_flip_dualCarrier`: double duality with `form.flip`.
* `TauCeti.IntegralLattice.dualSubmodule_dualCarrier`: dualizing twice recovers `L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2)
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`
-/

public section

open Module

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

/-- The dual carrier of an integral lattice:
`x` belongs to it exactly when `L.form x y` is integral for every `y ∈ L`. -/
abbrev dualCarrier (L : IntegralLattice V) : Submodule ℤ V :=
  L.form.dualSubmodule L.carrier

/-- The defining equation identifying `L.dualCarrier` with `L.form.dualSubmodule L.carrier`. -/
theorem dualCarrier_def (L : IntegralLattice V) :
    L.dualCarrier = L.form.dualSubmodule L.carrier := rfl

/-- The carrier of an integral lattice is contained in its dual carrier. -/
theorem le_dualCarrier (L : IntegralLattice V) : L.carrier ≤ L.dualCarrier :=
  L.le_dual

/-- The integral span of the rational basis obtained from Mathlib's chosen basis of `L` is the
carrier itself. -/
theorem span_range_rationalBasis (L : IntegralLattice V) :
    Submodule.span ℤ (Set.range L.rationalBasis) = L.carrier := by
  have h : ⇑L.rationalBasis = ⇑((Module.Free.chooseBasis ℤ L.carrier).extendOfIsLattice ℚ) :=
    funext fun i ↦ by rw [L.rationalBasis_apply, Basis.extendOfIsLattice_apply]
  rw [h]
  exact Basis.span_range_extendOfIsLattice (Module.Free.chooseBasis ℤ L.carrier)

open Classical in
/-- The dual carrier is the integral span of the bilinear dual basis to the rational basis
extending any `ℤ`-basis of the carrier. -/
theorem dualCarrier_eq_span_dualBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) :
    L.dualCarrier = Submodule.span ℤ
      (Set.range (L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ))) := by
  calc
    L.dualCarrier = L.form.dualSubmodule
        (Submodule.span ℤ (Set.range (b.extendOfIsLattice ℚ))) :=
      congrArg L.form.dualSubmodule (Basis.span_range_extendOfIsLattice b).symm
    _ = _ := L.form.dualSubmodule_span_of_basis L.form_nondegenerate (b.extendOfIsLattice ℚ)

open Classical in
/-- The dual carrier of a nondegenerate integral lattice is a full lattice in the same rational
ambient space. -/
noncomputable instance instIsLatticeDualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualCarrier.IsLattice ℚ := by
  let b := Module.Free.chooseBasis ℤ L.carrier
  rw [L.dualCarrier_eq_span_dualBasis b]
  exact isLattice_span_basis (L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ))

/-- The dual carrier has the same rank as the ambient rational space. -/
theorem finrank_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    Module.finrank ℤ L.dualCarrier = Module.finrank ℚ V :=
  Submodule.IsLattice.finrank_eq_finrank L.dualCarrier

/-- The pairing of a dual-lattice vector with a lattice vector, valued in `ℤ`. -/
noncomputable def dualPairing (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] Module.Dual ℤ L :=
  L.form.dualSubmoduleToDual L.carrier

/-- The integral dual pairing becomes the ambient rational form after casting to `ℚ`. -/
@[simp]
theorem dualPairing_cast (L : IntegralLattice V) (x : L.dualCarrier) (y : L) :
    (L.dualPairing x y : ℚ) = L.form x y := by
  rw [dualPairing, LinearMap.BilinForm.dualSubmoduleToDual_apply_apply]
  simpa using L.form.dualSubmoduleParing_spec x y

/-- The pairing with the carrier is perfect: every integral functional on `L` is represented by a
unique vector of `Lᵛ`. -/
noncomputable def dualPairingEquiv (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualCarrier ≃ₗ[ℤ] Module.Dual ℤ L :=
  LinearMap.BilinForm.dualSubmoduleEquivDual L.form L.form_nondegenerate L.carrier

/-- The perfect pairing equivalence has `dualPairing` as its underlying linear map. -/
@[simp]
theorem dualPairingEquiv_toLinearMap (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualPairingEquiv.toLinearMap = L.dualPairing := by
  apply LinearMap.ext
  intro x
  exact LinearMap.BilinForm.dualSubmoduleEquivDual_apply L.form L.form_nondegenerate L.carrier x

/-- The perfect pairing equivalence agrees with the ambient rational form after casting to `ℚ`. -/
@[simp]
theorem dualPairingEquiv_cast (L : IntegralLattice V) [L.IsNondegenerate]
    (x : L.dualCarrier) (y : L) :
    (L.dualPairingEquiv x y : ℚ) = L.form x y := by
  have hx : L.dualPairingEquiv x = L.dualPairing x :=
    LinearMap.congr_fun L.dualPairingEquiv_toLinearMap x
  rw [hx]
  exact L.dualPairing_cast x y

open Classical in
/-- A vector of the bilinear dual basis corresponding to an arbitrary carrier basis,
regarded as an element of the dual carrier. -/
noncomputable def dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) (i : ι) : L.dualCarrier :=
  ⟨L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ) i, by
    rw [L.dualCarrier_eq_span_dualBasis b]
    exact Submodule.subset_span (Set.mem_range_self i)⟩

open Classical in
/-- The underlying rational vector of `dualBasisElem` is the corresponding vector of the
bilinear dual basis. -/
@[simp]
theorem coe_dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) (i : ι) :
    (L.dualBasisElem b i : V) =
      L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ) i := by
  unfold dualBasisElem
  rfl

open Classical in
/-- Under the perfect-pairing equivalence, the bilinear dual basis of the ambient space is sent to
the module-dual basis of the carrier. -/
@[simp]
theorem dualPairingEquiv_dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) (i : ι) :
    L.dualPairingEquiv (L.dualBasisElem b i) = b.dualBasis i := by
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  apply Int.cast_injective (α := ℚ)
  rw [L.dualPairingEquiv_cast, L.coe_dualBasisElem]
  calc
    L.form (L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ) i) (b j : V) =
        L.form (L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ) i)
          ((b.extendOfIsLattice ℚ) j) := by rw [Basis.extendOfIsLattice_apply ℚ b j]
    _ = if j = i then 1 else 0 :=
      L.form.apply_dualBasis_left L.form_nondegenerate (b.extendOfIsLattice ℚ) i j
    _ = ((b.dualBasis i (b j) : ℤ) : ℚ) := by
      simp only [Basis.dualBasis_apply, Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp_all

open Classical in
/-- The basis of the dual carrier corresponding to a `ℤ`-basis of `L.carrier`. -/
noncomputable def dualCarrierBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) :
    Basis ι ℤ L.dualCarrier :=
  b.dualBasis.map L.dualPairingEquiv.symm

open Classical in
/-- The basis of the dual carrier corresponding to a `ℤ`-basis `b` consists of the ambient
bilinear dual-basis vectors. -/
@[simp]
theorem dualCarrierBasis_apply (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L.carrier) (i : ι) :
    L.dualCarrierBasis b i = L.dualBasisElem b i := by
  apply L.dualPairingEquiv.injective
  rw [dualCarrierBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    L.dualPairingEquiv_dualBasisElem]

/-- Taking the flipped dual submodule of the dual carrier recovers the original carrier. -/
theorem dualSubmodule_flip_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.form.flip.dualSubmodule L.dualCarrier = L.carrier :=
  LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule L.form L.form_nondegenerate L.carrier

/-- Taking the dual submodule twice recovers the original carrier. -/
@[simp]
theorem dualSubmodule_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.form.dualSubmodule L.dualCarrier = L.carrier := by
  rw [← L.form_flip]
  exact L.dualSubmodule_flip_dualCarrier

/-- A vector pairs integrally with every vector of the dual carrier exactly when it belongs to the
original carrier. -/
-- This is deliberately not a simp lemma: `LinearMap.BilinForm.mem_dualSubmodule` already expands
-- the quantified domain on the left, so the simp-normal-form linter rejects this statement as a
-- simp rule.
theorem forall_form_mem_one_dualCarrier_iff (L : IntegralLattice V) [L.IsNondegenerate]
    (x : V) :
    (∀ y ∈ L.dualCarrier, L.form x y ∈ (1 : Submodule ℤ ℚ)) ↔ x ∈ L.carrier := by
  rw [← LinearMap.BilinForm.mem_dualSubmodule, L.dualSubmodule_dualCarrier]

end IntegralLattice

end TauCeti
