/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.IntegralLattice.Basic

/-!
# Rationalizing an integral lattice form

Let `L` be a full integral lattice in a rational vector space `V`. The carrier's canonical
base-change equivalence identifies `V` with the scalar extension `ℚ ⊗[ℤ] L`. This file proves
that this equivalence identifies the scalar extension of `L.integralForm` with the ambient rational
form `L.form`.

Conversely, an integral symmetric form on a finite free `ℤ`-module `M` defines an integral lattice
in `ℚ ⊗[ℤ] M`. Its carrier consists exactly of the unit pure tensors `1 ⊗ₜ m`, so that
`TauCeti.TensorProduct.unitTmulEquiv` identifies `M` with it, and its restricted integral form
recovers the original form. Base-changing that carrier equivalence and then rationalizing is the
identity on `ℚ ⊗[ℤ] M`; at the level of forms the two models are related by the isometries
`rationalizationIsometry` and `carrierIsometry`.

Mathlib already supplies `LinearMap.BilinForm.baseChange`; the point here is to connect that
abstract tensor-product construction to the embedded-carrier model used by integral lattices.
The lattice `ofIntegralForm` is built from an arbitrary chosen basis of `M`, but no choice of basis
appears in the resulting equivalences or in the equations characterizing them.

## Main results

* `TauCeti.IntegralLattice.form_rationalizationEquiv`: the base-changed integral form equals
  the ambient form under the equivalence.
* `TauCeti.IntegralLattice.rationalizationIsometry`: this equivalence is an isometry from
  `L.integralForm.baseChange ℚ` to `L.form`.
* `TauCeti.IntegralLattice.ofIntegralForm`: the integral lattice obtained by rationalizing an
  abstract finite free integral form.
* `TauCeti.IntegralLattice.mem_ofIntegralForm_carrier_iff`: its carrier consists exactly of the
  unit pure tensors.
* `TauCeti.IntegralLattice.ofIntegralForm.carrierEquiv`: the original module identified with the
  embedded carrier.
* `TauCeti.IntegralLattice.ofIntegralForm.carrierIsometry`: that equivalence as an isometry of
  integral forms.
* `TauCeti.IntegralLattice.ofIntegralForm.carrierEquiv_baseChange_trans_rationalizationEquiv`:
  base-changing the carrier equivalence and then rationalizing is the identity.

## References

This is the rational-extension target in Layer 1 of
`TauCetiRoadmap/IntegralLattices/README.md`. See W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

/-- The scalar extension of the carrier's integral form is the ambient rational form under the
canonical rationalization equivalence. -/
@[simp]
theorem form_rationalizationEquiv (L : IntegralLattice V) (x y : ℚ ⊗[ℤ] L) :
    L.form (Submodule.rationalizationEquiv L.carrier x)
        (Submodule.rationalizationEquiv L.carrier y) =
      L.integralForm.baseChange ℚ x y := by
  let h := Submodule.IsLattice.isBaseChange_subtype L.carrier
  -- The generic equivalence is opaque across modules; identify it by its pure-tensor equation.
  have he : Submodule.rationalizationEquiv L.carrier = h.equiv := by
    apply LinearEquiv.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul q z =>
      rw [Submodule.rationalizationEquiv_tmul, h.equiv_tmul]
      rfl
  rw [he]
  exact IsBaseChange.bilinForm_baseChange h L.integralForm L.form
    (fun z w ↦ (L.integralForm_cast z w).symm) x y

/-- The canonical rationalization is an isometry from the base-changed integral form to the
ambient rational form. -/
noncomputable def rationalizationIsometry (L : IntegralLattice V) :
    (L.integralForm.baseChange ℚ).IsometryEquiv L.form where
  toLinearEquiv := Submodule.rationalizationEquiv L.carrier
  map_app' := L.form_rationalizationEquiv

/-- Evaluating the rationalization isometry on a tensor product element coincides with the
rationalization equivalence. -/
-- BilinForm.IsometryEquiv has no toLinearEquiv lemma; definition unfolding is canonical.
@[simp]
theorem rationalizationIsometry_apply (L : IntegralLattice V) (x : ℚ ⊗[ℤ] L) :
    L.rationalizationIsometry x = Submodule.rationalizationEquiv L.carrier x := by
  rfl

/-- Evaluating the inverse rationalization isometry coincides with the inverse rationalization
equivalence. -/
-- BilinForm.IsometryEquiv has no symm_toLinearEquiv lemma; definition unfolding is canonical.
@[simp]
theorem rationalizationIsometry_symm_apply (L : IntegralLattice V) (y : V) :
    L.rationalizationIsometry.symm y = (Submodule.rationalizationEquiv L.carrier).symm y := by
  rfl

section AbstractIntegralForm

variable {M : Type u} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Rationalizing an integral symmetric form on a finite free `ℤ`-module produces an integral
lattice in its scalar extension to `ℚ`. -/
noncomputable def ofIntegralForm (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    IntegralLattice (ℚ ⊗[ℤ] M) :=
  ofBasis ((Module.Free.chooseBasis ℤ M).baseChange ℚ) (B.baseChange ℚ)
    (LinearMap.BilinForm.isSymm_iff.mpr
      (LinearMap.BilinForm.IsSymm.baseChange ℚ (LinearMap.BilinForm.isSymm_iff.mp hB)))
    fun i j ↦ by
      rw [Basis.baseChange_apply, Basis.baseChange_apply,
        LinearMap.BilinForm.baseChange_tmul]
      simp only [one_mul, Int.smul_one_eq_cast, Submodule.mem_one]
      exact ⟨B (Module.Free.chooseBasis ℤ M i) (Module.Free.chooseBasis ℤ M j), by simp⟩

/-- The ambient rational form of a rationalized integral form is the base change to `ℚ`. -/
@[simp]
theorem ofIntegralForm_form (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (ofIntegralForm B hB).form = B.baseChange ℚ :=
  IntegralLattice.ofBasis_form _ _ _ _

/-- The carrier of a rationalized integral form is the lattice of unit pure tensors. -/
theorem ofIntegralForm_carrier (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (ofIntegralForm B hB).carrier = LinearMap.range (TensorProduct.mk ℤ ℚ M 1) :=
  (IntegralLattice.ofBasis_carrier _ _ _ _).trans
    (TensorProduct.range_mk_one_eq_span (Module.Free.chooseBasis ℤ M)).symm

/-- The carrier of a rationalized integral form consists exactly of the unit pure tensors. -/
@[simp]
theorem mem_ofIntegralForm_carrier_iff (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (x : ℚ ⊗[ℤ] M) : x ∈ (ofIntegralForm B hB).carrier ↔ ∃ m : M, 1 ⊗ₜ[ℤ] m = x := by
  rw [ofIntegralForm_carrier]
  exact LinearMap.mem_range

namespace ofIntegralForm

/-- The abstract integral module is canonically equivalent to the carrier of its rationalized
integral lattice: this is `TauCeti.TensorProduct.unitTmulEquiv` read through
`ofIntegralForm_carrier`. -/
noncomputable def carrierEquiv (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    M ≃ₗ[ℤ] ofIntegralForm B hB :=
  (TensorProduct.unitTmulEquiv ℤ ℚ M).trans
    (LinearEquiv.ofEq _ _ (ofIntegralForm_carrier B hB).symm)

/-- The carrier equivalence sends an abstract vector to its unit pure tensor. -/
@[simp]
theorem coe_carrierEquiv_apply (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : M) :
    (carrierEquiv B hB x : ℚ ⊗[ℤ] M) = 1 ⊗ₜ[ℤ] x :=
  (LinearEquiv.coe_ofEq_apply (ofIntegralForm_carrier B hB).symm _).trans
    (TensorProduct.coe_unitTmulEquiv_apply x)

/-- The inverse carrier equivalence recovers an abstract vector from its unit pure tensor. -/
@[simp]
theorem carrierEquiv_symm_tmul (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : M)
    (h : (1 : ℚ) ⊗ₜ[ℤ] x ∈ (ofIntegralForm B hB).carrier) :
    (carrierEquiv B hB).symm ⟨1 ⊗ₜ[ℤ] x, h⟩ = x := by
  apply (carrierEquiv B hB).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (coe_carrierEquiv_apply B hB x).symm

/-- Restricting the rationalized form along the carrier equivalence recovers the original
integral form. -/
@[simp]
theorem integralForm_carrierEquiv (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x y : M) :
    (ofIntegralForm B hB).integralForm (carrierEquiv B hB x) (carrierEquiv B hB y) = B x y := by
  apply Int.cast_injective (α := ℚ)
  rw [IntegralLattice.integralForm_cast, ofIntegralForm_form,
    coe_carrierEquiv_apply, coe_carrierEquiv_apply,
    LinearMap.BilinForm.baseChange_tmul]
  simp

/-- The carrier equivalence is an isometry from the abstract integral form to the restricted form
of its rationalized lattice. -/
noncomputable def carrierIsometry (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    B.IsometryEquiv (ofIntegralForm B hB).integralForm where
  toLinearEquiv := carrierEquiv B hB
  map_app' := integralForm_carrierEquiv B hB

/-- The carrier isometry acts through the canonical carrier equivalence. -/
@[simp]
theorem carrierIsometry_apply (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : M) :
    carrierIsometry B hB x = carrierEquiv B hB x :=
  (rfl)

/-- Evaluating the inverse carrier isometry coincides with the inverse carrier equivalence. -/
-- BilinForm.IsometryEquiv has no symm_toLinearEquiv lemma; definition unfolding is canonical.
@[simp]
theorem carrierIsometry_symm_apply (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (y : ofIntegralForm B hB) :
    (carrierIsometry B hB).symm y = (carrierEquiv B hB).symm y :=
  (rfl)

/-- Base-changing the carrier equivalence and then applying the lattice's rationalization
equivalence returns the vector one started from. -/
@[simp]
theorem rationalizationEquiv_baseChange_carrierEquiv
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : ℚ ⊗[ℤ] M) :
    Submodule.rationalizationEquiv (ofIntegralForm B hB).carrier
        (LinearEquiv.baseChange ℤ ℚ M _ (carrierEquiv B hB) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q m =>
    rw [LinearEquiv.baseChange_tmul, Submodule.rationalizationEquiv_tmul,
      coe_carrierEquiv_apply]
    exact (tmul_eq_smul_one_tmul q m).symm

/-- The bundled form of `rationalizationEquiv_baseChange_carrierEquiv`: base-changing the carrier
equivalence and then rationalizing is the identity on the original rationalization. -/
theorem carrierEquiv_baseChange_trans_rationalizationEquiv
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (LinearEquiv.baseChange ℤ ℚ M (ofIntegralForm B hB) (carrierEquiv B hB)).trans
      (Submodule.rationalizationEquiv (ofIntegralForm B hB).carrier) = LinearEquiv.refl ℚ _ :=
  LinearEquiv.ext (rationalizationEquiv_baseChange_carrierEquiv B hB)

end ofIntegralForm

end AbstractIntegralForm

end IntegralLattice

end TauCeti
