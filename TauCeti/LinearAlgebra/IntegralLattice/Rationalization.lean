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
in `ℚ ⊗[ℤ] M`. Its carrier is the image of `M` under `m ↦ 1 ⊗ₜ m`, and its restricted integral
form recovers the original form. Rationalizing that embedded carrier gives back the original tensor
product, so the abstract and embedded models are inverse constructions at the level of forms.

Mathlib already supplies `LinearMap.BilinForm.baseChange`; the point here is to connect that
abstract tensor-product construction to the embedded-carrier model used by integral lattices.
In particular, no choice of carrier basis appears in the resulting equivalence or its
characteristic equations.

## Main results

* `TauCeti.IntegralLattice.form_rationalizationEquiv`: the base-changed integral form equals
  the ambient form under the equivalence.
* `TauCeti.IntegralLattice.rationalizationIsometry`: this equivalence is an isometry from
  `L.integralForm.baseChange ℚ` to `L.form`.
* `TauCeti.IntegralLattice.ofIntegralForm`: the integral lattice obtained by rationalizing an
  abstract finite free integral form.
* `TauCeti.IntegralLattice.ofIntegralForm.carrierEquiv`: the original module identified with the
  embedded carrier.
* `TauCeti.IntegralLattice.ofIntegralForm.carrierIsometry`: that equivalence as an isometry of
  integral forms.

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

omit [Module.Free ℤ M] [Module.Finite ℤ M] in
private theorem isSymm_baseChange (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (B.baseChange ℚ).IsSymm := by
  constructor
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul q m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      rw [map_add, map_add, LinearMap.add_apply, hy₁, hy₂]
    | tmul r n =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        hB.eq m n, mul_comm q r]

/-- Rationalizing an integral symmetric form on a finite free `ℤ`-module produces an integral
lattice in its scalar extension to `ℚ`. -/
noncomputable def ofIntegralForm (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    IntegralLattice (ℚ ⊗[ℤ] M) :=
  ofBasis ((Module.Free.chooseBasis ℤ M).baseChange ℚ) (B.baseChange ℚ)
    (isSymm_baseChange B hB)
    fun i j ↦ by
      rw [Basis.baseChange_apply, Basis.baseChange_apply,
        LinearMap.BilinForm.baseChange_tmul]
      simp only [one_mul, Int.smul_one_eq_cast, Submodule.mem_one]
      exact ⟨B (Module.Free.chooseBasis ℤ M i) (Module.Free.chooseBasis ℤ M j), rfl⟩

@[simp]
theorem ofIntegralForm_form (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (ofIntegralForm B hB).form = B.baseChange ℚ :=
  IntegralLattice.ofBasis_form _ _ _ _

private theorem ofIntegralForm_carrier (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (ofIntegralForm B hB).carrier =
      Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ M).baseChange ℚ)) := by
  unfold ofIntegralForm
  exact IntegralLattice.ofBasis_carrier _ _ _ _

namespace ofIntegralForm

/-- The carrier basis of a rationalized integral form induced by the chosen basis of the abstract
module. -/
noncomputable def basis (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ (ofIntegralForm B hB) :=
  ((Module.Free.chooseBasis ℤ M).baseChange ℚ).restrictScalars ℤ |>.map
    (LinearEquiv.ofEq
      (Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ M).baseChange ℚ)))
      (ofIntegralForm B hB).carrier (ofIntegralForm_carrier B hB).symm)

/-- A basis vector of the embedded carrier is the unit pure tensor of the corresponding abstract
basis vector. -/
@[simp]
theorem coe_basis (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (i : Module.Free.ChooseBasisIndex ℤ M) :
    (basis B hB i : ℚ ⊗[ℤ] M) = 1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ M i := by
  rw [basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply, Basis.baseChange_apply]

/-- The abstract integral module is canonically equivalent to the carrier of its rationalized
integral lattice. -/
noncomputable def carrierEquiv (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    M ≃ₗ[ℤ] ofIntegralForm B hB :=
  (Module.Free.chooseBasis ℤ M).equiv (basis B hB) (Equiv.refl _)

/-- The carrier equivalence sends an abstract vector to its unit pure tensor. -/
@[simp]
theorem coe_carrierEquiv_apply (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : M) :
    (carrierEquiv B hB x : ℚ ⊗[ℤ] M) = 1 ⊗ₜ[ℤ] x := by
  have hmap :
      (Submodule.subtype (ofIntegralForm B hB).carrier).comp
          (carrierEquiv B hB).toLinearMap =
        (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom.toIntLinearMap := by
    apply (Module.Free.chooseBasis ℤ M).ext
    intro i
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, carrierEquiv,
      Basis.equiv_apply, Equiv.refl_apply]
    -- Forget the implementation wrappers on the subtype inclusion and integer-linear map.
    change (basis B hB i : ℚ ⊗[ℤ] M) = 1 ⊗ₜ[ℤ] Module.Free.chooseBasis ℤ M i
    exact coe_basis B hB i
  exact LinearMap.congr_fun hmap x

/-- The carrier of a rationalized integral form consists exactly of the unit pure tensors. -/
theorem mem_carrier_iff (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (x : ℚ ⊗[ℤ] M) :
    x ∈ (ofIntegralForm B hB).carrier ↔ ∃ m : M, 1 ⊗ₜ[ℤ] m = x := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := (carrierEquiv B hB).surjective
      (⟨x, hx⟩ : ofIntegralForm B hB)
    exact ⟨m, (coe_carrierEquiv_apply B hB m).symm.trans (congrArg Subtype.val hm)⟩
  · rintro ⟨m, rfl⟩
    rw [← coe_carrierEquiv_apply B hB m]
    exact (carrierEquiv B hB m).2

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

/-- Base-changing the carrier equivalence and then applying the lattice's rationalization
equivalence is the identity on the original rationalization. -/
theorem carrierEquiv_baseChange_trans_rationalizationEquiv
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (LinearEquiv.baseChange ℤ ℚ M (ofIntegralForm B hB) (carrierEquiv B hB)).trans
      (Submodule.rationalizationEquiv (ofIntegralForm B hB).carrier) = LinearEquiv.refl ℚ _ := by
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q m =>
    rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      Submodule.rationalizationEquiv_tmul, coe_carrierEquiv_apply,
      LinearEquiv.refl_apply]
    exact (tmul_eq_smul_one_tmul q m).symm

end ofIntegralForm

end AbstractIntegralForm

end IntegralLattice

end TauCeti
