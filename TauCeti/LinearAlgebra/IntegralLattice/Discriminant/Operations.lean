/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.OrthogonalSum
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# Discriminant forms under orthogonal sums and negation

The dual carrier of an orthogonal sum is the product of the two dual carriers.  Passing the
embedded original carriers through this equivalence and then quotienting gives the canonical
equivalence

```text
A_(L ⊥ M) ≃ A_L × A_M.
```

This file proves that the equivalence is an isometry for both discriminant pairings and, when the
lattices are even, their half-norm quadratic forms.  It also identifies the discriminant form of
the form-negated lattice `-L`: the quotient group is unchanged, while both its bilinear and
quadratic forms are negated.

## Main declarations

* `TauCeti.IntegralLattice.discriminantGroupOrthogonalSumEquiv`: the discriminant group of an
  orthogonal sum is the product of the discriminant groups.
* `TauCeti.IntegralLattice.discriminantBilinearIsometryOrthogonalSum`: the preceding equivalence
  preserves the product discriminant pairing.
* `TauCeti.IntegralLattice.discriminantQuadraticIsometryOrthogonalSum`: the corresponding
  isometry of half-norm discriminant quadratic modules.
* `TauCeti.IntegralLattice.discriminantBilinearIsometryNeg` and
  `TauCeti.IntegralLattice.discriminantQuadraticIsometryNeg`: form negation negates the
  discriminant pairing and quadratic map.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layers 2 and 3.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ## Orthogonal sums -/

/-- Membership in the dual carrier of an orthogonal sum is componentwise membership in the two
dual carriers. -/
theorem mem_dualCarrier_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W)
    (x : V × W) :
    x ∈ (L.orthogonalSum M).dualCarrier ↔ x.1 ∈ L.dualCarrier ∧ x.2 ∈ M.dualCarrier := by
  rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx
    constructor
    · rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      have hmem : (y, 0) ∈ (L.orthogonalSum M).carrier := by
        rw [orthogonalSum_carrier, Submodule.mem_prod]
        exact ⟨hy, M.carrier.zero_mem⟩
      have h := hx (y, 0) hmem
      simpa using h
    · rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      have hmem : (0, y) ∈ (L.orthogonalSum M).carrier := by
        rw [orthogonalSum_carrier, Submodule.mem_prod]
        exact ⟨L.carrier.zero_mem, hy⟩
      have h := hx (0, y) hmem
      simpa using h
  · rintro ⟨hx, hy⟩ z hz
    rw [orthogonalSum_carrier, Submodule.mem_prod] at hz
    rw [orthogonalSum_form, orthogonalSumForm_apply]
    exact Submodule.add_mem _ (hx z.1 hz.1) (hy z.2 hz.2)

/-- The dual carrier of an orthogonal sum is the product of the two dual carriers. -/
@[simp]
theorem dualCarrier_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).dualCarrier = L.dualCarrier.prod M.dualCarrier := by
  ext x
  rw [L.mem_dualCarrier_orthogonalSum M x, Submodule.mem_prod]

/-- The dual carrier of an orthogonal sum is canonically the product of the dual carriers. -/
def orthogonalSumDualCarrierEquiv (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).dualCarrier ≃ₗ[ℤ] L.dualCarrier × M.dualCarrier where
  toFun x :=
    (⟨x.1.1, (L.mem_dualCarrier_orthogonalSum M x.1).mp x.2 |>.1⟩,
      ⟨x.1.2, (L.mem_dualCarrier_orthogonalSum M x.1).mp x.2 |>.2⟩)
  invFun x :=
    ⟨(x.1, x.2), (L.mem_dualCarrier_orthogonalSum M (x.1, x.2)).mpr ⟨x.1.2, x.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dual-carrier product equivalence acts by taking the two ambient coordinates. -/
@[simp]
theorem orthogonalSumDualCarrierEquiv_apply (L : IntegralLattice V) (M : IntegralLattice W)
    (x : (L.orthogonalSum M).dualCarrier) :
    L.orthogonalSumDualCarrierEquiv M x =
      (⟨x.1.1, (L.mem_dualCarrier_orthogonalSum M x.1).mp x.2 |>.1⟩,
        ⟨x.1.2, (L.mem_dualCarrier_orthogonalSum M x.1).mp x.2 |>.2⟩) :=
  by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The inverse dual-carrier product equivalence acts by assembling the two ambient coordinates. -/
@[simp]
theorem coe_orthogonalSumDualCarrierEquiv_symm_apply
    (L : IntegralLattice V) (M : IntegralLattice W) (x : L.dualCarrier × M.dualCarrier) :
    ((L.orthogonalSumDualCarrierEquiv M).symm x : V × W) = (x.1.1, x.2.1) :=
  by
    apply Prod.ext <;> rfl

/-- Under the dual-carrier product equivalence, the embedded carrier of an orthogonal sum is the
product of the two embedded carriers. -/
theorem map_carrierInDual_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).carrierInDual.map
        (L.orthogonalSumDualCarrierEquiv M).toLinearMap =
      L.carrierInDual.prod M.carrierInDual := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_prod]
  simp only [mem_carrierInDual_iff]
  rw [orthogonalSum_carrier, Submodule.mem_prod]
  rfl

/-- The discriminant group of an orthogonal sum is canonically the product of the discriminant
groups of its summands. -/
def discriminantGroupOrthogonalSumEquiv
    (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).DiscriminantGroup ≃ₗ[ℤ]
      L.DiscriminantGroup × M.DiscriminantGroup :=
  (Submodule.Quotient.equiv (L.orthogonalSum M).carrierInDual
      (L.carrierInDual.prod M.carrierInDual) (L.orthogonalSumDualCarrierEquiv M)
      (L.map_carrierInDual_orthogonalSum M)).trans
    (Submodule.quotientProdEquiv L.carrierInDual M.carrierInDual)

/-- The orthogonal-sum discriminant-group equivalence maps a representative to the pair of its
component classes. -/
@[simp]
theorem discriminantGroupOrthogonalSumEquiv_mk (L : IntegralLattice V) (M : IntegralLattice W)
    (x : (L.orthogonalSum M).dualCarrier) :
    L.discriminantGroupOrthogonalSumEquiv M (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).1,
        Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).2) := by
  rw [discriminantGroupOrthogonalSumEquiv, LinearEquiv.trans_apply]
  rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    Submodule.quotientProdEquiv_apply_mk, LinearEquiv.coe_coe]

/-- The product equivalence of discriminant groups is an isometry from the discriminant pairing
of an orthogonal sum to the orthogonal product of the two discriminant pairings. -/
noncomputable def discriminantBilinearIsometryOrthogonalSum
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate] :
    FiniteBilinearModule.Isometry (L.orthogonalSum M).discriminantBilinearModule
      (L.discriminantBilinearModule.prod M.discriminantBilinearModule) where
  toAddEquiv := (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv
  map_pairing' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        -- The isometry's carrier is definitionally the discriminant group, but this conversion
        -- is intentionally not part of the public reduction API.
        change (L.discriminantBilinearModule.prod M.discriminantBilinearModule).pairing
            (L.discriminantGroupOrthogonalSumEquiv M (Submodule.Quotient.mk x))
            (L.discriminantGroupOrthogonalSumEquiv M (Submodule.Quotient.mk y)) = _
        rw [discriminantGroupOrthogonalSumEquiv_mk,
          discriminantGroupOrthogonalSumEquiv_mk]
        -- Use the characteristic pairing lemmas after crossing the bundled-carrier boundary.
        change L.discriminantPairing
            (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).1)
            (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M y).1) +
          M.discriminantPairing
            (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).2)
            (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M y).2) =
          (L.orthogonalSum M).discriminantPairing
            (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
        rw [discriminantPairing_mk, discriminantPairing_mk, discriminantPairing_mk,
          orthogonalSum_form, orthogonalSumForm_apply,
          orthogonalSumDualCarrierEquiv_apply]
        rw [L.orthogonalSumDualCarrierEquiv_apply M y, ← AddCircle.coe_add]

/-- The underlying additive equivalence of the orthogonal-sum discriminant-bilinear isometry is
the canonical product equivalence of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryOrthogonalSum_toAddEquiv
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate] :
    (L.discriminantBilinearIsometryOrthogonalSum M).toAddEquiv =
      (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv :=
  by rw [discriminantBilinearIsometryOrthogonalSum]

/-- The orthogonal-sum discriminant-bilinear isometry acts through the canonical discriminant-group
equivalence. -/
@[simp]
theorem discriminantBilinearIsometryOrthogonalSum_apply
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (x : (L.orthogonalSum M).DiscriminantGroup) :
    L.discriminantBilinearIsometryOrthogonalSum M x =
      L.discriminantGroupOrthogonalSumEquiv M x :=
  by
    exact congrArg (fun e ↦ e x)
      (L.discriminantBilinearIsometryOrthogonalSum_toAddEquiv M)

/-- The orthogonal-sum discriminant-bilinear isometry maps a representative to the pair of its
component classes. -/
theorem discriminantBilinearIsometryOrthogonalSum_mk
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (x : (L.orthogonalSum M).dualCarrier) :
    L.discriminantBilinearIsometryOrthogonalSum M (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).1,
        Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).2) :=
  L.discriminantGroupOrthogonalSumEquiv_mk M x

/-- The product equivalence of discriminant groups is an isometry from the half-norm
discriminant quadratic module of an orthogonal sum to the orthogonal product of the two
discriminant quadratic modules. -/
noncomputable def discriminantQuadraticIsometryOrthogonalSum
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    FiniteQuadraticModule.Isometry
      ((L.orthogonalSum M).discriminantQuadraticModule
        ((L.isEven_orthogonalSum_iff M).mpr ⟨hL, hM⟩))
      ((L.discriminantQuadraticModule hL).prod (M.discriminantQuadraticModule hM)) where
  toLinearEquiv := L.discriminantGroupOrthogonalSumEquiv M
  map_app' := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      -- The isometry's carrier is definitionally the discriminant group, but this conversion
      -- is intentionally not part of the public reduction API.
      change ((L.discriminantQuadraticModule hL).prod
          (M.discriminantQuadraticModule hM)).quadratic
          (L.discriminantGroupOrthogonalSumEquiv M (Submodule.Quotient.mk x)) = _
      rw [discriminantGroupOrthogonalSumEquiv_mk]
      -- Use the characteristic quadratic-map lemmas after crossing the bundled-carrier boundary.
      change L.discriminantQuadraticMap hL
          (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).1) +
        M.discriminantQuadraticMap hM
          (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).2) =
        (L.orthogonalSum M).discriminantQuadraticMap _ (Submodule.Quotient.mk x)
      rw [discriminantQuadraticMap_mk, discriminantQuadraticMap_mk,
        discriminantQuadraticMap_mk, orthogonalSum_form, orthogonalSumForm_apply,
        orthogonalSumDualCarrierEquiv_apply]
      rw [← AddCircle.coe_add]
      congr 1
      ring

/-- The underlying additive equivalence of the orthogonal-sum discriminant-quadratic isometry is
the canonical product equivalence of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryOrthogonalSum_toAddEquiv
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    (L.discriminantQuadraticIsometryOrthogonalSum M hL hM).toAddEquiv =
      (L.discriminantGroupOrthogonalSumEquiv M).toAddEquiv :=
  by
    rw [discriminantQuadraticIsometryOrthogonalSum]
    rfl

/-- The orthogonal-sum discriminant-quadratic isometry acts through the canonical
discriminant-group equivalence. -/
@[simp]
theorem discriminantQuadraticIsometryOrthogonalSum_apply
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (x : (L.orthogonalSum M).DiscriminantGroup) :
    L.discriminantQuadraticIsometryOrthogonalSum M hL hM x =
      L.discriminantGroupOrthogonalSumEquiv M x :=
  by
    exact congrArg (fun e ↦ e x)
      (L.discriminantQuadraticIsometryOrthogonalSum_toAddEquiv M hL hM)

/-- The orthogonal-sum discriminant-quadratic isometry maps a representative to the pair of its
component classes. -/
theorem discriminantQuadraticIsometryOrthogonalSum_mk
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) (x : (L.orthogonalSum M).dualCarrier) :
    L.discriminantQuadraticIsometryOrthogonalSum M hL hM (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).1,
        Submodule.Quotient.mk (L.orthogonalSumDualCarrierEquiv M x).2) := by
  rw [discriminantQuadraticIsometryOrthogonalSum_apply,
    discriminantGroupOrthogonalSumEquiv_mk]

/-- Forgetting the quadratic maps from the orthogonal-sum discriminant isometry recovers the
orthogonal-sum discriminant-bilinear isometry. -/
@[simp]
theorem discriminantQuadraticIsometryOrthogonalSum_toFiniteBilinearModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    (L.discriminantQuadraticIsometryOrthogonalSum M hL hM).toFiniteBilinearModule =
      L.discriminantBilinearIsometryOrthogonalSum M := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
    discriminantQuadraticIsometryOrthogonalSum_toAddEquiv,
    discriminantBilinearIsometryOrthogonalSum_toAddEquiv]

/-! ## Form negation -/

/-- Negating a lattice form does not change its dual carrier. -/
@[simp]
theorem dualCarrier_neg (L : IntegralLattice V) : (-L).dualCarrier = L.dualCarrier := by
  ext x
  simp only [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule, neg_carrier, neg_form,
    LinearMap.neg_apply]
  constructor
  · intro hx y hy
    exact (Submodule.neg_mem_iff (1 : Submodule ℤ ℚ)).mp (hx y hy)
  · intro hx y hy
    exact (Submodule.neg_mem_iff (1 : Submodule ℤ ℚ)).mpr (hx y hy)

/-- The dual carrier of a form-negated lattice is canonically identified with the original dual
carrier by the identity on ambient vectors. -/
def negDualCarrierEquiv (L : IntegralLattice V) :
    (-L).dualCarrier ≃ₗ[ℤ] L.dualCarrier where
  toFun x := ⟨x, by simpa using x.2⟩
  invFun x := ⟨x, by simp only [dualCarrier_neg]; exact x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dual-carrier equivalence for form negation is the identity on ambient vectors. -/
@[simp]
theorem coe_negDualCarrierEquiv_apply (L : IntegralLattice V) (x : (-L).dualCarrier) :
    (L.negDualCarrierEquiv x : V) = x :=
  (rfl)

/-- The inverse dual-carrier equivalence for form negation is also the identity on ambient
vectors. -/
@[simp]
theorem coe_negDualCarrierEquiv_symm_apply (L : IntegralLattice V) (x : L.dualCarrier) :
    (L.negDualCarrierEquiv.symm x : V) = x :=
  (rfl)

/-- Under the dual-carrier equivalence for form negation, the embedded carrier maps to the
original embedded carrier. -/
theorem map_carrierInDual_neg (L : IntegralLattice V) :
    (-L).carrierInDual.map L.negDualCarrierEquiv.toLinearMap = L.carrierInDual := by
  ext x
  rw [Submodule.mem_map_equiv]
  simp only [mem_carrierInDual_iff, neg_carrier, coe_negDualCarrierEquiv_symm_apply]

/-- Negating a lattice form leaves its discriminant group canonically unchanged. -/
def discriminantGroupNegEquiv (L : IntegralLattice V) :
    (-L).DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup :=
  Submodule.Quotient.equiv (-L).carrierInDual L.carrierInDual L.negDualCarrierEquiv
    L.map_carrierInDual_neg

/-- The discriminant-group equivalence for form negation maps every representative to the same
ambient representative. -/
@[simp]
theorem discriminantGroupNegEquiv_mk (L : IntegralLattice V) (x : (-L).dualCarrier) :
    L.discriminantGroupNegEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (L.negDualCarrierEquiv x) := by
  rw [discriminantGroupNegEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  congr 1

/-- The canonical discriminant-group equivalence is an isometry from the discriminant pairing
of the form-negated lattice to the negative of the original discriminant pairing. -/
noncomputable def discriminantBilinearIsometryNeg (L : IntegralLattice V)
    [L.IsNondegenerate] :
    FiniteBilinearModule.Isometry (-L).discriminantBilinearModule
      L.discriminantBilinearModule.neg where
  toAddEquiv := L.discriminantGroupNegEquiv.toAddEquiv
  map_pairing' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        -- The source and target carriers are definitionally discriminant groups, while their
        -- bundled pairings are intentionally accessed through characteristic lemmas.
        change -L.discriminantPairing
            (L.discriminantGroupNegEquiv (Submodule.Quotient.mk x))
            (L.discriminantGroupNegEquiv (Submodule.Quotient.mk y)) =
          (-L).discriminantPairing
            (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
        rw [discriminantGroupNegEquiv_mk,
          discriminantGroupNegEquiv_mk, discriminantPairing_mk, discriminantPairing_mk,
          neg_form]
        -- Coercion into `AddCircle` preserves negation, but its two sides are not syntactically
        -- identical until the ambient bilinear-form application is exposed.
        change -((L.form (x : V) (y : V) : ℚ) : AddCircle (1 : ℚ)) =
          ((-(L.form (x : V) (y : V)) : ℚ) : AddCircle (1 : ℚ))
        rw [← AddCircle.coe_neg]

/-- The underlying additive equivalence of the discriminant-bilinear isometry for form negation
is the canonical equivalence of discriminant groups. -/
@[simp]
theorem discriminantBilinearIsometryNeg_toAddEquiv (L : IntegralLattice V)
    [L.IsNondegenerate] :
    L.discriminantBilinearIsometryNeg.toAddEquiv = L.discriminantGroupNegEquiv.toAddEquiv :=
  (rfl)

/-- The discriminant-bilinear isometry for form negation acts through the canonical
discriminant-group equivalence. -/
@[simp]
theorem discriminantBilinearIsometryNeg_apply (L : IntegralLattice V) [L.IsNondegenerate]
    (x : (-L).DiscriminantGroup) :
    L.discriminantBilinearIsometryNeg x = L.discriminantGroupNegEquiv x :=
  by
    exact congrArg (fun e ↦ e x) L.discriminantBilinearIsometryNeg_toAddEquiv

/-- The discriminant-bilinear isometry for form negation maps every representative to the same
ambient representative. -/
theorem discriminantBilinearIsometryNeg_mk (L : IntegralLattice V) [L.IsNondegenerate]
    (x : (-L).dualCarrier) :
    L.discriminantBilinearIsometryNeg (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (L.negDualCarrierEquiv x) :=
  L.discriminantGroupNegEquiv_mk x

/-- The canonical discriminant-group equivalence is an isometry from the half-norm
discriminant quadratic module of a form-negated lattice to the negative of the original
discriminant quadratic module. -/
noncomputable def discriminantQuadraticIsometryNeg (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) :
    FiniteQuadraticModule.Isometry
      ((-L).discriminantQuadraticModule (L.isEven_neg_iff.mpr hL))
      (L.discriminantQuadraticModule hL).neg where
  toLinearEquiv := L.discriminantGroupNegEquiv
  map_app' := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      -- The source and target carriers are definitionally discriminant groups, while their
      -- bundled quadratic maps are intentionally accessed through characteristic lemmas.
      change -L.discriminantQuadraticMap hL
          (L.discriminantGroupNegEquiv (Submodule.Quotient.mk x)) =
        (-L).discriminantQuadraticMap (L.isEven_neg_iff.mpr hL)
          (Submodule.Quotient.mk x)
      rw [discriminantGroupNegEquiv_mk, discriminantQuadraticMap_mk,
        discriminantQuadraticMap_mk, neg_form]
      -- Coercion into `AddCircle` preserves negation; the remaining rational identity is the
      -- distribution of negation across division by two.
      change -(((L.form (x : V) (x : V) / 2 : ℚ)) : AddCircle (1 : ℚ)) =
        (((-(L.form (x : V) (x : V)) / 2 : ℚ)) : AddCircle (1 : ℚ))
      rw [← AddCircle.coe_neg]
      congr 1
      ring

/-- The underlying additive equivalence of the discriminant-quadratic isometry for form
negation is the canonical equivalence of discriminant groups. -/
@[simp]
theorem discriminantQuadraticIsometryNeg_toAddEquiv (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryNeg hL).toAddEquiv =
      L.discriminantGroupNegEquiv.toAddEquiv :=
  (rfl)

/-- The discriminant-quadratic isometry for form negation acts through the canonical
discriminant-group equivalence. -/
@[simp]
theorem discriminantQuadraticIsometryNeg_apply (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) (x : (-L).DiscriminantGroup) :
    L.discriminantQuadraticIsometryNeg hL x = L.discriminantGroupNegEquiv x :=
  by
    exact congrArg (fun e ↦ e x) (L.discriminantQuadraticIsometryNeg_toAddEquiv hL)

/-- The discriminant-quadratic isometry for form negation maps every representative to the same
ambient representative. -/
theorem discriminantQuadraticIsometryNeg_mk (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) (x : (-L).dualCarrier) :
    L.discriminantQuadraticIsometryNeg hL (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (L.negDualCarrierEquiv x) := by
  rw [discriminantQuadraticIsometryNeg_apply, discriminantGroupNegEquiv_mk]

/-- Forgetting the quadratic maps from the discriminant isometry for form negation recovers the
corresponding discriminant-bilinear isometry. -/
@[simp]
theorem discriminantQuadraticIsometryNeg_toFiniteBilinearModule
    (L : IntegralLattice V) [L.IsNondegenerate] (hL : L.IsEven) :
    (L.discriminantQuadraticIsometryNeg hL).toFiniteBilinearModule =
      L.discriminantBilinearIsometryNeg := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
    discriminantQuadraticIsometryNeg_toAddEquiv,
    discriminantBilinearIsometryNeg_toAddEquiv]

end TauCeti.IntegralLattice
