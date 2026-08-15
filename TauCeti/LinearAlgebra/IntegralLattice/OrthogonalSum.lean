/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthogonal sums of integral lattices

The orthogonal sum has product carrier and block-diagonal form. This file constructs the lattice,
its canonical carrier maps and product bases, and proves the currently available invariant laws:
rank is additive, Gram matrices are block diagonal, determinant and discriminant are
multiplicative, and evenness and nondegeneracy are componentwise.

Associativity, commutativity, and functoriality as lattice isometries, together with signature
additivity, belong after the lattice-isometry and signature APIs targeted by the same roadmap.

## Main definitions

* `TauCeti.IntegralLattice.orthogonalSumForm`: the block-diagonal ambient form.
* `TauCeti.IntegralLattice.orthogonalSum`: the orthogonal sum lattice.
* `TauCeti.IntegralLattice.orthogonalSumCarrierEquiv`: the carrier-product equivalence.
* `TauCeti.IntegralLattice.orthogonalSumBasis`: the product of two carrier bases.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v w x

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- The block-diagonal bilinear form on a product, with the two factors orthogonal. -/
def orthogonalSumForm (L : IntegralLattice V) (M : IntegralLattice W) :
    LinearMap.BilinForm ℚ (V × W) :=
  L.form.comp (LinearMap.fst ℚ V W) (LinearMap.fst ℚ V W) +
    M.form.comp (LinearMap.snd ℚ V W) (LinearMap.snd ℚ V W)

/-- Evaluation of the block-diagonal form is the sum of the component pairings. -/
@[simp]
theorem orthogonalSumForm_apply (L : IntegralLattice V) (M : IntegralLattice W)
    (p q : V × W) :
    orthogonalSumForm L M p q = L.form p.1 q.1 + M.form p.2 q.2 :=
  (rfl)

/-- The product of two full integral carriers is a full integral carrier. -/
private theorem isLattice_prod (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.carrier.prod M.carrier).IsLattice ℚ := by
  constructor
  · rw [← Module.Finite.iff_fg]
    let e : (L.carrier.prod M.carrier) ≃ₗ[ℤ] L × M :=
      { toFun := fun p ↦
          (⟨p.1.1, (Submodule.mem_prod.mp p.2).1⟩,
            ⟨p.1.2, (Submodule.mem_prod.mp p.2).2⟩)
        invFun := fun p ↦ ⟨(p.1, p.2), Submodule.mem_prod.mpr ⟨p.1.2, p.2.2⟩⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact Module.Finite.equiv e.symm
  · change Submodule.span ℚ ((L.carrier : Set V) ×ˢ (M.carrier : Set W)) = ⊤
    rw [Submodule.span_prod_eq (R := ℚ) L.carrier.zero_mem M.carrier.zero_mem,
      Submodule.IsLattice.span_eq_top, Submodule.IsLattice.span_eq_top,
      Submodule.prod_top]

/-- The orthogonal sum of two integral lattices. -/
def orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) : IntegralLattice (V × W) where
  carrier := L.carrier.prod M.carrier
  form := orthogonalSumForm L M
  isLattice := isLattice_prod L M
  isSymm := ⟨fun p q ↦ by simp only [orthogonalSumForm_apply, L.isSymm.eq, M.isSymm.eq]⟩
  le_dual := by
    intro p hp
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro q hq
    rw [orthogonalSumForm_apply]
    exact Submodule.add_mem _ (L.le_dual hp.1 q.1 hq.1) (M.le_dual hp.2 q.2 hq.2)

@[simp]
theorem orthogonalSum_carrier (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).carrier = L.carrier.prod M.carrier :=
  (rfl)

@[simp]
theorem orthogonalSum_form (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).form = orthogonalSumForm L M :=
  (rfl)

/-- The carrier of an orthogonal sum is canonically the product of the carrier types. -/
def orthogonalSumCarrierEquiv (L : IntegralLattice V) (M : IntegralLattice W) :
    L.orthogonalSum M ≃ₗ[ℤ] L × M where
  toFun p :=
    (⟨p.1.1, (Submodule.mem_prod.mp p.2).1⟩,
      ⟨p.1.2, (Submodule.mem_prod.mp p.2).2⟩)
  invFun p := ⟨(p.1, p.2), Submodule.mem_prod.mpr ⟨p.1.2, p.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' := by intro c p; apply Prod.ext <;> rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical inclusion of the first carrier into an orthogonal sum. -/
def orthogonalSumInl (L : IntegralLattice V) (M : IntegralLattice W) :
    L →ₗ[ℤ] L.orthogonalSum M where
  toFun a := ⟨(a, 0), Submodule.mem_prod.mpr ⟨a.2, M.carrier.zero_mem⟩⟩
  map_add' := by intro a b; apply Subtype.ext; ext <;> simp
  map_smul' := by intro c a; apply Subtype.ext; ext <;> simp

/-- The canonical inclusion of the second carrier into an orthogonal sum. -/
def orthogonalSumInr (L : IntegralLattice V) (M : IntegralLattice W) :
    M →ₗ[ℤ] L.orthogonalSum M where
  toFun b := ⟨(0, b), Submodule.mem_prod.mpr ⟨L.carrier.zero_mem, b.2⟩⟩
  map_add' := by intro a b; apply Subtype.ext; ext <;> simp
  map_smul' := by intro c a; apply Subtype.ext; ext <;> simp

/-- The canonical first projection from the carrier of an orthogonal sum. -/
def orthogonalSumFst (L : IntegralLattice V) (M : IntegralLattice W) :
    L.orthogonalSum M →ₗ[ℤ] L :=
  (LinearMap.fst ℤ L M).comp (orthogonalSumCarrierEquiv L M).toLinearMap

/-- The canonical second projection from the carrier of an orthogonal sum. -/
def orthogonalSumSnd (L : IntegralLattice V) (M : IntegralLattice W) :
    L.orthogonalSum M →ₗ[ℤ] M :=
  (LinearMap.snd ℤ L M).comp (orthogonalSumCarrierEquiv L M).toLinearMap

@[simp] theorem orthogonalSumInl_apply (L : IntegralLattice V) (M : IntegralLattice W) (a : L) :
    (orthogonalSumInl L M a : V × W) = ((a : V), 0) := by
  rfl

@[simp] theorem orthogonalSumInr_apply (L : IntegralLattice V) (M : IntegralLattice W) (b : M) :
    (orthogonalSumInr L M b : V × W) = (0, (b : W)) := by
  rfl

@[simp] theorem orthogonalSumFst_apply (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) :
    orthogonalSumFst L M p = (orthogonalSumCarrierEquiv L M p).1 := (rfl)

@[simp] theorem orthogonalSumSnd_apply (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) :
    orthogonalSumSnd L M p = (orthogonalSumCarrierEquiv L M p).2 := (rfl)

@[simp]
theorem orthogonalSumCarrierEquiv_inl (L : IntegralLattice V) (M : IntegralLattice W) (a : L) :
    orthogonalSumCarrierEquiv L M (orthogonalSumInl L M a) = (a, 0) := by
  rfl

@[simp]
theorem orthogonalSumCarrierEquiv_inr (L : IntegralLattice V) (M : IntegralLattice W) (b : M) :
    orthogonalSumCarrierEquiv L M (orthogonalSumInr L M b) = (0, b) := by
  rfl

@[simp]
theorem orthogonalSumFst_inl (L : IntegralLattice V) (M : IntegralLattice W) (a : L) :
    orthogonalSumFst L M (orthogonalSumInl L M a) = a := by
  rfl

@[simp]
theorem orthogonalSumFst_inr (L : IntegralLattice V) (M : IntegralLattice W) (b : M) :
    orthogonalSumFst L M (orthogonalSumInr L M b) = 0 := by
  rfl

@[simp]
theorem orthogonalSumSnd_inl (L : IntegralLattice V) (M : IntegralLattice W) (a : L) :
    orthogonalSumSnd L M (orthogonalSumInl L M a) = 0 := by
  rfl

@[simp]
theorem orthogonalSumSnd_inr (L : IntegralLattice V) (M : IntegralLattice W) (b : M) :
    orthogonalSumSnd L M (orthogonalSumInr L M b) = b := by
  rfl

@[simp]
theorem coe_orthogonalSumCarrierEquiv_fst (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) : ((orthogonalSumCarrierEquiv L M p).1 : V) = p.1.1 := by
  rfl

@[simp]
theorem coe_orthogonalSumCarrierEquiv_snd (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) : ((orthogonalSumCarrierEquiv L M p).2 : W) = p.1.2 := by
  rfl

/-- The product of carrier bases is a basis of the orthogonal sum carrier. -/
noncomputable def orthogonalSumBasis {I : Type w} {J : Type x} (L : IntegralLattice V)
    (M : IntegralLattice W) (e : Basis I ℤ L) (f : Basis J ℤ M) :
    Basis (I ⊕ J) ℤ (L.orthogonalSum M) :=
  (e.prod f).map (orthogonalSumCarrierEquiv L M).symm

@[simp]
theorem orthogonalSumBasis_apply_inl {I : Type w} {J : Type x} (L : IntegralLattice V)
    (M : IntegralLattice W) (e : Basis I ℤ L) (f : Basis J ℤ M) (i : I) :
    orthogonalSumBasis L M e f (Sum.inl i) = orthogonalSumInl L M (e i) := by
  apply (orthogonalSumCarrierEquiv L M).injective
  simp [orthogonalSumBasis]

@[simp]
theorem orthogonalSumBasis_apply_inr {I : Type w} {J : Type x} (L : IntegralLattice V)
    (M : IntegralLattice W) (e : Basis I ℤ L) (f : Basis J ℤ M) (j : J) :
    orthogonalSumBasis L M e f (Sum.inr j) = orthogonalSumInr L M (f j) := by
  apply (orthogonalSumCarrierEquiv L M).injective
  simp [orthogonalSumBasis]

/-- The integral form of an orthogonal sum is the sum of its two component forms. -/
@[simp]
theorem integralForm_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W)
    (p q : L.orthogonalSum M) :
    (L.orthogonalSum M).integralForm p q =
      L.integralForm (orthogonalSumFst L M p) (orthogonalSumFst L M q) +
        M.integralForm (orthogonalSumSnd L M p) (orthogonalSumSnd L M q) := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_add, integralForm_cast, orthogonalSum_form, orthogonalSumForm_apply,
    orthogonalSumFst_apply, orthogonalSumSnd_apply, coe_orthogonalSumCarrierEquiv_fst,
    coe_orthogonalSumCarrierEquiv_snd]

/-- The integral norm of an orthogonal-sum vector is the sum of its component norms. -/
@[simp]
theorem integralNorm_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) :
    (L.orthogonalSum M).integralNorm p =
      L.integralNorm (orthogonalSumFst L M p) +
        M.integralNorm (orthogonalSumSnd L M p) := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_add, integralNorm_cast, norm_apply, orthogonalSum_form,
    orthogonalSumForm_apply, orthogonalSumFst_apply, orthogonalSumSnd_apply,
    coe_orthogonalSumCarrierEquiv_fst, coe_orthogonalSumCarrierEquiv_snd]

/-- The rank of an orthogonal sum is the sum of the ranks. -/
@[simp]
theorem finrank_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) :
    Module.finrank ℤ (L.orthogonalSum M) = Module.finrank ℤ L + Module.finrank ℤ M := by
  rw [LinearEquiv.finrank_eq (orthogonalSumCarrierEquiv L M), Module.finrank_prod]

/-- In product bases, the Gram matrix of an orthogonal sum is block diagonal. -/
theorem gramMatrix_orthogonalSum {I : Type w} {J : Type x} (L : IntegralLattice V)
    (M : IntegralLattice W) (e : Basis I ℤ L) (f : Basis J ℤ M) :
    (L.orthogonalSum M).gramMatrix (orthogonalSumBasis L M e f) =
      Matrix.fromBlocks (L.gramMatrix e) 0 0 (M.gramMatrix f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gramMatrix_apply, Matrix.fromBlocks]

/-- The Gram determinant of an orthogonal sum in product bases is the product of the two Gram
determinants. -/
theorem gramDet_orthogonalSum {I : Type w} {J : Type x} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : IntegralLattice V) (M : IntegralLattice W)
    (e : Basis I ℤ L) (f : Basis J ℤ M) :
    (L.orthogonalSum M).gramDet (orthogonalSumBasis L M e f) = L.gramDet e * M.gramDet f := by
  rw [gramDet_def, gramMatrix_orthogonalSum, Matrix.det_fromBlocks_zero₂₁, gramDet_def,
    gramDet_def]

/-- The signed determinant of an orthogonal sum is multiplicative. -/
@[simp]
theorem determinant_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).determinant = L.determinant * M.determinant := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  let f := Module.Free.chooseBasis ℤ M
  rw [(L.orthogonalSum M).determinant_eq_gramDet (orthogonalSumBasis L M e f),
    gramDet_orthogonalSum, ← L.determinant_eq_gramDet e, ← M.determinant_eq_gramDet f]

/-- The nonnegative discriminant of an orthogonal sum is multiplicative. -/
@[simp]
theorem discriminant_orthogonalSum (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).discriminant = L.discriminant * M.discriminant := by
  rw [discriminant_def, determinant_orthogonalSum, Int.natAbs_mul, discriminant_def,
    discriminant_def]

/-- An orthogonal sum is even exactly when both summands are even. -/
@[simp]
theorem isEven_orthogonalSum_iff (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).IsEven ↔ L.IsEven ∧ M.IsEven := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  let f := Module.Free.chooseBasis ℤ M
  constructor
  · intro h
    have hs := (isEven_iff_basis (L.orthogonalSum M) (orthogonalSumBasis L M e f)).mp h
    exact ⟨(isEven_iff_basis L e).mpr fun i ↦ by
        simpa using hs (Sum.inl i),
      (isEven_iff_basis M f).mpr fun j ↦ by
        simpa using hs (Sum.inr j)⟩
  · rintro ⟨hL, hM⟩
    apply (isEven_iff_basis (L.orthogonalSum M) (orthogonalSumBasis L M e f)).mpr
    intro i
    rcases i with i | j
    · simpa using (isEven_iff_basis L e).mp hL i
    · simpa using (isEven_iff_basis M f).mp hM j

/-- The block-diagonal form is nondegenerate exactly when both component forms are
nondegenerate. -/
@[simp]
theorem nondegenerate_orthogonalSumForm_iff (L : IntegralLattice V) (M : IntegralLattice W) :
    (orthogonalSumForm L M).Nondegenerate ↔ L.form.Nondegenerate ∧ M.form.Nondegenerate := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · exact ⟨
        fun a ha ↦ congrArg Prod.fst (hleft (a, 0) fun p ↦ by simpa using ha p.1),
        fun b hb ↦ congrArg Prod.fst (hright (b, 0) fun p ↦ by simpa using hb p.1)⟩
    · exact ⟨
        fun a ha ↦ congrArg Prod.snd (hleft (0, a) fun p ↦ by simpa using ha p.2),
        fun b hb ↦ congrArg Prod.snd (hright (0, b) fun p ↦ by simpa using hb p.2)⟩
  · rintro ⟨hL, hM⟩
    constructor
    · intro p hp
      apply Prod.ext
      · exact hL.1 p.1 fun a ↦ by simpa using hp (a, 0)
      · exact hM.1 p.2 fun b ↦ by simpa using hp (0, b)
    · intro q hq
      apply Prod.ext
      · exact hL.2 q.1 fun a ↦ by simpa using hq (a, 0)
      · exact hM.2 q.2 fun b ↦ by simpa using hq (0, b)

/-- The ambient form of an orthogonal sum is nondegenerate exactly when both summand forms are. -/
@[simp]
theorem nondegenerate_orthogonalSum_iff (L : IntegralLattice V) (M : IntegralLattice W) :
    (L.orthogonalSum M).form.Nondegenerate ↔
      L.form.Nondegenerate ∧ M.form.Nondegenerate := by
  rw [orthogonalSum_form, nondegenerate_orthogonalSumForm_iff]

end TauCeti.IntegralLattice
