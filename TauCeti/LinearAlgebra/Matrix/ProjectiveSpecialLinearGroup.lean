/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
-- not redundant: supplies the scoped `GL(n, R)⁺` notation, which the projective import
-- does not re-export under the module system
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Maps into `PSL(2, ℝ)`

The algebraic maps connecting the matrix groups of the modular theory to `PSL(2, ℝ)`:

* `sl2zToPSL2R : SL(2, ℤ) →* PSL(2, ℝ)` — cast entries to `ℝ`, then project; its kernel is
  the center of `SL(2, ℤ)` (`sl2zToPSL2R_ker`), since an integer matrix casts to a real
  scalar matrix iff it is itself scalar.
* `psl2zToPSL2R : PSL(2, ℤ) →* PSL(2, ℝ)` — the injective descent
  (`psl2zToPSL2R_injective`).
* `glPosToSL2R : GL(2, ℝ)⁺ →* SL(2, ℝ)` — the det-normalized representative
  `(√det g)⁻¹ • g`, a monoid homomorphism since positive scalars are central and `√` is
  multiplicative on them; `glPosToPSL2R` is its projectivization.

The actions of these groups on the upper half-plane, and the compatibility of these maps
with them, are in `TauCeti/Analysis/Complex/UpperHalfPlane/PSLAction.lean`.

Split out of the AINTLIB `LeanModularForms` port
(`LeanModularForms/Modularforms/PSL2Action.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>): these
declarations are pure matrix-group algebra with no dependence on `ℍ`.
-/

public section

noncomputable section

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

/-- The lift `SL(2, ℤ) →* PSL(2, ℝ)`: cast `SL(2, ℤ)` entries to `ℝ` via
`SpecialLinearGroup.map (Int.castRingHom ℝ)`, then project to the `±I`-quotient. -/
def sl2zToPSL2R : SL(2, ℤ) →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp] theorem sl2zToPSL2R_apply (g : SL(2, ℤ)) :
    sl2zToPSL2R g =
      (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) : PSL(2, ℝ)) := (rfl)

private lemma map_intCast_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) i j =
    (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := rfl

private lemma g_mem_center_of_map_intCast_mem_center (g : SL(2, ℤ))
    (hmem : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ)) : g ∈ Subgroup.center SL(2, ℤ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨r, hr_pow, hr_scalar⟩ := hmem
  have h_entry_R : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) =
      (Matrix.scalar (Fin 2) r) i j := fun i j ↦ by
    have h_ij := congr_fun (congr_fun hr_scalar i) j
    rw [map_intCast_entry] at h_ij
    exact h_ij.symm
  set z : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  have hr_z : (z : ℝ) = r := by
    have h00 := h_entry_R 0 0
    rwa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  have h_diag : ∀ i, (g : Matrix (Fin 2) (Fin 2) ℤ) i i = z := fun i ↦ by
    have h_iR : (((g : Matrix _ _ ℤ) i i : ℤ) : ℝ) = (z : ℝ) := by
      have hii := h_entry_R i i
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hii
      rw [hii, ← hr_z]
    exact_mod_cast h_iR
  have h_off : ∀ i j, i ≠ j → (g : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j hij ↦ by
    have h_R : (((g : Matrix _ _ ℤ) i j : ℤ) : ℝ) = 0 := by
      have hij' := h_entry_R i j
      rwa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at hij'
    exact_mod_cast h_R
  have hz_sq : z ^ 2 = 1 := by
    have hz_sq_R : (z : ℝ) ^ 2 = 1 := by
      rw [hr_z]
      simpa [Fintype.card_fin] using hr_pow
    exact_mod_cast hz_sq_R
  refine ⟨z, by simpa [Fintype.card_fin] using hz_sq, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, h_diag]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, h_off i j hij]

private lemma map_intCast_mem_center_of_g_mem_center (g : SL(2, ℤ))
    (hmem : g ∈ Subgroup.center SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨z, hz_pow, hz_scalar⟩ := hmem
  refine ⟨(z : ℝ), by exact_mod_cast hz_pow, ?_⟩
  ext i j
  have h_ij := congr_fun (congr_fun hz_scalar i) j
  rw [map_intCast_entry]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h_ij ⊢
    exact_mod_cast h_ij
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h_ij ⊢
    exact_mod_cast h_ij

/-- The kernel of `sl2zToPSL2R` is the center of `SL(2, ℤ)`: an integer matrix
casts to a real scalar matrix iff it is itself a scalar matrix. -/
theorem sl2zToPSL2R_ker : sl2zToPSL2R.ker = Subgroup.center SL(2, ℤ) := by
  ext g
  simp only [MonoidHom.mem_ker, sl2zToPSL2R_apply, QuotientGroup.eq_one_iff]
  exact ⟨g_mem_center_of_map_intCast_mem_center g, map_intCast_mem_center_of_g_mem_center g⟩

/-- The descended hom `PSL(2, ℤ) →* PSL(2, ℝ)`. `sl2zToPSL2R` factors through
`PSL(2, ℤ) = SL(2, ℤ) ⧸ center SL(2, ℤ)` since integer scalar matrices map into
`center SL(2, ℝ)`. -/
def psl2zToPSL2R : PSL(2, ℤ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) sl2zToPSL2R fun x hx ↦ by
    rwa [sl2zToPSL2R_ker]

@[simp] theorem psl2zToPSL2R_mk (g : SL(2, ℤ)) :
    psl2zToPSL2R (↑g : PSL(2, ℤ)) = sl2zToPSL2R g :=
  QuotientGroup.lift_mk' _ _ g

/-- `psl2zToPSL2R` is injective: its kernel is the image of
`sl2zToPSL2R.ker = center SL(2, ℤ)` under the `PSL(2, ℤ)`-projection, which is `⊥`. -/
theorem psl2zToPSL2R_injective : Function.Injective psl2zToPSL2R :=
  QuotientGroup.injective_lift_iff _ _ _ |>.2 sl2zToPSL2R_ker.symm

/-- The det-normalized `SL(2, ℝ)` representative of a `GL(2, ℝ)⁺` element, as a monoid
homomorphism: the matrix `(√ det g)⁻¹ • g` has determinant `1`, and normalization is
multiplicative because positive scalars are central and `√` is multiplicative on them. -/
def glPosToSL2R : GL(2, ℝ)⁺ →* SL(2, ℝ) where
  toFun g :=
    ⟨(Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), by
      have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
      -- the subtype's defining property is stated through `Subtype.val`; `change` exposes
      -- the determinant of the underlying smul-matrix, which no rewriting lemma names
      change ((Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
          ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hg_pos.le]
      exact inv_mul_cancel₀ (ne_of_gt hg_pos)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
    have h_det : ((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val =
        (g : GL (Fin 2) ℝ).det.val * (h : GL (Fin 2) ℝ).det.val := by
      simp [Units.val_mul]
    have h_mat : (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      simp [Units.val_mul]
    -- `Subtype.ext` reduces to the value level, where the normalized matrix of a product
    -- is definitionally the smul-matrix of the coerced product; `change` states it since
    -- the `glPosToSL2R`-value has no `coe_mk`-style equation before this definition ends
    change (Real.sqrt (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val))⁻¹ •
        (((g * h : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [h_det, h_mat, Real.sqrt_mul hg_pos.le, mul_inv]
    rw [← smul_mul_smul_comm]
    rfl

/-- The matrix of the det-normalized representative: `(√det g)⁻¹ • g`. -/
@[simp] theorem glPosToSL2R_coe_matrix (g : GL(2, ℝ)⁺) :
    ((glPosToSL2R g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := (rfl)

/-- The projective representative of a `GL(2, ℝ)⁺` element: the composition of
`glPosToSL2R` with the projection to `PSL(2, ℝ)`, a monoid homomorphism. -/
def glPosToPSL2R : GL(2, ℝ)⁺ →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp glPosToSL2R

/-- `glPosToPSL2R` is the class of the det-normalized representative. -/
@[simp] theorem glPosToPSL2R_apply (g : GL(2, ℝ)⁺) :
    glPosToPSL2R g = (↑(glPosToSL2R g) : PSL(2, ℝ)) := (rfl)
