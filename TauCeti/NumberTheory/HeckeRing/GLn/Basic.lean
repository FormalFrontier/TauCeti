/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.HeckeRing.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DoubleCoset

/-!
# The arithmetic Hecke triple for `GL_n`

The canonical arithmetic Hecke triple in `GL_n(ℚ)`, following [Shimura][shimura1971] §3.2:
`H = SL_n(ℤ)` (embedded via `mapGL ℚ`) and `Δ` the submonoid of integral matrices with
positive determinant. The heart is **Shimura's Lemma 3.10**
(`posDetInt_le_commensurator`): `Δ` lies in the commensurator of `SL_n(ℤ)`, because for an
integral `α` with `det α = d ≠ 0` the congruence subgroup
`Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))` has finite index and has conjugates in both directions
contained in `SL_n(ℤ)` — since `α⁻¹ = adj(α)/d` and `γ ≡ 1 mod d`.
The file ends with the resulting `IsHeckeTriple` instance, on which the Hecke ring
`𝕋 Δ SL_n(ℤ) ℤ` of `GL_n` is founded.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/Basic.lean`, Chris Birkbeck), realizing the Layer-2
substrate of the ModularForms roadmap (the `GL₂` case specializes to the Hecke operators on
modular forms); the AINTLIB `HeckePair` bundle is replaced by Mathlib's `IsHeckeTriple`.

## Main definitions

* `SLnZ`: `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, via `mapGL ℚ`.
* `posDetInt`: integral matrices with positive determinant, Shimura's `Δ`.

## Main results

* `SLnZ_le_posDetInt`: `SL_n(ℤ) ≤ Δ`.
* `posDetInt_le_commensurator`: `Δ ≤ commensurator(SL_n(ℤ))` (Shimura's Lemma 3.10).
* `commensurable_map_SLnZ`: the image of a finite-index subgroup of `SL_n(ℤ)` is commensurable
  with `SL_n(ℤ)` — the step by which each congruence subgroup inherits Lemma 3.10 and so sits
  in a Hecke triple of its own.
* the `IsHeckeTriple (posDetInt n) (SLnZ n) (SLnZ n)` instance, and the
  Hecke ring `IntegralHeckeRing n` it founds.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

section Embedding

/-- `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, via `mapGL ℚ : SL(n, ℤ) →* GL(n, ℚ)`.
    Following mathlib's pattern for arithmetic subgroups. -/
noncomputable def SLnZ : Subgroup (GL (Fin n) ℚ) :=
  (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ).range

/-- Coercion from `SL_n(ℤ)` to `GL_n(ℚ)` via `mapGL ℚ`. -/
noncomputable scoped instance coeMapGLRat :
    Coe (SpecialLinearGroup (Fin n) ℤ) (GL (Fin n) ℚ) :=
  ⟨mapGL ℚ⟩

/-- The canonical membership: integral special-linear matrices land in `SL_n(ℤ)`. Not a
`simp` lemma: `mem_SLnZ_iff` subsumes it as a normal form. -/
lemma coe_mem_SLnZ (σ : SpecialLinearGroup (Fin n) ℤ) :
    (σ : GL (Fin n) ℚ) ∈ SLnZ n := ⟨σ, rfl⟩

/-- Membership in `SL_n(ℤ)` characterised by an integral special-linear witness: the
elimination principle paired with `coe_mem_SLnZ`. `SLnZ` is a sealed definition, so modules
downstream cannot unfold it to `MonoidHom.range`; this lemma is how they extract the witness. -/
@[simp] lemma mem_SLnZ_iff {g : GL (Fin n) ℚ} :
    g ∈ SLnZ n ↔ ∃ σ : SpecialLinearGroup (Fin n) ℤ, (σ : GL (Fin n) ℚ) = g := by
  rw [SLnZ, MonoidHom.mem_range]

/-- An element of `SL_n(ℤ)` has matrix determinant one over `ℚ`.

`SpecialLinearGroup.det_mapGL` is the same fact for `GeneralLinearGroup.det`, which is
`ℚˣ`-valued; every consumer needs the `Matrix.det` of the coerced matrix, so this is the
`Units.val` bridge rather than a second proof. -/
lemma det_eq_one_of_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    (↑g : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff n).mp hg
  exact congrArg Units.val (SpecialLinearGroup.det_mapGL (S := ℚ) σ)

/-- The case of coefficient subgroups inside `SL_n(ℤ)`, which is how the congruence subgroups
get it. -/
lemma det_eq_of_mem_doubleCoset_of_le_SLnZ {H₁ H₂ : Subgroup (GL (Fin n) ℚ)}
    (h₁ : H₁ ≤ SLnZ n) (h₂ : H₂ ≤ SLnZ n) {a b : GL (Fin n) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a H₁ H₂) :
    (↑b : Matrix (Fin n) (Fin n) ℚ).det = (↑a : Matrix (Fin n) (Fin n) ℚ).det :=
  DoubleCoset.det_eq_of_mem_doubleCoset_of_det_eq_one
    (fun _ hγ ↦ det_eq_one_of_mem_SLnZ n (h₁ hγ)) (fun _ hγ ↦ det_eq_one_of_mem_SLnZ n (h₂ hγ)) hb

/-- The `SL_n(ℤ)` case of `det_eq_of_mem_doubleCoset_of_le_SLnZ`. -/
lemma det_eq_of_mem_doubleCoset_SLnZ {a b : GL (Fin n) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a (SLnZ n) (SLnZ n)) :
    (↑b : Matrix (Fin n) (Fin n) ℚ).det = (↑a : Matrix (Fin n) (Fin n) ℚ).det :=
  det_eq_of_mem_doubleCoset_of_le_SLnZ n le_rfl le_rfl hb

/-- The image in `GL_n(ℚ)` of a finite-index subgroup of `SL_n(ℤ)` is commensurable with
`SL_n(ℤ)`. Since `mapGL ℚ` is injective, both relative indices transport along it: one is the
index of `H`, finite by hypothesis, and the other is `1`.

This is the commensurability every congruence subgroup needs in order to sit in a Hecke
triple, so it is stated once here for an arbitrary finite-index subgroup rather than
re-proved at each of `Γ₀(N)`, `Γ₁(N)`, `Γ(N)`. -/
lemma commensurable_map_SLnZ (H : Subgroup (SpecialLinearGroup (Fin n) ℤ)) [H.FiniteIndex] :
    Subgroup.Commensurable (H.map (mapGL ℚ)) (SLnZ n) := by
  constructor
  · rw [SLnZ, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [SLnZ, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

end Embedding

section PosDetInt

/-- An element of `GL_n(ℚ)` has integer matrix entries if its underlying matrix
    is the image of an integer matrix under `ℤ → ℚ`. -/
def HasIntEntries (g : GL (Fin n) ℚ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ,
    (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)

/-- Characteristic lemma for `HasIntEntries`: introduction and elimination via the
integer-matrix witness, without exposing the definition body. -/
@[simp]
lemma hasIntEntries_iff {g : GL (Fin n) ℚ} :
    HasIntEntries n g ↔ ∃ A : Matrix (Fin n) (Fin n) ℤ,
      (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ) :=
  (Iff.rfl)

lemma hasIntEntries_of_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    HasIntEntries n g :=
  let ⟨σ, hσ⟩ := hg
  ⟨σ.val, hσ ▸ by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- The identity matrix has integer entries. -/
lemma hasIntEntries_one : HasIntEntries n (1 : GL (Fin n) ℚ) :=
  ⟨1, by ext i j; simp [Matrix.map_apply, Matrix.one_apply]⟩

/-- Product of integer-entry matrices has integer entries. -/
lemma HasIntEntries.mul {a b : GL (Fin n) ℚ} (ha : HasIntEntries n a) (hb : HasIntEntries n b) :
    HasIntEntries n (a * b) :=
  let ⟨A, hA⟩ := ha; let ⟨B, hB⟩ := hb
  ⟨A * B, by ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]⟩

/-- The submonoid of `GL_n(ℚ)` with integer matrix entries. -/
noncomputable def intEntries : Submonoid (GL (Fin n) ℚ) where
  carrier := {g | HasIntEntries n g}
  one_mem' := hasIntEntries_one n
  mul_mem' := fun ha hb ↦ HasIntEntries.mul (n := n) ha hb

@[simp]
lemma mem_intEntries {g : GL (Fin n) ℚ} : g ∈ intEntries n ↔ HasIntEntries n g := (Iff.rfl)

/-- The submonoid of `GL_n(ℚ)` consisting of invertible matrices with integer entries
and positive determinant — Shimura's `Δ`, as the integral-entry part of Mathlib's
positive-determinant subgroup `Matrix.GLPos`. -/
noncomputable def posDetInt : Submonoid (GL (Fin n) ℚ) :=
  intEntries n ⊓ (Matrix.GLPos (Fin n) ℚ).toSubmonoid

/-- Membership in `Δ`: integer entries and positive determinant. -/
@[simp]
lemma mem_posDetInt_iff {g : GL (Fin n) ℚ} :
    g ∈ posDetInt n ↔
      HasIntEntries n g ∧ 0 < (↑g : Matrix (Fin n) (Fin n) ℚ).det := by
  simp [posDetInt, Submonoid.mem_inf, Matrix.mem_glpos,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- `posDetInt n` is contained in the positive-determinant submonoid, forgetting integrality.
`posDetInt n` is defined as a meet, so this is one projection of it — but the meet is not visible
outside this file (`posDetInt` is not `@[expose]`), so consumers that need only positivity, and
not integrality, must go through this lemma. -/
lemma posDetInt_le_glpos : posDetInt n ≤ (Matrix.GLPos (Fin n) ℚ).toSubmonoid := inf_le_right

end PosDetInt

section Pair

/-- `SL_n(ℤ) ⊆ Δ`: elements of `SL_n(ℤ)` have integer entries and det = 1 > 0. -/
lemma SLnZ_le_posDetInt : (SLnZ n).toSubmonoid ≤ posDetInt n := by
  rintro g ⟨A, rfl⟩
  refine ⟨⟨A.val, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩, ?_⟩
  simp

/-- `SL_n(ℤ)` has positive determinant, forgetting integrality — the composite of
`SLnZ_le_posDetInt` with `posDetInt_le_glpos`, for consumers that need only the determinant. -/
lemma SLnZ_le_glpos : SLnZ n ≤ Matrix.GLPos (Fin n) ℚ := fun _ h ↦
  posDetInt_le_glpos n (SLnZ_le_posDetInt n h)

/-- Kernel element of `SL_n(ℤ) → SL_n(ℤ/dℤ)` has entries congruent to identity mod d. -/
private lemma ker_entry_dvd (d : ℕ) (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod d))).ker) (i j : Fin n) :
    (d : ℤ) ∣ (γ.val i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) := by
  rw [MonoidHom.mem_ker] at hγ
  have h0 := congr_arg Subtype.val hγ
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    SpecialLinearGroup.coe_one] at h0
  have h := congr_fun₂ h0 i j
  rw [Matrix.map_apply, Int.coe_castRingHom] at h
  rw [Matrix.one_apply] at h ⊢
  split_ifs at h ⊢
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simp [h])
  · rw [sub_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- When `d | (gamma - I)` entry-wise, decompose `gamma = I + d * M`. -/
private lemma gamma_decompose (d : ℤ) (gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, d ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j)) :
    gamma = 1 + d • Matrix.of fun i j ↦ (gamma i j - (1 : Matrix _ _ ℤ) i j) / d := by
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp only [Matrix.one_apply] at hgamma
  nlinarith [mul_comm ((gamma i j - if i = j then 1 else 0) / d) d,
    Int.ediv_mul_cancel (hgamma i j)]

/-- If `d | (γ - I)` entry-wise, then `d | (adj(A) * γ * A)` entry-wise.
    Key: `adj(A) * (I + dM) * A = d·I + d·(adj(A)·M·A)`. -/
private lemma adjugate_conj_dvd (A gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, A.det ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j))
    (i j : Fin n) :
    A.det ∣ (A.adjugate * gamma * A) i j := by
  set M := Matrix.of fun i j ↦ (gamma i j - (1 : Matrix _ _ ℤ) i j) / A.det
  have : A.adjugate * gamma * A = A.adjugate * A + A.det • (A.adjugate * M * A) := by
    rw [gamma_decompose n A.det gamma hgamma]
    conv_lhs => rw [mul_add, Matrix.mul_one, mul_smul_comm]
    rw [add_mul, smul_mul_assoc]
  rw [this, adjugate_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- If `d | P i j` for all entries and `det(P) = d ^ n`, then
    `det(P / d) = 1`, where the division is entry-wise integer division. -/
private lemma det_entrywise_div_eq_one (d : ℤ) (P : Matrix (Fin n) (Fin n) ℤ)
    (hdvd : ∀ i j : Fin n, d ∣ P i j) (hd : d ≠ 0) (hdet : (P.det : ℚ) = (d : ℚ) ^ n) :
    (Matrix.of fun i j ↦ P i j / d).det = 1 := by
  suffices h : ((Matrix.of fun i j ↦ P i j / d).det : ℚ) = 1 by exact_mod_cast h
  have h_mat_eq : (Matrix.of fun i j ↦ P i j / d).map (Int.cast : ℤ → ℚ) =
      (d : ℚ)⁻¹ • (P.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [Int.cast_div (hdvd i j) (Int.cast_ne_zero.mpr hd)]
    ring
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hdetc : ∀ B : Matrix (Fin n) (Fin n) ℤ,
      (B.map (Int.cast : ℤ → ℚ)).det = (B.det : ℚ) := fun B => by
    simpa [RingHom.mapMatrix_apply] using (RingHom.map_det (Int.castRingHom ℚ) B).symm
  rw [← hdetc, h_mat_eq, det_smul, Fintype.card_fin, hdetc, hdet, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero n hdQ)

variable [NeZero n]

/-- The integer matrix `(adj(A) * γ * A) / det(A)` has determinant 1
    when `det(γ) = 1`. -/
private lemma conj_mat_det_one (A gamma : Matrix (Fin n) (Fin n) ℤ) (hgamma_det : gamma.det = 1)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j) (hAdet : A.det ≠ 0) :
    (Matrix.of fun i j ↦ (A.adjugate * gamma * A) i j / A.det).det = 1 := by
  apply det_entrywise_div_eq_one n A.det _ hdvd hAdet
  simp only [Matrix.det_mul, det_adjugate, hgamma_det]
  push_cast
  rw [mul_one, Fintype.card_fin, ← pow_succ, Nat.sub_one_add_one_eq_of_pos (NeZero.pos n)]

omit [NeZero n] in
/-- The entrywise quotient `δ = (adj(A) * γ * A) / det(A)` satisfies `A * δ = γ * A`,
    given the entrywise divisibility and `det(A) ≠ 0`. -/
private lemma int_mul_eq (A gamma : Matrix (Fin n) (Fin n) ℤ) (hAdet : A.det ≠ 0)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j) :
    A * (Matrix.of fun i j ↦ (A.adjugate * gamma * A) i j / A.det) = gamma * A := by
  set delta := Matrix.of fun i j ↦ (A.adjugate * gamma * A) i j / A.det
  have ha : A.det • delta = A.adjugate * gamma * A := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, delta]
    exact Int.mul_ediv_cancel' (hdvd i j)
  suffices h : A.det • (A * delta) = A.det • (gamma * A) by
    ext i j
    exact mul_left_cancel₀ hAdet
      (by simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun₂ h i j)
  rw [← mul_smul_comm, ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_adjugate, smul_mul_assoc, one_mul, smul_mul_assoc]

omit [NeZero n] in
/-- The integral matrix beneath an element of `GL_n(ℚ)` has nonzero determinant. -/
private lemma det_ne_zero_of_val_eq (g : GL (Fin n) ℚ) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)) : A.det ≠ 0 := by
  have h := g.det_ne_zero
  rw [hA] at h
  have hdetc : (A.map (Int.cast : ℤ → ℚ)).det = (A.det : ℚ) := by
    simpa [RingHom.mapMatrix_apply] using (RingHom.map_det (Int.castRingHom ℚ) A).symm
  rw [hdetc, Int.cast_ne_zero] at h
  exact h

/-- If `g` has integer matrix `A` and `γ ∈ SL_n(ℤ)` is congruent to the identity modulo
`|det A|`, then `g⁻¹ γ g` is again in `SL_n(ℤ)`. -/
lemma inv_conjugate_mem_SLnZ_of_mem_ker (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ))
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker) :
    g⁻¹ * (γ : GL (Fin n) ℚ) * g ∈ SLnZ n := by
  have hAdet : A.det ≠ 0 := det_ne_zero_of_val_eq n g hA
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet⟩
  have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) :=
    fun i j ↦ Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ i j)
  have hdvd := adjugate_conj_dvd n A γ.val h_entry
  set delta_mat := Matrix.of fun i j ↦ (A.adjugate * γ.val * A) i j / A.det
  have hdelta_det : delta_mat.det = 1 := conj_mat_det_one n A γ.val γ.prop hdvd hAdet
  set delta : SpecialLinearGroup (Fin n) ℤ := ⟨delta_mat, hdelta_det⟩
  rw [SLnZ, MonoidHom.mem_range]
  refine ⟨delta, ?_⟩
  have h_int_eq : A * delta_mat = γ.val * A := int_mul_eq n A γ.val hAdet hdvd
  have h_mat_eq : (g * (delta : GL (Fin n) ℚ)).val = ((γ : GL (Fin n) ℚ) * g).val := by
    -- unit multiplication is definitionally matrix multiplication of the coordinates;
    -- `change` states it since no rewriting lemma unfolds `Units.val` products here
    change (g.val * (delta : GL (Fin n) ℚ).val : Matrix _ _ ℚ) =
      ((γ : GL (Fin n) ℚ).val * g.val : Matrix _ _ ℚ)
    simp only [mapGL_coe_matrix, algebraMap_int_eq,
      map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom] at hA ⊢
    rw [hA]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq]
  have h_unit_eq : g * (delta : GL (Fin n) ℚ) = (γ : GL (Fin n) ℚ) * g := Units.ext h_mat_eq
  have h_delta : (delta : GL (Fin n) ℚ) = g⁻¹ * ((γ : GL (Fin n) ℚ) * g) := by
    rw [← h_unit_eq, inv_mul_cancel_left]
  rw [h_delta, mul_assoc]

omit [NeZero n] in
omit [NeZero n] in
/-- The transposed conjugation product, entrywise: the bridge deriving each `_reverse` lemma
from its forward counterpart applied to `Aᵀ` and `γᵀ`. -/
private lemma transpose_conj_apply (A gamma : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (Aᵀ.adjugate * gammaᵀ * Aᵀ) i j = (A * gamma * A.adjugate) j i := by
  rw [← Matrix.adjugate_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
    Matrix.transpose_apply, Matrix.mul_assoc]

omit [NeZero n] in
/-- Reverse direction of `adjugate_conj_dvd`, derived from it at `Aᵀ`, `γᵀ`:
`d | (γ - I)` entry-wise implies `d | (A * γ * adj(A))` entry-wise. -/
private lemma conj_dvd_reverse (A gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, A.det ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j))
    (i j : Fin n) :
    A.det ∣ (A * gamma * A.adjugate) i j := by
  have hT : ∀ i j : Fin n, Aᵀ.det ∣ (gammaᵀ i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) := by
    intro i j
    have h_one : (1 : Matrix (Fin n) (Fin n) ℤ) i j = (1 : Matrix (Fin n) (Fin n) ℤ) j i := by
      rcases eq_or_ne i j with rfl | h
      · rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [Matrix.det_transpose, Matrix.transpose_apply, h_one]
    exact hgamma j i
  have h := adjugate_conj_dvd n Aᵀ gammaᵀ hT j i
  rwa [Matrix.det_transpose, transpose_conj_apply] at h

/-- Reverse direction of `conj_mat_det_one`, derived from it at `Aᵀ`, `γᵀ`:
`(A * γ * adj(A)) / det(A)` has determinant 1 when `det(γ) = 1`. -/
private lemma conj_mat_det_one_reverse
    (A gamma : Matrix (Fin n) (Fin n) ℤ) (hgamma_det : gamma.det = 1)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A * gamma * A.adjugate) i j) (hAdet : A.det ≠ 0) :
    (Matrix.of fun i j ↦ (A * gamma * A.adjugate) i j / A.det).det = 1 := by
  have hdvdT : ∀ i j : Fin n, Aᵀ.det ∣ (Aᵀ.adjugate * gammaᵀ * Aᵀ) i j := fun i j ↦ by
    rw [Matrix.det_transpose, transpose_conj_apply]
    exact hdvd j i
  have h := conj_mat_det_one n Aᵀ gammaᵀ (by rwa [Matrix.det_transpose]) hdvdT
    (by rwa [Matrix.det_transpose])
  have h_transpose : (Matrix.of fun i j ↦ (A * gamma * A.adjugate) i j / A.det) =
      (Matrix.of fun i j ↦ (Aᵀ.adjugate * gammaᵀ * Aᵀ) i j / Aᵀ.det)ᵀ := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.det_transpose,
      transpose_conj_apply]
  rw [h_transpose, Matrix.det_transpose]
  exact h

omit [NeZero n] in
/-- Reverse direction of `int_mul_eq`, derived from it at `Aᵀ`, `γᵀ`: `δ * A = A * γ` where
`δ = (A * γ * adj(A)) / det(A)`. -/
private lemma int_mul_eq_reverse (A gamma : Matrix (Fin n) (Fin n) ℤ) (hAdet : A.det ≠ 0)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A * gamma * A.adjugate) i j) :
    (Matrix.of fun i j ↦ (A * gamma * A.adjugate) i j / A.det) * A = A * gamma := by
  have hdvdT : ∀ i j : Fin n, Aᵀ.det ∣ (Aᵀ.adjugate * gammaᵀ * Aᵀ) i j := fun i j ↦ by
    rw [Matrix.det_transpose, transpose_conj_apply]
    exact hdvd j i
  have h := int_mul_eq n Aᵀ gammaᵀ (by rwa [Matrix.det_transpose]) hdvdT
  have h_transpose : (Matrix.of fun i j ↦ (Aᵀ.adjugate * gammaᵀ * Aᵀ) i j / Aᵀ.det) =
      (Matrix.of fun i j ↦ (A * gamma * A.adjugate) i j / A.det)ᵀ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.det_transpose,
      transpose_conj_apply]
  rw [h_transpose] at h
  have h2 := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose] at h2

/-- Reverse direction of `inv_conjugate_mem_SLnZ_of_mem_ker`: if `g` has integer matrix `A`
and `γ ∈ SL_n(ℤ)` is congruent to the identity modulo `|det A|`, then `g γ g⁻¹` is again in
`SL_n(ℤ)`. -/
lemma conjugate_mem_SLnZ_of_mem_ker (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ))
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker) :
    g * (γ : GL (Fin n) ℚ) * g⁻¹ ∈ SLnZ n := by
  have hAdet : A.det ≠ 0 := det_ne_zero_of_val_eq n g hA
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet⟩
  have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) :=
    fun i j ↦ Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ i j)
  have hdvd := conj_dvd_reverse n A γ.val h_entry
  set delta_mat := Matrix.of fun i j ↦ (A * γ.val * A.adjugate) i j / A.det
  have hdelta_det : delta_mat.det = 1 :=
    conj_mat_det_one_reverse n A γ.val γ.prop hdvd hAdet
  set delta : SpecialLinearGroup (Fin n) ℤ := ⟨delta_mat, hdelta_det⟩
  have h_int_eq : delta_mat * A = A * γ.val := int_mul_eq_reverse n A γ.val hAdet hdvd
  have h_mat_eq : ((delta : GL (Fin n) ℚ) * g).val = (g * (γ : GL (Fin n) ℚ)).val := by
    -- unit multiplication is definitionally matrix multiplication of the coordinates;
    -- `change` states it since no rewriting lemma unfolds `Units.val` products here
    change ((delta : GL (Fin n) ℚ).val * g.val : Matrix _ _ ℚ) =
      (g.val * (γ : GL (Fin n) ℚ).val : Matrix _ _ ℚ)
    simp only [mapGL_coe_matrix, algebraMap_int_eq,
      map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom] at hA ⊢
    rw [hA]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq]
  have h_unit_eq : (delta : GL (Fin n) ℚ) * g = g * (γ : GL (Fin n) ℚ) := Units.ext h_mat_eq
  have h_conj : g * (γ : GL (Fin n) ℚ) * g⁻¹ = (delta : GL (Fin n) ℚ) := by
    rw [← h_unit_eq, mul_inv_cancel_right]
  rw [SLnZ, MonoidHom.mem_range, h_conj]
  exact ⟨delta, rfl⟩

omit [NeZero n] in
/-- The image in `GL_n(ℚ)` of the congruence kernel `Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))`
    has nonzero relative index in `SL_n(ℤ)`: it is a finite-index congruence subgroup. -/
private lemma congruence_ker_image_relIndex_ne_zero (d : ℕ) [NeZero d] :
    (Subgroup.map (mapGL ℚ) (SpecialLinearGroup.map (Int.castRingHom (ZMod d))).ker).relIndex
      (SLnZ n) ≠ 0 := by
  set phi : SpecialLinearGroup (Fin n) ℤ →* SpecialLinearGroup (Fin n) (ZMod d) :=
    SpecialLinearGroup.map (Int.castRingHom (ZMod d))
  have h_map : SLnZ n =
      Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ) ⊤ := by
    simp [SLnZ, MonoidHom.range_eq_map]
  rw [h_map, Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
  exact (Subgroup.finiteIndex_ker phi).index_ne_zero

/-- The image of the congruence kernel lies inside `g • SL_n(ℤ)`: conjugating a kernel
    element by `g⁻¹` keeps it integral (`inv_conjugate_mem_SLnZ_of_mem_ker`). -/
private lemma congruence_ker_image_le_conj (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    Subgroup.map (mapGL ℚ) (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker ≤
      ConjAct.toConjAct g • SLnZ n := by
  rintro x ⟨γ, hγ_ker, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  -- the pointwise-smul membership unfolds definitionally to a `ConjAct` action on the
  -- element; `change` states it so the `ConjAct.smul_def` rewrite applies
  change (ConjAct.toConjAct g)⁻¹ • (γ : GL (Fin n) ℚ) ∈ SLnZ n
  rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
  exact inv_conjugate_mem_SLnZ_of_mem_ker n g A hA γ hγ_ker

/-- The image of the congruence kernel lies inside `g⁻¹ • SL_n(ℤ)`: conjugating a kernel
    element by `g` keeps it integral (`conjugate_mem_SLnZ_of_mem_ker`). -/
private lemma congruence_ker_image_le_conj_inv (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    Subgroup.map (mapGL ℚ) (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker ≤
      ConjAct.toConjAct g⁻¹ • SLnZ n := by
  rintro x ⟨γ, hγ_ker, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [ConjAct.toConjAct_inv, inv_inv]
  -- the pointwise-smul membership unfolds definitionally to a `ConjAct` action on the
  -- element; `change` states it so the `ConjAct.smul_def` rewrite applies
  change ConjAct.toConjAct g • (γ : GL (Fin n) ℚ) ∈ SLnZ n
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  exact conjugate_mem_SLnZ_of_mem_ker n g A hA γ hγ_ker

/-- Every integral-entry element of `GL_n(ℚ)` lies in the commensurator of `SL_n(ℤ)`
(Shimura Lemma 3.10): if `α` has integer entries with `|det(α)| = d` — nonzero, since
invertibility already forces the determinant of an integral witness to be nonzero, so
positivity is not needed — then the congruence subgroup `Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))`
has finite index in `SL_n(ℤ)` and is contained in both `SL_n(ℤ) ∩ α·SL_n(ℤ)·α⁻¹` and
`SL_n(ℤ) ∩ α⁻¹·SL_n(ℤ)·α`, establishing commensurability. -/
lemma mem_commensurator_of_hasIntEntries {g : GL (Fin n) ℚ} (hg : HasIntEntries n g) :
    g ∈ commensurator (SLnZ n) := by
  obtain ⟨A, hA⟩ := hg
  rw [commensurator_mem_iff]
  set H := SLnZ n
  have hAdet_ne : A.det ≠ 0 := det_ne_zero_of_val_eq n g hA
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
  set K := (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker.map
    (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ)
  have hK_relIndex : K.relIndex H ≠ 0 := congruence_ker_image_relIndex_ne_zero n A.det.natAbs
  have hK_le_gH : K ≤ ConjAct.toConjAct g • H := congruence_ker_image_le_conj n g A hA
  have hK_le_ginvH : K ≤ ConjAct.toConjAct g⁻¹ • H :=
    congruence_ker_image_le_conj_inv n g A hA
  refine ⟨ne_zero_of_dvd_ne_zero hK_relIndex (Subgroup.relIndex_dvd_of_le_left H hK_le_gH), ?_⟩
  have h1 : ConjAct.toConjAct g⁻¹ • (ConjAct.toConjAct g • H) = H := by
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [(Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct g⁻¹) H
    (ConjAct.toConjAct g • H)).symm.trans (by rw [h1])]
  exact ne_zero_of_dvd_ne_zero hK_relIndex (Subgroup.relIndex_dvd_of_le_left H hK_le_ginvH)

/-- `Δ ⊆ commensurator(SL_n(ℤ))`, by projection: a positive-determinant integral matrix is
in particular integral. -/
lemma posDetInt_le_commensurator :
    posDetInt n ≤ (commensurator (SLnZ n)).toSubmonoid := fun _ hg ↦
  (Subgroup.mem_toSubmonoid _ _).mpr
    (mem_commensurator_of_hasIntEntries n hg.1)

/-- **The arithmetic Hecke triple for `GL_n`**: `SL_n(ℤ) ≤ Δ ≤ commensurator(SL_n(ℤ))` in
`GL_n(ℚ)`, where `Δ` is the positive-determinant integral submonoid. This is the Hecke triple
underlying the classical Hecke operators, following Shimura §3.2. -/
instance : IsHeckeTriple (posDetInt n) (SLnZ n) (SLnZ n) :=
  IsHeckeTriple.of_diagonal (SLnZ_le_posDetInt n) (posDetInt_le_commensurator n)

end Pair

section API

open scoped HeckeCosetModule

/-- The Hecke ring of `GL_n` over `ℤ`: the Hecke ring of the arithmetic triple. -/
abbrev IntegralHeckeRing := 𝕋 (posDetInt n) (SLnZ n) ℤ

variable [NeZero n]

end API

end HeckeRing.GLn
