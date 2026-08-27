/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
import Mathlib.Data.Matrix.Basis

/-!
# The normalizer of the diagonal torus

Over a field with at least two units, an invertible matrix normalizes the diagonal torus exactly
when it is monomial: it is a diagonal matrix followed by a permutation matrix.  The permutation
is unique, and multiplication of monomial matrices multiplies these permutations.  Consequently
the quotient of the normalizer by the diagonal torus is canonically the symmetric group.

This is the group-of-points calculation behind the Weyl group of the diagonal maximal torus in
`GL_n`.  It complements `TauCeti.SplitTorus.coordinatePermMulEquivWeylGroup`, which identifies the
Weyl group of the corresponding coordinate root datum with the same permutation group.

## Main declarations

* `TauCeti.permutationGL`: the permutation-matrix embedding in `GL`.
* `TauCeti.mem_normalizer_diagonalTorus_iff_exists`: normalizing matrices are precisely products
  of a diagonal matrix and a permutation matrix.
* `TauCeti.diagonalNormalizerPerm`: the permutation homomorphism from the normalizer.
* `TauCeti.diagonalNormalizer_mul_diagGL_mul_inv`: conjugation by a normalizer element relabels
  diagonal coordinates by its coordinate permutation.
* `TauCeti.diagonalNormalizerQuotientMulEquivPerm`: the normalizer quotient is the symmetric
  group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances Layer 7, "Borel subgroups, maximal tori" and "Root datum `(G, T)`", of the
ReductiveGroups roadmap through the standard split maximal torus of `GL_n`.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} {n : ℕ}

section Permutation

variable [Semiring k]

/-- A permutation as an invertible matrix.  The inverse in the matrix entry is what makes this a
homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationGL {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Equiv.Perm ι →* GL ι k :=
  (Matrix.permMatrixHom (R := k)).toHomUnits

/-- The matrix underlying `permutationGL σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem permutationGL_coe {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (permutationGL (k := k) σ : Matrix ι ι k) = σ⁻¹.permMatrix k :=
  by
    rw [permutationGL, MonoidHom.coe_toHomUnits]
    rfl

/-- Conjugating a diagonal matrix by a permutation matrix relabels its diagonal entries. -/
@[simp]
theorem permutationGL_mul_diagGL_mul_inv (σ : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    permutationGL (k := k) σ * diagGL t * (permutationGL (k := k) σ)⁻¹ =
      diagGL (fun i ↦ t (σ⁻¹ i)) := by
  rw [mul_diagGL_of_coe_eq_permMatrix
    (g := permutationGL (k := k) σ) (π := σ⁻¹) (permutationGL_coe σ),
    mul_inv_cancel_right]
  congr

/-- Permutation matrices normalize the diagonal torus. -/
theorem permutationGL_mem_normalizer (σ : Equiv.Perm (Fin n)) :
    permutationGL (k := k) σ ∈
      Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rw [mem_diagonalTorus_iff_exists_diagGL]
    rintro ⟨t, rfl⟩
    rw [permutationGL_mul_diagGL_mul_inv]
    exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨fun i ↦ t (σ⁻¹ i), rfl⟩
  · intro hd
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hd
    have hback := permutationGL_mul_diagGL_mul_inv (k := k) (n := n) σ⁻¹ t
    rw [map_inv, inv_inv] at hback
    have hback' : (permutationGL (k := k) σ)⁻¹ * diagGL t *
        permutationGL (k := k) σ = diagGL (fun i ↦ t (σ i)) := by
      simpa only [inv_inv] using hback
    rw [ht] at hback'
    group at hback'
    rw [mem_diagonalTorus_iff_exists_diagGL]
    exact ⟨fun i ↦ t (σ i), hback'.symm⟩

end Permutation

section Field

variable [Field k] [Nontrivial kˣ]

omit [Nontrivial kˣ] in
private theorem mul_single_one_mul_apply
    (A B : Matrix (Fin n) (Fin n) k) (i j l : Fin n) :
    (A * (Matrix.single j j 1 : Matrix (Fin n) (Fin n) k) * B) i l =
      A i j * B j l := by
  classical
  let E : Matrix (Fin n) (Fin n) k := Matrix.single j j 1
  -- Naming the coordinate idempotent fixes the matrix multiplication instance during rewriting.
  change (A * E * B) i l = A i j * B j l
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  calc
    ∑ r, A i r * (E * B) r l = A i j * (E * B) j l := by
      apply Finset.sum_eq_single j
      · intro r _ hr
        simp [E, hr]
      · simp
    _ = A i j * B j l := by simp [E]

private theorem conjugate_single_isDiag {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (j : Fin n) :
    ((g : Matrix (Fin n) (Fin n) k) * Matrix.single j j 1 *
      ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).IsDiag := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : kˣ, u ≠ 1 := exists_ne 1
  let d : Fin n → kˣ := fun i ↦ if i = j then u else 1
  have hd : diagGL d ∈ diagonalTorus k n :=
    mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩
  have hconj : g * diagGL d * g⁻¹ ∈ diagonalTorus k n :=
    (Subgroup.mem_normalizer_iff.mp hg (diagGL d)).mp hd
  have hdiag : ((g * diagGL d * g⁻¹ : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k).IsDiag := mem_diagonalTorus_iff.mp hconj
  intro i l hil
  let G : Matrix (Fin n) (Fin n) k := g
  let Ginv : Matrix (Fin n) (Fin n) k := (g⁻¹ : GL (Fin n) k)
  let E : Matrix (Fin n) (Fin n) k := Matrix.single j j 1
  have hzero : (G * (diagGL d : Matrix (Fin n) (Fin n) k) * Ginv) i l = 0 := by
    simpa only [G, Ginv, Units.val_mul] using hdiag hil
  have hunit : (u : k) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hu (Units.ext h)
  have hdmat : (diagGL d : Matrix (Fin n) (Fin n) k) =
      1 + ((u : k) - 1) • Matrix.single j j 1 := by
    have hdval : (fun i ↦ (d i : k)) =
        (fun _ ↦ (1 : k)) + Pi.single j ((u : k) - 1) := by
      funext a
      by_cases haj : a = j
      · subst a
        simp [d]
      · simp [d, haj]
    rw [diagGL_coe, hdval]
    -- Expose the function addition so `diagonal_add` identifies the coordinate summand.
    change Matrix.diagonal (fun i : Fin n ↦
      (1 : k) + (Pi.single j ((u : k) - 1) : Fin n → k) i) = _
    rw [← Matrix.diagonal_add, Matrix.diagonal_one,
      Matrix.diagonal_single, Matrix.smul_single, smul_eq_mul, mul_one]
  have hentry :
      (G * E * Ginv) i l = 0 := by
    rw [hdmat] at hzero
    have hmatrix : G * (1 + ((u : k) - 1) • E) * Ginv =
        G * Ginv + ((u : k) - 1) • (G * E * Ginv) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.mul_smul, Matrix.smul_mul]
    have hGG : G * Ginv = 1 := by
      simpa only [G, Ginv, ← Units.inv_eq_val_inv] using g.val_inv
    have hcalc :
        (G * (1 + ((u : k) - 1) • E) * Ginv) i l =
          ((u : k) - 1) * ((G * E * Ginv) i l) := by
      rw [hmatrix, hGG, Matrix.add_apply, Matrix.one_apply_ne hil,
        Matrix.smul_apply, zero_add, smul_eq_mul]
    rw [hcalc] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hunit
  simpa only [G, Ginv, E] using hentry

private theorem existsUnique_ne_zero_column {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (j : Fin n) : ∃! i, (g : Matrix (Fin n) (Fin n) k) i j ≠ 0 := by
  classical
  let G : Matrix (Fin n) (Fin n) k := g
  let Ginv : Matrix (Fin n) (Fin n) k := (g⁻¹ : GL (Fin n) k)
  have hleft : Ginv * G = 1 := by
    simpa only [G, Ginv, ← Units.inv_eq_val_inv] using g.inv_val
  have hcol : ∃ i, G i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    have hjj := congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M j j) hleft
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
    simp only [h, mul_zero, Finset.sum_const_zero] at hjj
    exact zero_ne_one hjj
  obtain ⟨i, hi⟩ := hcol
  refine ⟨i, hi, ?_⟩
  intro l hl
  have hdiag := conjugate_single_isDiag hg j
  have hinv_zero (r : Fin n) (hri : r ≠ i) : Ginv j r = 0 := by
    have hoff :
        (((g : Matrix (Fin n) (Fin n) k) * Matrix.single j j 1 *
          ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
            Matrix (Fin n) (Fin n) k) i r = 0 :=
      hdiag hri.symm
    have hmul : G i j * Ginv j r = 0 := by
      simpa only [G, Ginv, mul_single_one_mul_apply] using hoff
    exact (mul_eq_zero.mp hmul).resolve_left hi
  have hsum : ∑ r, Ginv j r * G r j = 1 := by
    have hjj := congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M j j) hleft
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq] using hjj
  have hsingle : ∑ r, Ginv j r * G r j = Ginv j i * G i j := by
    apply Finset.sum_eq_single i
    · intro r _ hri
      rw [hinv_zero r hri, zero_mul]
    · simp
  have hinv : Ginv j i ≠ 0 := by
    intro h
    rw [hsingle, h, zero_mul] at hsum
    exact zero_ne_one hsum
  by_contra hil
  have hoff :
      (((g : Matrix (Fin n) (Fin n) k) * Matrix.single j j 1 *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
          Matrix (Fin n) (Fin n) k) l i = 0 :=
    hdiag hil
  have hmul : G l j * Ginv j i = 0 := by
    simpa only [G, Ginv, mul_single_one_mul_apply] using hoff
  exact hinv ((mul_eq_zero.mp hmul).resolve_left (by simpa only [G] using hl))

/-- The row containing the unique nonzero entry in a column of a normalizer element. -/
private noncomputable def diagonalNormalizerRow
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) (j : Fin n) : Fin n :=
  Classical.choose (existsUnique_ne_zero_column g.property j)

private theorem diagonalNormalizerRow_ne_zero
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) (j : Fin n) :
    ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (diagonalNormalizerRow g j) j ≠ 0 :=
  (Classical.choose_spec (existsUnique_ne_zero_column g.property j)).1

private theorem eq_diagonalNormalizerRow_of_ne_zero
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    {i j : Fin n}
    (hij : ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ≠ 0) :
    i = diagonalNormalizerRow g j :=
  (Classical.choose_spec (existsUnique_ne_zero_column g.property j)).2 i hij

omit [Nontrivial kˣ] in
private theorem mul_apply_eq_single_of_column_support
    (A B : Matrix (Fin n) (Fin n) k) (i j l : Fin n)
    (huniq : ∀ r, A r l ≠ 0 → r = i) :
    (B * A) j l = B j i * A i l := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro r _ hri
    have hz : A r l = 0 := by
      by_contra hr
      exact hri (huniq r hr)
    rw [hz, mul_zero]
  · simp

private theorem diagonalNormalizerRow_injective
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    Function.Injective (diagonalNormalizerRow g) := by
  intro j l hjl
  by_contra hjl'
  let G : Matrix (Fin n) (Fin n) k := (g : GL (Fin n) k)
  let Ginv : Matrix (Fin n) (Fin n) k := ((g : GL (Fin n) k)⁻¹ : GL (Fin n) k)
  have hleft : Ginv * G = 1 := by
    simpa only [G, Ginv, ← Units.inv_eq_val_inv] using (g : GL (Fin n) k).inv_val
  have hj := diagonalNormalizerRow_ne_zero g j
  have hl := diagonalNormalizerRow_ne_zero g l
  have hjuniq : ∀ r, G r j ≠ 0 → r = diagonalNormalizerRow g j := by
    intro r hr
    exact eq_diagonalNormalizerRow_of_ne_zero g (by simpa only [G] using hr)
  have hluniq : ∀ r, G r l ≠ 0 → r = diagonalNormalizerRow g l := by
    intro r hr
    exact eq_diagonalNormalizerRow_of_ne_zero g (by simpa only [G] using hr)
  have hprod_one : Ginv j (diagonalNormalizerRow g j) *
      G (diagonalNormalizerRow g j) j = 1 := by
    rw [← mul_apply_eq_single_of_column_support G Ginv _ _ _
      hjuniq, hleft, Matrix.one_apply_eq]
  have hprod_zero : Ginv j (diagonalNormalizerRow g l) *
      G (diagonalNormalizerRow g l) l = 0 := by
    rw [← mul_apply_eq_single_of_column_support G Ginv _ _ _
      hluniq, hleft, Matrix.one_apply_ne hjl']
  rw [← hjl] at hprod_zero
  have hinv : Ginv j (diagonalNormalizerRow g j) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod_one
    exact zero_ne_one hprod_one
  have hl' : G (diagonalNormalizerRow g j) l ≠ 0 := by
    rw [hjl]
    simpa only [G] using hl
  exact hinv ((mul_eq_zero.mp hprod_zero).resolve_right hl')

/-- The permutation of rows selected by the columns of a normalizer element. -/
private noncomputable def diagonalNormalizerEquiv
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (diagonalNormalizerRow g)
    (diagonalNormalizerRow_injective g).bijective_of_finite

@[simp]
private theorem diagonalNormalizerEquiv_apply
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) (j : Fin n) :
    diagonalNormalizerEquiv g j = diagonalNormalizerRow g j :=
  rfl

/-- An invertible matrix normalizes the diagonal torus exactly when it is a diagonal matrix
followed by a permutation matrix. -/
theorem mem_normalizer_diagonalTorus_iff_exists {g : GL (Fin n) k} :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) ↔
      ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n),
        g = diagGL d * permutationGL (k := k) σ := by
  classical
  constructor
  · intro hg
    let gn : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) := ⟨g, hg⟩
    let e : Equiv.Perm (Fin n) := diagonalNormalizerEquiv gn
    have hcoeff (i : Fin n) :
        (g : Matrix (Fin n) (Fin n) k) i (e.symm i) ≠ 0 := by
      have h := diagonalNormalizerRow_ne_zero gn (e.symm i)
      simpa only [gn, e, ← diagonalNormalizerEquiv_apply,
        Equiv.apply_symm_apply] using h
    let d : Fin n → kˣ := fun i ↦
      Units.mk0 ((g : Matrix (Fin n) (Fin n) k) i (e.symm i)) (hcoeff i)
    refine ⟨d, e, ?_⟩
    apply Units.ext
    ext i j
    simp only [Units.val_mul, diagGL_coe, permutationGL_coe]
    rw [Matrix.diagonal_mul]
    by_cases hij : i = e j
    · subst i
      simp [d]
    · have hzero : (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
        by_contra h
        exact hij (by
          simpa only [e, diagonalNormalizerEquiv_apply] using
            eq_diagonalNormalizerRow_of_ne_zero gn h)
      rw [hzero]
      simp [Equiv.Perm.permMatrix, Equiv.symm_apply_eq, hij]
  · rintro ⟨d, σ, rfl⟩
    exact (Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))).mul_mem
      (Subgroup.le_normalizer (by
        exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
      (permutationGL_mem_normalizer σ)

omit [Nontrivial kˣ] in
private theorem permutation_eq_of_diagGL_mul_permutationGL_eq
    {d e : Fin n → kˣ} {σ τ : Equiv.Perm (Fin n)}
    (h : diagGL d * permutationGL (k := k) σ =
      diagGL e * permutationGL (k := k) τ) : σ = τ := by
  apply Equiv.ext
  intro j
  by_contra hj
  have hentry := congrArg
    (fun x : GL (Fin n) k ↦ (x : Matrix (Fin n) (Fin n) k) (σ j) j) h
  simp only [Units.val_mul, diagGL_coe, permutationGL_coe,
    Matrix.diagonal_mul] at hentry
  have hleft : (σ⁻¹.permMatrix k) (σ j) j = 1 := by
    simp [Equiv.Perm.permMatrix]
  have hright : (τ⁻¹.permMatrix k) (σ j) j = 0 := by
    simp [Equiv.Perm.permMatrix, Equiv.symm_apply_eq, hj]
  rw [hleft, hright, mul_one, mul_zero] at hentry
  exact Units.ne_zero (d (σ j)) hentry

/-- The diagonal factor in the chosen monomial factorization of a normalizer element. -/
private noncomputable def diagonalNormalizerDiag
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) : Fin n → kˣ :=
  Classical.choose (mem_normalizer_diagonalTorus_iff_exists.mp g.property)

/-- The permutation factor in the chosen monomial factorization of a normalizer element. -/
private noncomputable def diagonalNormalizerPermFun
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    Equiv.Perm (Fin n) :=
  Classical.choose (Classical.choose_spec
    (mem_normalizer_diagonalTorus_iff_exists.mp g.property))

private theorem diagonalNormalizer_factor
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    (g : GL (Fin n) k) = diagGL (diagonalNormalizerDiag g) *
      permutationGL (k := k) (diagonalNormalizerPermFun g) :=
  Classical.choose_spec (Classical.choose_spec
    (mem_normalizer_diagonalTorus_iff_exists.mp g.property))

private theorem diagonalNormalizerPermFun_one :
    diagonalNormalizerPermFun
      (1 : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) = 1 := by
  have hone : (1 : GL (Fin n) k) =
      diagGL (fun _ ↦ (1 : kˣ)) * permutationGL (k := k) 1 := by
    -- Present both factors as images of the identity under their defining homomorphisms.
    change 1 = diagGL (1 : Fin n → kˣ) * permutationGL (k := k) 1
    rw [map_one, map_one, mul_one]
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor 1).symm.trans hone

private theorem diagonalNormalizerPermFun_mul
    (g h : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerPermFun (g * h) =
      diagonalNormalizerPermFun g * diagonalNormalizerPermFun h := by
  let σ := diagonalNormalizerPermFun g
  let τ := diagonalNormalizerPermFun h
  let d := diagonalNormalizerDiag g
  let e := diagonalNormalizerDiag h
  have hmove : permutationGL (k := k) σ * diagGL e =
      diagGL (fun i ↦ e (σ⁻¹ i)) * permutationGL (k := k) σ :=
    mul_diagGL_of_coe_eq_permMatrix (permutationGL (k := k) σ) σ⁻¹
      (permutationGL_coe σ) e
  have hfactor : ((g * h :
      Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) : GL (Fin n) k) =
      diagGL (fun i ↦ d i * e (σ⁻¹ i)) * permutationGL (k := k) (σ * τ) := by
    -- Forget the normalizer subtype so the two chosen monomial factorizations can be substituted.
    change (g : GL (Fin n) k) * (h : GL (Fin n) k) = _
    rw [diagonalNormalizer_factor g, diagonalNormalizer_factor h]
    -- Name the four factors before moving the middle diagonal past the permutation matrix.
    change (diagGL d * permutationGL (k := k) σ) *
      (diagGL e * permutationGL (k := k) τ) = _
    rw [mul_assoc, ← mul_assoc (permutationGL (k := k) σ), hmove]
    have hdiag : diagGL (fun i ↦ d i * e (σ⁻¹ i)) =
        diagGL d * diagGL (fun i ↦ e (σ⁻¹ i)) := by
      rw [← map_mul]
      rfl
    rw [hdiag, map_mul (permutationGL (k := k)) σ τ]
    group
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor (g * h)).symm.trans hfactor

/-- The permutation of coordinate lines induced by a matrix normalizing the diagonal torus. -/
noncomputable def diagonalNormalizerPerm :
    Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) →*
      Equiv.Perm (Fin n) where
  toFun := diagonalNormalizerPermFun
  map_one' := diagonalNormalizerPermFun_one
  map_mul' := diagonalNormalizerPermFun_mul

/-- A monomial factorization of a diagonal-normalizer element has the coordinate permutation
selected by `diagonalNormalizerPerm`. -/
theorem diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (d : Fin n → kˣ) (σ : Equiv.Perm (Fin n))
    (h : (g : GL (Fin n) k) = diagGL d * permutationGL (k := k) σ) :
    diagonalNormalizerPerm (k := k) (n := n) g = σ := by
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor g).symm.trans h

/-- The coordinate permutation induced by a permutation matrix is the original permutation. -/
@[simp]
theorem diagonalNormalizerPerm_permutationGL (σ : Equiv.Perm (Fin n)) :
    diagonalNormalizerPerm (k := k) (n := n)
        ⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩ = σ := by
  have hone : permutationGL (k := k) σ =
      diagGL (fun _ ↦ (1 : kˣ)) * permutationGL (k := k) σ := by
    -- Present the trivial diagonal factor as the image of the identity.
    change permutationGL (k := k) σ =
      diagGL (1 : Fin n → kˣ) * permutationGL (k := k) σ
    rw [map_one, one_mul]
  exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ _ σ hone

/-- Conjugation by a diagonal-normalizer element relabels the diagonal entries by its coordinate
permutation: the entry at `i` becomes the original entry at the inverse image of `i`. -/
@[simp]
theorem diagonalNormalizer_mul_diagGL_mul_inv
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (t : Fin n → kˣ) :
    (g : GL (Fin n) k) * diagGL t * (g : GL (Fin n) k)⁻¹ =
      diagGL (fun i ↦ t ((diagonalNormalizerPerm (k := k) (n := n) g).symm i)) := by
  obtain ⟨d, σ, hg⟩ := mem_normalizer_diagonalTorus_iff_exists.mp g.property
  have hσ := diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL g d σ hg
  rw [hσ, hg]
  calc
    (diagGL d * permutationGL (k := k) σ) * diagGL t *
          (diagGL d * permutationGL (k := k) σ)⁻¹ =
        diagGL d *
          (permutationGL (k := k) σ * diagGL t *
            (permutationGL (k := k) σ)⁻¹) * (diagGL d)⁻¹ := by group
    _ = diagGL d * diagGL (fun i ↦ t (σ⁻¹ i)) * (diagGL d)⁻¹ := by
      rw [permutationGL_mul_diagGL_mul_inv]
    _ = diagGL (fun i ↦ t (σ⁻¹ i)) := by
      have hcomm : Commute (diagGL d) (diagGL (fun i ↦ t (σ⁻¹ i))) :=
        (Commute.all d (fun i ↦ t (σ⁻¹ i))).map diagGL
      rw [hcomm.eq]
      simp

/-- Every coordinate permutation is induced by a permutation matrix in the normalizer. -/
theorem diagonalNormalizerPerm_surjective :
    Function.Surjective (diagonalNormalizerPerm (k := k) (n := n)) := by
  intro σ
  exact ⟨⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩,
    diagonalNormalizerPerm_permutationGL σ⟩

/-- The coordinate permutation induced by a normalizer element is trivial exactly for elements
of the diagonal torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerPerm (k := k) (n := n) g = 1 ↔
      (g : GL (Fin n) k) ∈ diagonalTorus k n := by
  constructor
  · intro hg
    have hfactor := diagonalNormalizer_factor g
    -- Unfold only the homomorphism's value, keeping the chosen factorization opaque.
    change diagonalNormalizerPermFun g = 1 at hg
    rw [hg, map_one, mul_one] at hfactor
    exact mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨diagonalNormalizerDiag g, hfactor.symm⟩
  · intro hg
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    have hone : (g : GL (Fin n) k) =
        diagGL d * permutationGL (k := k) 1 := by
      rw [map_one, mul_one, hd]
    exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL g d 1 hone

/-- The normalizer of the diagonal torus modulo the torus is canonically the symmetric group. -/
noncomputable def diagonalNormalizerQuotientMulEquivPerm :
    Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n)
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (GL (Fin n) k)),
      (g : GL (Fin n) k) ∈ diagonalTorus k n → φ g = 1 := by
    intro g hg
    exact (diagonalNormalizerPerm_eq_one_iff g).mpr hg
  let φbar := Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill
  apply MulEquiv.ofBijective φbar
  constructor
  · exact (Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr diagonalNormalizerPerm_eq_one_iff
  · exact Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill diagonalNormalizerPerm_surjective

/-- The quotient equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)
        (g : Subgroup.normalizerQuotient (diagonalTorus k n)) =
      diagonalNormalizerPerm (k := k) (n := n) g :=
  by
    unfold diagonalNormalizerQuotientMulEquivPerm
    rfl

/-- The inverse quotient equivalence sends a coordinate permutation to the class of its
permutation matrix. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).symm σ =
      Subgroup.normalizerQuotientMk (diagonalTorus k n)
        ⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩ := by
  apply (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).injective
  simp

end Field

end

end TauCeti
