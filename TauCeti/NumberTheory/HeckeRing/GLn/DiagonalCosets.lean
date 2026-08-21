/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
public import TauCeti.NumberTheory.HeckeRing.One

import TauCeti.LinearAlgebra.Matrix.SmithNormalForm
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal

/-!
# Diagonal coset representatives for the `GL_n` Hecke ring

The double cosets `T(a₁,...,aₙ) = SL_n(ℤ) · diag(a₁,...,aₙ) · SL_n(ℤ)` attached to diagonal
matrices with positive integer entries, and the elementary divisor theorem for the arithmetic
Hecke triple: the map from positive divisibility chains `a₁ ∣ a₂ ∣ ⋯ ∣ aₙ` to double cosets
in `SL_n(ℤ) \ Δ / SL_n(ℤ)` is a bijection, so these classes span the Hecke ring freely.
Following [Shimura][shimura1971], §3.2.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), on top of the matrix-level Smith normal form
`Matrix.exists_smith_normal_form_of_det_pos` and its uniqueness
`Matrix.smith_normal_form_unique`.

## Main definitions

* `natDiagGL`: the diagonal matrix `diag(a₁,...,aₙ)` as an element of `GL_n(ℚ)`.
* `IsDvdChain`: the divisibility condition `a i ∣ a j` for `i ≤ j`.
* `diagCoset`: the double coset `SL_n(ℤ) · diag(a₁,...,aₙ) · SL_n(ℤ)`.
* `diagElem`: the Hecke ring element `T(a₁,...,aₙ)`, the coset with coefficient `1`.

## Main results

* `exists_diagonal_representative`: every double coset of the arithmetic Hecke triple is
  `diagCoset a` for a positive divisibility chain `a` (Smith normal form).
* `diagCoset_bijective`: positive divisibility chains biject with the double cosets.
* `diagCosetEquiv`: that bijection as an equivalence, the canonical index of the double
  cosets.
* `span_diagElem_eq_top`: the elements `T(a₁,...,aₙ)` span the Hecke ring.
* `diagElem_mul_of_mulMap_eq`: the product criterion `T(a) · T(b) = T(c)`, given that the
  coset decomposition multiplies into `T(c)` alone and does so with multiplicity at most one.
  The `GL_n` reading of `HeckeCosetModule.mul_single_single_of_mulMap_eq`, which carries the
  argument at the level of arbitrary Hecke cosets and coefficients.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open Matrix Matrix.SpecialLinearGroup DoubleCoset

namespace HeckeRing.GLn

variable (n : ℕ)

section Diagonal

/-- The diagonal `GL_n(ℚ)` element `diag(a₁,...,aₙ)` with positive natural number entries.
Returns `1` (the identity matrix) when the positivity condition `∀ i, 0 < a i` fails;
this is a junk value that simplifies the API by avoiding an explicit positivity argument.
Only positivity is needed for a meaningful value — a positive tuple that is not a
divisibility chain still names its genuine diagonal coset. -/
noncomputable def natDiagGL (a : Fin n → ℕ) : GL (Fin n) ℚ :=
  if h : ∀ i, 0 < a i then
    TauCeti.diagGL fun i ↦ Units.mk0 (a i : ℚ) (by exact_mod_cast (h i).ne')
  else 1

@[simp] lemma natDiagGL_coe (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ) =
    Matrix.diagonal (fun i ↦ (a i : ℚ)) := by
  rw [natDiagGL, dite_eq_left ha, TauCeti.diagGL_coe]
  simp

lemma hasIntEntries_natDiagGL (a : Fin n → ℕ) : HasIntEntries n (natDiagGL n a) := by
  rw [natDiagGL]
  split_ifs with h
  · exact (hasIntEntries_iff n).mpr ⟨Matrix.diagonal (fun i ↦ (a i : ℤ)), by
      rw [TauCeti.diagGL_coe]
      ext i j; simp [Matrix.diagonal_apply, Matrix.map_apply]⟩
  · exact hasIntEntries_one n

/-- Positivity is preserved by pointwise products. -/
private lemma pi_mul_pos {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < (a * b) i :=
  fun i ↦ Nat.mul_pos (ha i) (hb i)

/-- The diagonal element is multiplicative in its tuple of entries. -/
@[simp]
lemma natDiagGL_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    natDiagGL n a * natDiagGL n b = natDiagGL n (a * b) := by
  apply Units.ext
  simp [natDiagGL_coe n a ha, natDiagGL_coe n b hb,
    natDiagGL_coe n (a * b) (pi_mul_pos n ha hb), Matrix.diagonal_mul_diagonal,
    Pi.mul_apply, Nat.cast_mul]

lemma natDiagGL_det_pos (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    0 < (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ).det := by
  rw [natDiagGL_coe n a ha, det_diagonal]
  exact Finset.prod_pos (fun i _ ↦ by positivity [ha i])

/-- Membership in Shimura's `Δ` is unconditional: the junk value is the identity. -/
lemma natDiagGL_mem_posDetInt (a : Fin n → ℕ) : natDiagGL n a ∈ posDetInt n := by
  refine (mem_posDetInt_iff n).mpr ⟨hasIntEntries_natDiagGL n a, ?_⟩
  by_cases ha : ∀ i, 0 < a i
  · exact natDiagGL_det_pos n a ha
  · rw [natDiagGL, dite_eq_right ha]
    simp

lemma natDiagGL_det (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ).det = ∏ i, (a i : ℚ) := by
  rw [natDiagGL_coe n a ha, Matrix.det_diagonal]

/-- The junk branch of `natDiagGL`: without positivity the value is the identity. -/
@[simp] lemma natDiagGL_of_not_pos {a : Fin n → ℕ} (ha : ¬ ∀ i, 0 < a i) :
    natDiagGL n a = 1 :=
  dite_eq_right ha

private lemma natDiagGL_const_eq_scalar {c : ℕ} (hc : 0 < c) :
    natDiagGL n (fun _ ↦ c) =
      Matrix.GeneralLinearGroup.scalar (Fin n)
        (Units.mk0 (c : ℚ) (by exact_mod_cast hc.ne')) := by
  apply Units.ext
  ext i j
  simp only [natDiagGL_coe n _ fun _ ↦ hc, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0]

/-- A constant diagonal matrix is a scalar, hence commutes with everything — unconditionally
in the constant, since `c = 0` sends `natDiagGL` to its junk value `1`. -/
lemma natDiagGL_const_comm (c : ℕ) (g : GL (Fin n) ℚ) :
    natDiagGL n (fun _ ↦ c) * g = g * natDiagGL n (fun _ ↦ c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- at rank zero `GL (Fin 0) ℚ` is trivial
  · exact Subsingleton.elim _ _
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [natDiagGL_of_not_pos n (not_forall.mpr ⟨⟨0, hn⟩, by simp⟩), one_mul, mul_one]
  · rw [natDiagGL_const_eq_scalar n hc]
    exact Matrix.GeneralLinearGroup.scalar_commute _ _

@[simp] lemma natDiagGL_one : natDiagGL n (fun _ ↦ 1) = 1 := by
  ext1
  rw [natDiagGL_coe n _ (fun _ ↦ Nat.one_pos)]
  simp

end Diagonal

/-- The divisibility chain condition on natural-number sequences: entries divide all later entries.
Equivalent to the successive condition `a₁ ∣ a₂ ∣ ⋯ ∣ aₙ` by transitivity of divisibility. -/
def IsDvdChain {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≤ j → a i ∣ a j

/-- Elimination and introduction for the sealed definition `IsDvdChain`. -/
@[simp]
lemma isDvdChain_iff {n : ℕ} {a : Fin n → ℕ} :
    IsDvdChain a ↔ ∀ ⦃i j : Fin n⦄, i ≤ j → a i ∣ a j :=
  (Iff.rfl)

lemma isDvdChain_const (c : ℕ) : IsDvdChain (fun _ : Fin n ↦ c) :=
  fun _ _ _ ↦ dvd_refl _

/-- The pointwise product of two divisibility chains is a divisibility chain. Scaling by a
constant `c` is the case where `b` is the constant function, with `hb := isDvdChain_const n c`. -/
lemma isDvdChain_mul {a b : Fin n → ℕ} (ha : IsDvdChain a) (hb : IsDvdChain b) :
    IsDvdChain (a * b) :=
  isDvdChain_iff.mpr fun _ _ hij ↦
    mul_dvd_mul (isDvdChain_iff.mp ha hij) (isDvdChain_iff.mp hb hij)

/-- The positive divisibility chains of length `n`: the parameter space of the diagonal
double cosets. -/
abbrev CanonicalDiagonal (n : ℕ) : Type :=
  {a : Fin n → ℕ // (∀ i, 0 < a i) ∧ IsDvdChain a}

section DiagCoset

variable {n}

/-- `T(a₁,...,aₙ) = Γ · diag(a₁,...,aₙ) · Γ` as a double coset of the arithmetic Hecke
triple. The positivity hypothesis belongs in lemmas, not the definition; the value is junk
when it fails. -/
noncomputable def diagCoset (a : Fin n → ℕ) : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n) :=
  HeckeCoset.mk _ _ ⟨natDiagGL n a, natDiagGL_mem_posDetInt n a⟩

/-- `T(a₁,...,aₙ)` as a Hecke ring element with coefficient `1`. -/
noncomputable def diagElem (a : Fin n → ℕ) : IntegralHeckeRing n :=
  HeckeCosetModule.single ℤ (diagCoset a) 1

/-- The underlying set of `diagCoset a` is the double coset of `natDiagGL n a`. -/
@[simp] lemma diagCoset_toSet (a : Fin n → ℕ) :
    (diagCoset a).toSet = doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) :=
  HeckeCoset.toSet_mk _

/-- Defining equation for the sealed `diagCoset`. -/
lemma diagCoset_def (a : Fin n → ℕ) :
    diagCoset a =
      HeckeCoset.mk (SLnZ n) (SLnZ n) ⟨natDiagGL n a, natDiagGL_mem_posDetInt n a⟩ :=
  (rfl)

/-- The chosen representative of a diagonal coset decomposes as `h₁ · diag(a) · h₂` with
`h₁, h₂ ∈ SL_n(ℤ)`. -/
lemma exists_rep_diagCoset_eq_mul_natDiagGL_mul (a : Fin n → ℕ) :
    ∃ h₁ ∈ SLnZ n, ∃ h₂ ∈ SLnZ n,
      ((diagCoset a).rep : GL (Fin n) ℚ) = h₁ * natDiagGL n a * h₂ := by
  have hmem : ((diagCoset a).rep : GL (Fin n) ℚ) ∈
      doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) := by
    rw [← diagCoset_toSet]
    exact HeckeCoset.rep_mem _
  exact mem_doubleCoset.mp hmem

/-- Defining equation for the sealed `diagElem`. -/
lemma diagElem_def (a : Fin n → ℕ) :
    diagElem a = HeckeCosetModule.single ℤ (diagCoset a) 1 :=
  (rfl)

@[simp] lemma diagCoset_one : diagCoset (fun _ : Fin n ↦ 1) = 1 :=
  congrArg (HeckeCoset.mk _ _) (Subtype.ext (natDiagGL_one n))

/-- The identity normal form: the diagonal Hecke element of the all-ones tuple is `1`. -/
@[simp] lemma diagElem_one : diagElem (fun _ : Fin n ↦ 1) = 1 := by
  rw [diagElem_def, diagCoset_one]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- The junk normal form: a tuple that is not everywhere positive gives the identity double
coset, matching the junk value of `natDiagGL`. -/
@[simp] lemma diagCoset_of_not_pos {a : Fin n → ℕ} (ha : ¬ ∀ i, 0 < a i) : diagCoset a = 1 :=
  congrArg (HeckeCoset.mk _ _) (Subtype.ext (natDiagGL_of_not_pos n ha))

/-- The junk normal form of the Hecke-ring element. -/
@[simp] lemma diagElem_of_not_pos {a : Fin n → ℕ} (ha : ¬ ∀ i, 0 < a i) : diagElem a = 1 := by
  rw [diagElem_def, diagCoset_of_not_pos ha]
  exact (HeckeCosetModule.one_def ℤ).symm

/-- Two diagonal double cosets are equal iff the underlying double cosets in `GL_n(ℚ)`
coincide. -/
lemma diagCoset_eq_iff (a b : Fin n → ℕ) :
    diagCoset a = diagCoset b ↔
    doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) =
    doubleCoset (natDiagGL n b) (SLnZ n) (SLnZ n) := by
  rw [diagCoset, diagCoset, HeckeCoset.eq_iff]

end DiagCoset

section SmithNormalForm

variable {n}

/-- Smith normal form transports the double coset: if `L · A · R` is the diagonal of a
positive natural tuple, the double coset of `α` is that of `natDiagGL n a`. -/
private lemma double_coset_eq_of_SLnZ_equiv (α : posDetInt n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑(↑α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (a : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (L R : SpecialLinearGroup (Fin n) ℤ)
    (hLR : (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal (fun i ↦ (a i : ℤ))) :
    doubleCoset (↑α : GL (Fin n) ℚ) (SLnZ n) (SLnZ n) =
      doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) := by
  symm
  apply doubleCoset_eq_of_mem
  rw [mem_doubleCoset]
  refine ⟨(L : GL (Fin n) ℚ), coe_mem_SLnZ n L, (R : GL (Fin n) ℚ), coe_mem_SLnZ n R, ?_⟩
  apply Units.ext
  rw [natDiagGL_coe n a ha_pos]
  simp only [Units.val_mul, mapGL_coe_matrix, algebraMap_int_eq, hA]
  symm
  calc (↑L : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ) *
      A.map (Int.cast : ℤ → ℚ) * (↑R : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ)
      = ((↑L : Matrix _ _ ℤ) * A).map (Int.cast : ℤ → ℚ) *
        (↑R : Matrix _ _ ℤ).map (Int.cast : ℤ → ℚ) := by
          simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    _ = ((↑L : Matrix _ _ ℤ) * A * (↑R : Matrix _ _ ℤ)).map (Int.cast : ℤ → ℚ) := by
        simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    _ = (Matrix.diagonal (fun i ↦ (a i : ℤ))).map (Int.cast : ℤ → ℚ) := by rw [hLR]
    _ = Matrix.diagonal (fun i ↦ (a i : ℚ)) := by
        rw [Matrix.diagonal_map (by simp)]
        norm_cast

private lemma mk_eq_diagCoset (α : posDetInt n) :
    ∃ a : Fin n → ℕ, (∀ i, 0 < a i) ∧ IsDvdChain a ∧
      HeckeCoset.mk (SLnZ n) (SLnZ n) α = diagCoset a := by
  obtain ⟨hint, hdet⟩ := (mem_posDetInt_iff n).mp α.2
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp hint
  have hdet_pos : 0 < A.det := by
    have h1 : (A.det : ℚ) = (↑(↑α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
      rw [hA]
      simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) A
    exact_mod_cast h1 ▸ hdet
  obtain ⟨L, R, d, hd_pos, hd_div, hLR⟩ := A.exists_smith_normal_form_of_det_pos hdet_pos
  have hd_pos_nat : ∀ i, 0 < (d i).toNat := fun i ↦ by
    linarith [hd_pos i, (Int.toNat_of_nonneg (le_of_lt (hd_pos i))).symm]
  set a : Fin n → ℕ := fun i ↦ (d i).toNat
  have hd_eq : ∀ i, (d i) = (a i : ℤ) := fun i ↦ by
    simp [a, Int.toNat_of_nonneg (le_of_lt (hd_pos i))]
  have hdiv : IsDvdChain a := by
    intro i j hij
    have h1 := hd_div hij
    rw [hd_eq i, hd_eq j] at h1
    exact_mod_cast h1
  refine ⟨a, hd_pos_nat, hdiv, ?_⟩
  rw [diagCoset, HeckeCoset.eq_iff]
  refine double_coset_eq_of_SLnZ_equiv α A hA a hd_pos_nat L R ?_
  rw [hLR]
  exact congrArg Matrix.diagonal (funext hd_eq)

/-- **Existence of diagonal representatives** (Smith normal form): every double coset of the
arithmetic Hecke triple is `diagCoset a` for a positive divisibility chain
`a₁ ∣ a₂ ∣ ⋯ ∣ aₙ`. -/
theorem exists_diagonal_representative (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    ∃ a : Fin n → ℕ, (∀ i, 0 < a i) ∧ IsDvdChain a ∧ D = diagCoset a := by
  obtain ⟨a, hpos, hchain, h⟩ := mk_eq_diagCoset (HeckeCoset.rep D)
  rw [HeckeCoset.mk_rep] at h
  exact ⟨a, hpos, hchain, h⟩

/-- **Uniqueness of elementary divisors**: the entries of a diagonal representative with a
divisibility chain are uniquely determined by the double coset. -/
theorem eq_of_diagCoset_eq {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hda : IsDvdChain a) (hdb : IsDvdChain b)
    (heq : diagCoset a = diagCoset b) : a = b := by
  rw [diagCoset_eq_iff a b] at heq
  have hmem : natDiagGL n b ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) :=
    heq ▸ mem_doubleCoset_self (SLnZ n) (SLnZ n) _
  rw [mem_doubleCoset] at hmem
  obtain ⟨x, hx, y, hy, hmat⟩ := hmem
  obtain ⟨L, rfl⟩ := (mem_SLnZ_iff n).mp hx
  obtain ⟨R, rfl⟩ := (mem_SLnZ_iff n).mp hy
  -- push the `GL_n(ℚ)` identity down to an integer matrix identity
  have hmat_int : (L : Matrix (Fin n) (Fin n) ℤ) *
      Matrix.diagonal (fun i ↦ (a i : ℤ)) * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal (fun i ↦ (b i : ℤ)) := by
    ext i j
    have h := congr_arg (fun (g : GL (Fin n) ℚ) ↦ (↑g : Matrix _ _ ℚ) i j) hmat
    simp only [natDiagGL_coe n a ha, natDiagGL_coe n b hb, Matrix.diagonal_apply,
      Units.val_mul, Matrix.mul_apply, mapGL_coe_matrix, map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, algebraMap_int_eq, eq_intCast] at h
    simp only [Matrix.diagonal_apply, Matrix.mul_apply]
    exact_mod_cast h.symm
  have hcast : (fun i ↦ (a i : ℤ)) = (fun i ↦ (b i : ℤ)) :=
    Matrix.smith_normal_form_unique
      (fun i ↦ by positivity) (fun i ↦ by positivity)
      (fun i j hij ↦ Int.natCast_dvd_natCast.mpr (hda hij))
      (fun i j hij ↦ Int.natCast_dvd_natCast.mpr (hdb hij)) L.toGL R.toGL
      (by simpa using hmat_int)
  funext i
  exact_mod_cast congr_fun hcast i

/-- **Classification of the double cosets** (Shimura §3.2): positive divisibility chains
biject with the double cosets of the arithmetic Hecke triple. -/
theorem diagCoset_bijective :
    Function.Bijective (fun a : CanonicalDiagonal n ↦ diagCoset a.1) := by
  constructor
  · rintro ⟨a, hapos, hachain⟩ ⟨b, hbpos, hbchain⟩ h
    exact Subtype.ext (eq_of_diagCoset_eq hapos hbpos hachain hbchain h)
  · intro D
    obtain ⟨a, hpos, hchain, rfl⟩ := exists_diagonal_representative D
    exact ⟨⟨a, hpos, hchain⟩, rfl⟩

/-- **The canonical index of the double cosets** (Shimura §3.2): the positive divisibility
chains index the double cosets of the arithmetic Hecke triple, so they may be used directly
as the index type and the inverse gives each coset its canonical diagonal. -/
noncomputable def diagCosetEquiv :
    CanonicalDiagonal n ≃ HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n) :=
  Equiv.ofBijective _ diagCoset_bijective

@[simp] lemma diagCosetEquiv_apply (a : CanonicalDiagonal n) :
    diagCosetEquiv a = diagCoset a.1 := (rfl)

/-- The Hecke ring of the arithmetic triple is spanned by the diagonal double coset elements
`T(a₁,...,aₙ)` with positive entries and divisibility chain. -/
theorem span_diagElem_eq_top :
    Submodule.span ℤ (Set.range fun a : CanonicalDiagonal n ↦ diagElem a.1) = ⊤ := by
  have hmem : ∀ (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) (c : ℤ),
      HeckeCosetModule.single ℤ D c ∈ Submodule.span ℤ
        (Set.range fun a : CanonicalDiagonal n ↦ diagElem a.1) := by
    intro D c
    obtain ⟨a, hpos, hchain, hrep⟩ := exists_diagonal_representative D
    subst hrep
    rw [← HeckeCosetModule.smul_single_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, hpos, hchain⟩, rfl⟩)
  rw [Submodule.eq_top_iff']
  intro f
  rw [← HeckeCosetModule.sum_single ℤ f]
  exact Submodule.finsuppSum_mem _ _ _ _ fun D _ ↦ hmem D (f D)

end SmithNormalForm

section ProductCriterion

variable {n}

-- The multiplication this section is about needs the arithmetic Hecke triple, whose
-- instance carries `NeZero n`.
variable [NeZero n]

/-- **The product criterion for diagonal Hecke elements.** If every pair in the coset
decomposition of `T(a) · T(b)` multiplies into the single double coset `T(c)`, and `T(c)`
occurs there with multiplicity at most one, then `T(a) · T(b) = T(c)`.

This is the structure-constant computation shared by every "a product of diagonal elements
is again diagonal" result: the two hypotheses are all that vary between them. Both the
scalar product `diagElem_const_mul` (Shimura 3.17) and the coprime product
`diagElem_mul_of_coprime` (Shimura 3.16) are this lemma applied to their own inputs. -/
theorem diagElem_mul_of_mulMap_eq (a b c : Fin n → ℕ)
    (hmulMap : ∀ p, HeckeCoset.mulMap (SLnZ n) (SLnZ n) (SLnZ n)
      (diagCoset a).rep (diagCoset b).rep p = diagCoset c)
    (hmul : multiplicity (SLnZ n) (SLnZ n) (SLnZ n)
      (((diagCoset a).rep : GL (Fin n) ℚ)) (((diagCoset b).rep : GL (Fin n) ℚ))
      (((diagCoset c).rep : GL (Fin n) ℚ)) ≤ 1) :
    diagElem a * diagElem b = diagElem c := by
  rw [diagElem_def, diagElem_def, diagElem_def]
  exact HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ _ _ _ hmulMap hmul

end ProductCriterion

end HeckeRing.GLn
