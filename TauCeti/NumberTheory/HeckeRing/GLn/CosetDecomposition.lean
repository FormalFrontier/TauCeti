/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# Upper-triangular representatives for a diagonal double coset

For an arbitrary tuple `a` of naturals, this file exhibits a family of elements of the double
coset `SL_n(ℤ) · diag(a) · SL_n(ℤ)`, indexed by the bounded entry assignments
`B_{ij} ∈ {0, …, a_j / a_i - 1}` for `i < j`. The construction, its membership in the double
coset, and its injectivity need no hypothesis on `a` at all.

*Distinctness of the cosets* does: when `a` is positive and a divisibility chain (`IsDvdChain`),
distinct entry assignments give representatives in distinct left `SL_n(ℤ)`-cosets. The chain
condition is what makes `a_j / a_i` an exact quotient, which is what turns integrality of the
connecting element into the divisibility the argument runs on.

Counting the index type then bounds the number of left cosets in the double coset below by
`∏_{i < j} (a_j / a_i)`. That count is a consequence of the distinctness proved here, not
itself a declaration in this file.

The representative attached to `B` is *defined* as `diag(a) · U(B)`, where `U(B)` is the
unipotent upper-triangular integral matrix with off-diagonal entries `B`. Two things follow
from that shape, and are the reason for choosing it over an entrywise definition: `U(B)` is
upper triangular with ones on the diagonal, so `det U(B) = 1` and `U(B) ∈ SL_n(ℤ)`; and hence
the representative lies in the double coset with no further argument.
`upperTriGL_apply_lt`, `upperTriGL_apply_diag` and `upperTriGL_apply_eq_zero_of_lt` recover the
entrywise description `M_{ij} = a_i · B_{ij}` for consumers that need it; injectivity itself
does not, since `upperTriGL` is visibly a composition of injective maps.

## Main definitions

* `UpperTriEntries` — the bounded entry assignments `B_{ij} ∈ Fin (a j / a i)` for `i < j`.
* `unitriMat`, `unitriSL` — the unipotent upper-triangular matrix `U(B)`, and its packaging as
  an element of `SL_n(ℤ)`.
* `upperTriGL` — the representative `diag(a) · U(B)` in `GL_n(ℚ)`.

## Main results

* `upperTriGL_mem_doubleCoset` — every representative lies in `SL_n(ℤ) · diag(a) · SL_n(ℤ)`.
* `unitriMat_injective`, `upperTriGL_injective` — distinct entry assignments give distinct
  matrices, hence distinct representatives.
* `eq_of_upperTriGL_eq_mapGL_mul_upperTriGL` and `eq_of_upperTriGL_mul_inv_mem_SLnZ` — the
  representatives lie in *distinct* left `SL_n(ℤ)`-cosets: two of them are left-equivalent
  only when their entry assignments already agree, for a positive `IsDvdChain`.

The two steps behind that conclusion are also stated separately, since each is reusable:
`dvd_comparison_of_upperTriGL_eq_mapGL_mul_upperTriGL` turns left equivalence into
`(a_j / a_i) ∣ C_{ij}` for the comparison matrix `C = U(B₁) · U(B₂)⁻¹`, by conjugating the
connecting element back through `diag(a)`; and `eq_of_dvd_comparison` turns that divisibility
into `C = 1`, because the entry bound `B_{ij} < a_j / a_i` leaves no room for a nonzero
multiple, by induction on `j - i`.

## References

The background for working with upper-triangular representatives at all is Shimura,
*Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Exercise 3.26(A),
p. 65: for every `α ∈ Δ` one can choose representatives `α_j` of `ΓαΓ = ⋃_j Γα_j` with
`L_ν α_j ⊆ L_ν` for the standard flag `L_ν = ∑_{i ≤ ν} ℤ e_i`, i.e. upper-triangular ones.
Shimura leaves it as an exercise and works the `n = 2` case explicitly in Prop. 3.33 (p. 70)
and Prop. 3.36 (p. 72).

That exercise is motivation, not the statement proved here. It asserts only that
flag-preserving representatives *exist*; it does not supply this bounded family
`B_{ij} ∈ Fin (a_j / a_i)`, nor the distinctness of the left cosets they occupy. Those are
proved below and are not read off from the exercise.

The definitions follow the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB)
file `LeanModularForms/HeckeRIngs/GLn/CosetDecomposition.lean` (Chris Birkbeck), whose module
docstring cites "Shimura, Proposition 3.22" — that number is in fact Lemma 3.22, an Euler
product identity, and is unrelated. The results here are new: the AINTLIB file states the
definitions and the determinant, and advertises the coset results in its docstring without
proving them.
-/

public section

open Matrix Matrix.SpecialLinearGroup DoubleCoset

namespace HeckeRing.GLn

variable (n : ℕ)

/-- Bounded entry assignments for upper-triangular representatives: an integer
`B_{ij} ∈ {0, …, a_j / a_i - 1}` for each pair `i < j`.

Stated for an arbitrary tuple `a`, with no chain or positivity hypothesis: those are needed by
the results, not to name the index type. The component `Fin (a j / a i)` is empty exactly when
`a j / a i = 0`, which for positive `a i` means `a j < a i`. -/
abbrev UpperTriEntries (a : Fin n → ℕ) : Type :=
  (p : {ij : Fin n × Fin n // ij.1 < ij.2}) → Fin (a p.val.2 / a p.val.1)

variable {n}

/-- The unipotent upper-triangular integral matrix `U(B)`: ones on the diagonal, `B_{ij}`
above it, zeros below. -/
def unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ if h : i < j then (B ⟨(i, j), h⟩ : ℕ) else if i = j then 1 else 0

@[simp] lemma unitriMat_apply_lt {a : Fin n → ℕ} (B : UpperTriEntries n a) {i j : Fin n}
    (h : i < j) : unitriMat B i j = (B ⟨(i, j), h⟩ : ℕ) := by
  simp [unitriMat, h]

@[simp] lemma unitriMat_apply_diag {a : Fin n → ℕ} (B : UpperTriEntries n a) (i : Fin n) :
    unitriMat B i i = 1 := by
  simp [unitriMat]

@[simp] lemma unitriMat_apply_eq_zero_of_lt {a : Fin n → ℕ} (B : UpperTriEntries n a)
    {i j : Fin n} (h : j < i) : unitriMat B i j = 0 := by
  simp [unitriMat, h.asymm, h.ne']

lemma isUpperTriangular_unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    Matrix.IsUpperTriangular (unitriMat B) :=
  fun _ _ h ↦ unitriMat_apply_eq_zero_of_lt B h

/-- `U(B)` is upper triangular with ones on the diagonal, so its determinant is `1`. -/
@[simp] lemma det_unitriMat {a : Fin n → ℕ} (B : UpperTriEntries n a) : (unitriMat B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_unitriMat B)]
  simp

/-- `U(B)` packaged as an element of `SL_n(ℤ)`. -/
def unitriSL {a : Fin n → ℕ} (B : UpperTriEntries n a) : SpecialLinearGroup (Fin n) ℤ :=
  ⟨unitriMat B, det_unitriMat B⟩

@[simp] lemma coe_unitriSL {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    (unitriSL B : Matrix (Fin n) (Fin n) ℤ) = unitriMat B := (rfl)

/-- The upper-triangular representative `diag(a) · U(B)` attached to a bounded entry
assignment. -/
noncomputable def upperTriGL {a : Fin n → ℕ} (B : UpperTriEntries n a) : GL (Fin n) ℚ :=
  natDiagGL n a * (mapGL ℚ (unitriSL B))

/-- The defining factorisation of the representative, as a characteristic lemma: consumers can
work from `diag(a) · U(B)` without unfolding `upperTriGL`. -/
lemma upperTriGL_def {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    upperTriGL B = natDiagGL n a * (mapGL ℚ (unitriSL B)) := (rfl)

/-- **The matrix of the representative**: `diag(a) · U(B)` entrywise over `ℚ`. `upperTriGL` is
built from `natDiagGL` and `mapGL`, so consumers that need the literal matrix — for instance to
recognise the classical `T_p` representatives `!![1, b; 0, p]` at `n = 2`, `a = ![1, p]` — would
otherwise unfold three definitions to get it. -/
@[simp] lemma upperTriGL_coe {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) (B : UpperTriEntries n a) :
    (↑(upperTriGL B) : Matrix (Fin n) (Fin n) ℚ) =
      Matrix.diagonal (fun i ↦ (a i : ℚ)) * (unitriMat B).map (Int.cast) := by
  rw [upperTriGL_def, Units.val_mul, natDiagGL_coe n a ha]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- Each upper-triangular representative lies in the double coset of `diag(a)`. -/
lemma upperTriGL_mem_doubleCoset {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    upperTriGL B ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) :=
  mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ (unitriSL B), coe_mem_SLnZ n _,
    by rw [upperTriGL, one_mul]⟩

/-- The entrywise description of the representative above the diagonal: `M_{ij} = a_i · B_{ij}`.
-/
@[simp] lemma upperTriGL_apply_lt {a : Fin n → ℕ} (ha : ∀ i, 0 < a i) (B : UpperTriEntries n a)
    {i j : Fin n} (h : i < j) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i j = (a i : ℚ) * (B ⟨(i, j), h⟩ : ℕ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul, unitriMat_apply_lt B h]

/-- The entrywise description on the diagonal: `M_{ii} = a_i`. -/
@[simp] lemma upperTriGL_apply_diag {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (B : UpperTriEntries n a) (i : Fin n) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i i = (a i : ℚ) := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul]

/-- The representative is upper triangular: entries below the diagonal vanish. -/
@[simp] lemma upperTriGL_apply_eq_zero_of_lt {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (B : UpperTriEntries n a) {i j : Fin n} (h : j < i) :
    (upperTriGL B : Matrix (Fin n) (Fin n) ℚ) i j = 0 := by
  rw [upperTriGL]
  simp [natDiagGL_coe n a ha, Matrix.diagonal_mul, unitriMat_apply_eq_zero_of_lt B h]

/-- Distinct entry assignments give distinct unipotent matrices. -/
lemma unitriMat_injective {a : Fin n → ℕ} : Function.Injective (unitriMat (a := a)) := by
  intro B₁ B₂ h
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hE := congrFun (congrFun h i) j
  rw [unitriMat_apply_lt B₁ hij, unitriMat_apply_lt B₂ hij] at hE
  exact Fin.ext (by exact_mod_cast hE)

/-- Distinct entry assignments give distinct representatives. No positivity hypothesis on `a`
is needed: this holds even at a tuple where `natDiagGL` takes its junk value `1`. -/
lemma upperTriGL_injective {a : Fin n → ℕ} : Function.Injective (upperTriGL (a := a)) := by
  intro B₁ B₂ h
  rw [upperTriGL, upperTriGL] at h
  have hSL := mapGL_injective (mul_left_cancel h)
  exact unitriMat_injective (by rw [← coe_unitriSL, ← coe_unitriSL, hSL])

/-! ## Distinctness of the left cosets

Two representatives lie in the same left `SL_n(ℤ)`-coset exactly when the conjugate
`diag(a)⁻¹ · S · diag(a)` of the connecting element `S` is integral, which says
`(a_j / a_i) ∣ C_{ij}` for the comparison matrix `C = U(B₁) · U(B₂)⁻¹`. The entry bound
`B_{ij} < a_j / a_i` then forces `C = 1`. -/

/-- A unipotent upper-triangular `C` with `C · U(B₂) = U(B₁)`, divisible above the diagonal by
the entry bounds, vanishes above the diagonal. -/
private lemma comparison_apply_eq_zero {a : Fin n → ℕ} {B₁ B₂ : UpperTriEntries n a}
    {C : Matrix (Fin n) (Fin n) ℤ} (hmul : C * unitriMat B₂ = unitriMat B₁)
    (hup : Matrix.IsUpperTriangular C) (hdiag : ∀ i, C i i = 1)
    (hdvd : ∀ ⦃i j : Fin n⦄, i < j → ((a j / a i : ℕ) : ℤ) ∣ C i j) :
    ∀ ⦃i j : Fin n⦄, i < j → C i j = 0 := by
  suffices H : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) - (i : ℕ) = d → i < j → C i j = 0 from
    fun i j hij ↦ H _ i j rfl hij
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    have hne : i ≠ j := hij.ne
    -- Only `k = i` and `k = j` contribute to `(C * U(B₂)) i j`.
    have hvanish : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin n)) →
        C i k * unitriMat B₂ k j = 0 := by
      intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rcases lt_trichotomy k i with hki | rfl | hik
      · rw [hup hki, zero_mul]
      · exact absurd rfl hk.1
      · rcases lt_trichotomy k j with hkj | rfl | hjk
        · rw [ih ((k : ℕ) - (i : ℕ)) (by omega) i k rfl hik, zero_mul]
        · exact absurd rfl hk.2
        · rw [unitriMat_apply_eq_zero_of_lt B₂ hjk, mul_zero]
    have hkey := congrFun (congrFun hmul i) j
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
      hvanish, Finset.sum_pair hne, hdiag i, one_mul, unitriMat_apply_diag, mul_one,
      unitriMat_apply_lt B₂ hij, unitriMat_apply_lt B₁ hij] at hkey
    -- `C i j` is a difference of two entries, each strictly below `a j / a i`.
    have hb₁ : (B₁ ⟨(i, j), hij⟩ : ℕ) < a j / a i := (B₁ ⟨(i, j), hij⟩).isLt
    have hb₂ : (B₂ ⟨(i, j), hij⟩ : ℕ) < a j / a i := (B₂ ⟨(i, j), hij⟩).isLt
    refine Int.eq_zero_of_abs_lt_dvd (hdvd hij) ?_
    have hCij : C i j = ((B₁ ⟨(i, j), hij⟩ : ℕ) : ℤ) - ((B₂ ⟨(i, j), hij⟩ : ℕ) : ℤ) := by
      linarith
    rw [hCij, abs_lt]
    omega

/-- The divisibility criterion for equality of entry assignments: if the comparison matrix
`C = U(B₁) · U(B₂)⁻¹` satisfies `(a_j / a_i) ∣ C_{ij}` above the diagonal, then `B₁ = B₂`.

This is arithmetic about a hypothesised divisibility; nothing here mentions cosets. What makes
that divisibility hold for two representatives in the same left `SL_n(ℤ)`-coset is
`dvd_comparison_of_upperTriGL_eq_mapGL_mul_upperTriGL`, and
`eq_of_upperTriGL_eq_mapGL_mul_upperTriGL` is the two combined. -/
lemma eq_of_dvd_comparison {a : Fin n → ℕ} {B₁ B₂ : UpperTriEntries n a}
    (hdvd : ∀ ⦃i j : Fin n⦄, i < j →
      ((a j / a i : ℕ) : ℤ) ∣ (unitriMat B₁ * (unitriMat B₂)⁻¹) i j) :
    B₁ = B₂ := by
  have : Invertible (unitriMat B₂) :=
    Matrix.invertibleOfIsUnitDet _ (by rw [det_unitriMat]; exact isUnit_one)
  set C : Matrix (Fin n) (Fin n) ℤ := unitriMat B₁ * (unitriMat B₂)⁻¹ with hC
  have hunit : C.IsUpperUnitriangular := hC ▸
    ((Matrix.isUpperUnitriangular_def (unitriMat B₁)).2
      ⟨isUpperTriangular_unitriMat B₁, unitriMat_apply_diag B₁⟩).mul
      ((Matrix.isUpperUnitriangular_def (unitriMat B₂)).2
        ⟨isUpperTriangular_unitriMat B₂, unitriMat_apply_diag B₂⟩).inv
  have hup : Matrix.IsUpperTriangular C := hunit.isUpperTriangular
  have hdiag : ∀ i, C i i = 1 := hunit.apply_diag
  have hmul : C * unitriMat B₂ = unitriMat B₁ := by
    rw [hC, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_invertible _),
      Matrix.mul_one]
  have hzero := comparison_apply_eq_zero hmul hup hdiag hdvd
  have hC1 : C = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hzero h, Matrix.one_apply_ne h.ne]
    · rw [hdiag, Matrix.one_apply_eq]
    · rw [hup h, Matrix.one_apply_ne h.ne']
  exact unitriMat_injective (by rw [← hmul, hC1, Matrix.one_mul])

/-- The inverse of `U(B)` in `SL_n(ℤ)` is its matrix inverse.

Deliberately not `@[simp]`: `simp` already rewrites the left-hand side past this, to
`(unitriMat B).adjugate`, through `SpecialLinearGroup.coe_inv` and `coe_unitriSL`, so the
marking is rejected by `simpNF` as not being in normal form. The lemma is kept as the named
bridge to the `Matrix.inv` spelling, for `rw` and for `simp only` sets that want it. -/
private lemma coe_inv_unitriSL {a : Fin n → ℕ} (B : UpperTriEntries n a) :
    (((unitriSL B)⁻¹ : SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)
      = (unitriMat B)⁻¹ := by
  rw [SpecialLinearGroup.coe_inv, Matrix.inv_def, coe_unitriSL, det_unitriMat, Ring.inverse_one,
    one_smul]

/-- Two representatives in the same left `SL_n(ℤ)`-coset have comparison matrix divisible above
the diagonal: `(a_j / a_i) ∣ C_{ij}` for `C = U(B₁) · U(B₂)⁻¹`. This is the divisibility that
`eq_of_dvd_comparison` takes as a hypothesis, so the two together make distinctness a theorem
about the coset relation rather than a criterion. Only `a i ∣ a j` is needed, at the pair asked
about. -/
lemma dvd_comparison_of_upperTriGL_eq_mapGL_mul_upperTriGL {a : Fin n → ℕ}
    (ha : ∀ i, 0 < a i) {B₁ B₂ : UpperTriEntries n a} {S : SpecialLinearGroup (Fin n) ℤ}
    (hS : upperTriGL B₁ = mapGL ℚ S * upperTriGL B₂) {i j : Fin n} (hdvd : a i ∣ a j) :
    ((a j / a i : ℕ) : ℤ) ∣ (unitriMat B₁ * (unitriMat B₂)⁻¹) i j := by
  -- Cancel `U(B₂)` on the right, in the group `GL_n(ℚ)`.
  have hGL : natDiagGL n a * mapGL ℚ (unitriSL B₁ * (unitriSL B₂)⁻¹)
      = mapGL ℚ S * natDiagGL n a := by
    rw [upperTriGL, upperTriGL] at hS
    rw [map_mul, map_inv, ← mul_assoc, hS]
    group
  -- Read the `(i, j)` entry of both sides, then descend from `ℚ` to `ℤ`.
  have hmat : (natDiagGL n a : Matrix (Fin n) (Fin n) ℚ) *
        (mapGL ℚ (unitriSL B₁ * (unitriSL B₂)⁻¹) : Matrix (Fin n) (Fin n) ℚ)
      = (mapGL ℚ S : Matrix (Fin n) (Fin n) ℚ) *
        (natDiagGL n a : Matrix (Fin n) (Fin n) ℚ) := by
    rw [← Units.val_mul, ← Units.val_mul, hGL]
  have hentry := congrFun (congrFun hmat i) j
  rw [natDiagGL_coe n a ha, mapGL_coe_matrix, mapGL_coe_matrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal] at hentry
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    eq_intCast, Matrix.map_apply, SpecialLinearGroup.coe_mul, coe_unitriSL,
    coe_inv_unitriSL] at hentry
  have hZ : (a i : ℤ) * (unitriMat B₁ * (unitriMat B₂)⁻¹) i j
      = (S : Matrix (Fin n) (Fin n) ℤ) i j * (a j : ℤ) := by exact_mod_cast hentry
  -- `a j = a i * (a j / a i)` exactly, so `a i` cancels.
  rw [← Nat.mul_div_cancel' hdvd, Nat.cast_mul, ← mul_assoc,
    mul_comm ((S : Matrix _ _ ℤ) i j), mul_assoc] at hZ
  exact Dvd.intro_left _ (mul_left_cancel₀ (by exact_mod_cast (ha i).ne') hZ).symm

/-- The upper-triangular representatives of a positive divisibility chain lie in pairwise
**distinct** left `SL_n(ℤ)`-cosets: if two of them differ by a left factor in `SL_n(ℤ)`, their
entry assignments already agree. Equivalently, `B ↦ SL_n(ℤ) · upperTriGL B` is injective. -/
theorem eq_of_upperTriGL_eq_mapGL_mul_upperTriGL {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (hchain : IsDvdChain a)
    {B₁ B₂ : UpperTriEntries n a}
    {S : SpecialLinearGroup (Fin n) ℤ} (hS : upperTriGL B₁ = mapGL ℚ S * upperTriGL B₂) :
    B₁ = B₂ :=
  eq_of_dvd_comparison fun _ _ hij ↦
    dvd_comparison_of_upperTriGL_eq_mapGL_mul_upperTriGL ha hS (isDvdChain_iff.mp hchain hij.le)

/-- The same statement phrased with the subgroup `SLnZ n` of `GL_n(ℚ)`: distinct entry
assignments give representatives in distinct left cosets of `SL_n(ℤ)`. -/
theorem eq_of_upperTriGL_mul_inv_mem_SLnZ {a : Fin n → ℕ} (ha : ∀ i, 0 < a i)
    (hchain : IsDvdChain a) {B₁ B₂ : UpperTriEntries n a}
    (h : upperTriGL B₁ * (upperTriGL B₂)⁻¹ ∈ SLnZ n) : B₁ = B₂ := by
  obtain ⟨S, hSeq⟩ := (mem_SLnZ_iff n).mp h
  exact eq_of_upperTriGL_eq_mapGL_mul_upperTriGL ha hchain (by rw [hSeq]; group)

end HeckeRing.GLn
