/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Matrix.scalar` occurs in the statements below, and the `2 × 2` entry lemmas
-- (`Matrix.det_fin_two`, `Fin.sum_univ_two`) in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Notation
-- `Subgroup.centralizer` occurs in the statements below.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `ConjClasses.carrier` occurs in the statements below, and `TauCeti.ConjClasses.ncard_carrier_mk`
-- is what turns a centralizer order into a class size.
public import TauCeti.Algebra.Group.Conj
-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal
-- `TauCeti.GL2NonSplitTorus` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- Non-public: the order of `GL (Fin 2) F` and the number of units of a finite field are used only
-- inside the counting proofs, so downstream importers do not pay for them.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Centralizers of the regular semisimple elements of `GL₂`

A `2 × 2` matrix over a field is **regular** as soon as it is not scalar: it is then cyclic
(nonderogatory), and the matrices commuting with it are exactly the polynomials in it. In size `2`
those polynomials are the affine combinations `a • 1 + b • M`, and that is the content of
`TauCeti.commute_finTwo_iff`, the engine of this file: the commutant of a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` is the two-dimensional algebra `F[M]`.

Two consequences organize the conjugacy classes of `GL₂(F)`. First, the commutant of a non-scalar
matrix is commutative, so the centralizer of a non-central element of `GL₂(F)` is an **abelian**
subgroup (`TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar`). Second, for a **regular
semisimple** element — one with two distinct eigenvalues, over `F` or over a quadratic extension
`E/F` — that centralizer is exactly the **maximal torus** containing it:

* the *split* case, an invertible diagonal matrix with distinct diagonal entries: its centralizer
  is the split torus `TauCeti.diagGL` of all invertible diagonal matrices
  (`TauCeti.centralizer_diagGL`), of order `(q - 1)²`, so its conjugacy class has `q (q + 1)`
  elements;
* the *elliptic* case, an element of the non-split torus `TauCeti.GL2NonSplitTorus` not coming from
  `F`: its centralizer is that whole torus
  (`TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`), of order `q² - 1`, so its
  conjugacy class has `q (q - 1)` elements.

The remaining conjugacy classes of `GL₂(𝔽_q)` are the central ones, whose centralizer is
everything, and the non-semisimple ones `!![a, 1; 0, a]`, whose centralizer is again `F[M]ˣ` but
for a matrix with a repeated eigenvalue; the latter is not proved here.

The class sizes are read off the centralizer orders by orbit-stabilizer
(`TauCeti.ConjClasses.ncard_carrier_mk`), together with `Matrix.card_GL_field`, which gives
`|GL₂(𝔽_q)| = (q² - 1)(q² - q)`.

## Main results

* `TauCeti.commute_finTwo_iff`: a matrix commutes with a non-scalar `2 × 2` matrix `M` exactly when
  it is of the form `a • 1 + b • M`.
* `TauCeti.commute_of_commute_finTwo`: two matrices commuting with a common non-scalar `2 × 2`
  matrix commute with each other.
* `TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar`: the centralizer of a non-central
  element of `GL (Fin 2) F` is abelian.
* `TauCeti.centralizer_diagGL`, `TauCeti.natCard_centralizer_diagGL`,
  `TauCeti.ncard_carrier_conjClasses_diagGL`: the centralizer of an invertible diagonal matrix with
  distinct entries is the split torus, of order `(q - 1)²`, and its conjugacy class has `q (q + 1)`
  elements.
* `TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`,
  `TauCeti.GL2NonSplitTorus.natCard_centralizer_gl2NonSplitTorusHom`,
  `TauCeti.GL2NonSplitTorus.ncard_carrier_conjClasses_gl2NonSplitTorusHom`: the centralizer of an
  elliptic element is the non-split torus, of order `q² - 1`, and its conjugacy class has
  `q (q - 1)` elements.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)".
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 5.2.
-/

public section

open Matrix

namespace TauCeti

section Commutant

variable {F : Type*} [Field F] {M N P : Matrix (Fin 2) (Fin 2) F}

/-- A `2 × 2` matrix is scalar exactly when its off-diagonal entries vanish and its two diagonal
entries agree. -/
theorem mem_range_scalar_finTwo_iff :
    M ∈ Set.range (Matrix.scalar (Fin 2)) ↔ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [Matrix.scalar_apply]
  · rintro ⟨h01, h10, h00⟩
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00]

/-- The entries of `a • 1 + b • M`, for a `2 × 2` matrix `M`. -/
private theorem scalar_add_smul_apply (a b : F) (i j : Fin 2) :
    (Matrix.scalar (Fin 2) a + b • M) i j = (if i = j then a else 0) + b * M i j := by
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

/-- A `2 × 2` matrix is `a • 1 + b • M` as soon as its four entries are. -/
private theorem eq_scalar_add_smul_finTwo {a b : F} (h00 : N 0 0 = a + b * M 0 0)
    (h01 : N 0 1 = b * M 0 1) (h10 : N 1 0 = b * M 1 0) (h11 : N 1 1 = a + b * M 1 1) :
    N = Matrix.scalar (Fin 2) a + b • M := by
  ext i j
  rw [scalar_add_smul_apply]
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

/-- **The commutant of a non-scalar `2 × 2` matrix.** A matrix commutes with a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` exactly when it lies in the two-dimensional subalgebra spanned by
`1` and `M`; equivalently, a non-scalar `2 × 2` matrix is cyclic, so its commutant is `F[M]`.

The hypothesis is necessary: everything commutes with a scalar matrix. -/
theorem commute_finTwo_iff (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    Commute M N ↔ ∃ a b : F, N = Matrix.scalar (Fin 2) a + b • M := by
  constructor
  · intro h
    -- The entry equations of `M * N = N * M`; only three of the four are used.
    have key : ∀ i j : Fin 2,
        M i 0 * N 0 j + M i 1 * N 1 j = N i 0 * M 0 j + N i 1 * M 1 j := fun i j => by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h.eq i) j
    have e00 := key 0 0
    have e01 := key 0 1
    have e10 := key 1 0
    -- Being non-scalar, `M` has a nonzero off-diagonal entry or distinct diagonal entries.
    rw [mem_range_scalar_finTwo_iff] at hM
    push Not at hM
    by_cases h01 : M 0 1 = 0
    · by_cases h10 : M 1 0 = 0
      · -- `M` is diagonal with distinct entries: everything commuting with it is diagonal.
        have hdiag : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.mpr (hM h01 h10)
        obtain ⟨b, hb⟩ : ∃ b : F, b * (M 0 0 - M 1 1) = N 0 0 - N 1 1 :=
          ⟨(N 0 0 - N 1 1) / (M 0 0 - M 1 1), div_mul_cancel₀ _ hdiag⟩
        have hN01 : N 0 1 = 0 :=
          mul_right_cancel₀ hdiag (by linear_combination e01 + (N 0 0 - N 1 1) * h01)
        have hN10 : N 1 0 = 0 :=
          mul_right_cancel₀ hdiag (by linear_combination -e10 + (N 0 0 - N 1 1) * h10)
        exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_finTwo (by ring)
          (by rw [hN01, h01, mul_zero]) (by rw [hN10, h10, mul_zero])
          (by linear_combination hb)⟩
      · -- The lower-left entry is nonzero and determines the coefficient of `M`.
        obtain ⟨b, hb⟩ : ∃ b : F, b * M 1 0 = N 1 0 := ⟨N 1 0 / M 1 0, div_mul_cancel₀ _ h10⟩
        exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_finTwo (by ring)
          (mul_left_cancel₀ h10 (by linear_combination -e00 - M 0 1 * hb)) hb.symm
          (mul_left_cancel₀ h10 (by linear_combination -e10 + (M 0 0 - M 1 1) * hb))⟩
    · -- The upper-right entry is nonzero and determines the coefficient of `M`.
      obtain ⟨b, hb⟩ : ∃ b : F, b * M 0 1 = N 0 1 := ⟨N 0 1 / M 0 1, div_mul_cancel₀ _ h01⟩
      exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_finTwo (by ring) hb.symm
        (mul_left_cancel₀ h01 (by linear_combination e00 - M 1 0 * hb))
        (mul_left_cancel₀ h01 (by linear_combination e01 + (M 0 0 - M 1 1) * hb))⟩
  · rintro ⟨a, b, rfl⟩
    exact ((Matrix.scalar_commute a (Commute.all a) M).symm).add_right
      ((Commute.refl M).smul_right b)

/-- Two matrices commuting with a common non-scalar `2 × 2` matrix commute with each other: both
lie in the commutative algebra `F[M]`. -/
theorem commute_of_commute_finTwo (hM : M ∉ Set.range (Matrix.scalar (Fin 2)))
    (hN : Commute M N) (hP : Commute M P) : Commute N P := by
  obtain ⟨a, b, rfl⟩ := (commute_finTwo_iff hM).mp hN
  obtain ⟨c, d, rfl⟩ := (commute_finTwo_iff hM).mp hP
  have hs : ∀ x : F, Commute (Matrix.scalar (Fin 2) x) M :=
    fun x => Matrix.scalar_commute x (Commute.all x) M
  have h1 : Commute (Matrix.scalar (Fin 2) a) (Matrix.scalar (Fin 2) c) :=
    Matrix.scalar_commute a (Commute.all a) _
  have h2 : Commute (Matrix.scalar (Fin 2) a) (d • M) := (hs a).smul_right d
  have h3 : Commute (b • M) (Matrix.scalar (Fin 2) c) := (hs c).symm.smul_left b
  have h4 : Commute (b • M) (d • M) := ((Commute.refl M).smul_right d).smul_left b
  exact (h1.add_right h2).add_left (h3.add_right h4)

end Commutant

section GeneralLinearGroup

variable {F : Type*} [Field F] {g h : GL (Fin 2) F}

/-- Membership in the centralizer of `g`, read on the underlying matrices. -/
theorem mem_centralizer_singleton_iff_commute_coe :
    h ∈ Subgroup.centralizer {g} ↔
      Commute (g : Matrix (Fin 2) (Fin 2) F) (h : Matrix (Fin 2) (Fin 2) F) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

/-- A non-central element of `GL (Fin 2) F` is one whose matrix is not scalar; the matrices
commuting with it then form a commutative algebra, so its centralizer is an **abelian** subgroup.
This is what makes the centralizers of the regular elements of `GL₂` tori. -/
theorem isMulCommutative_centralizer_of_notMem_range_scalar
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) :
    IsMulCommutative ↥(Subgroup.centralizer {g}) :=
  ⟨⟨fun x y => Subtype.ext (Commute.units_val_iff.mp (commute_of_commute_finTwo hg
    (mem_centralizer_singleton_iff_commute_coe.mp x.2)
    (mem_centralizer_singleton_iff_commute_coe.mp y.2))).eq⟩⟩

end GeneralLinearGroup

section SplitTorus

variable {F : Type*} [Field F] {t : Fin 2 → Fˣ}

/-- An invertible diagonal matrix with distinct diagonal entries is not scalar. -/
theorem notMem_range_scalar_diagGL (ht : t 0 ≠ t 1) :
    (diagGL t : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [mem_range_scalar_finTwo_iff]
  rintro ⟨-, -, h⟩
  exact ht (Units.ext (by simpa using h))

/-- **The centralizer of a split regular semisimple element of `GL₂`.** An invertible diagonal
matrix with *distinct* diagonal entries has, as its centralizer, exactly the split torus of all
invertible diagonal matrices: the maximal torus containing it. -/
theorem centralizer_diagGL (ht : t 0 ≠ t 1) :
    Subgroup.centralizer {diagGL t} = (diagGL (k := F) (n := 2)).range := by
  ext h
  rw [mem_centralizer_singleton_iff_commute_coe, MonoidHom.mem_range]
  constructor
  · intro hcomm
    obtain ⟨a, b, hab⟩ := (commute_finTwo_iff (notMem_range_scalar_diagGL ht)).mp hcomm
    have hentry : ∀ i j : Fin 2, (h : Matrix (Fin 2) (Fin 2) F) i j =
        (if i = j then a else 0) + b * (diagGL t : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
      rw [hab, scalar_add_smul_apply]
    -- The commuting matrix is diagonal, and it is invertible, so its entries are units.
    have h01 : (h : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simp [hentry 0 1]
    have h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [hentry 1 0]
    have hdet : (h : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      have hu := (Matrix.GeneralLinearGroup.det h).isUnit.ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10] at hu
      simpa using hu
    refine ⟨fun i => Units.mk0 ((h : Matrix (Fin 2) (Fin 2) F) i i) ?_, ?_⟩
    · fin_cases i
      · exact left_ne_zero_of_mul hdet
      · exact right_ne_zero_of_mul hdet
    · refine Units.ext ?_
      ext i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hentry i j, hij]
  · rintro ⟨s, rfl⟩
    exact Commute.units_val_iff.mpr ((Commute.all t s).map diagGL)

variable [Fintype F]

/-- **The order of the centralizer of a split regular semisimple element**: over a field with `q`
elements the split torus has `(q - 1)²` elements, one invertible scalar per diagonal entry. -/
theorem natCard_centralizer_diagGL (ht : t 0 ≠ t 1) :
    Nat.card (Subgroup.centralizer {diagGL t}) = (Fintype.card F - 1) ^ 2 := by
  classical
  rw [centralizer_diagGL ht, ← Nat.card_congr (MonoidHom.ofInjective
    (diagGL_injective (k := F) (n := 2))).toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card]

end SplitTorus

section Counting

variable {F : Type*} [Field F] [Fintype F]

/-- The order of `GL₂` over a field with `q` elements, in the factored form
`(q - 1)² · q · (q + 1)` that divides out against the centralizer orders. -/
private theorem natCard_gl2 :
    Nat.card (GL (Fin 2) F) =
      (Fintype.card F - 1) ^ 2 * (Fintype.card F * (Fintype.card F + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 :=
    ⟨Fintype.card F - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have h1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have h2 : (m + 1) ^ 2 - (m + 1) = m * (m + 1) := by
    have : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
    omega
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hm]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.add_sub_cancel, h1, h2]
  ring

/-- The factor the split class-size computation cancels by is positive: `(q - 1)² > 0` for a field
with `q > 1` elements. -/
private theorem sub_one_sq_pos : 0 < (Fintype.card F - 1) ^ 2 :=
  pow_pos (Nat.sub_pos_of_lt Fintype.one_lt_card) 2

/-- **The size of a split regular semisimple conjugacy class of `GL₂(𝔽_q)`**: it is
`q (q + 1) = [GL₂(𝔽_q) : T]` for the split torus `T`. -/
theorem ncard_carrier_conjClasses_diagGL {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    (ConjClasses.mk (diagGL t)).carrier.ncard = Fintype.card F * (Fintype.card F + 1) := by
  have key := Subgroup.index_mul_card (Subgroup.centralizer {diagGL t})
  rw [natCard_centralizer_diagGL ht, natCard_gl2] at key
  rw [ConjClasses.ncard_carrier_mk]
  refine Nat.eq_of_mul_eq_mul_right (sub_one_sq_pos (F := F)) ?_
  rw [key]
  ring

end Counting

namespace GL2NonSplitTorus

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  (hE : Module.finrank F E = 2) {x : Eˣ}

/-- A scalar matrix over `F` is the image of the algebra map of the matrix algebra, so that the
commutant description of `TauCeti.commute_finTwo_iff` can be compared with `Algebra.leftMulMatrix`
through `AlgHom.commutes`. -/
private theorem scalar_eq_algebraMap (c : F) :
    Matrix.scalar (Fin 2) c = algebraMap F (Matrix (Fin 2) (Fin 2) F) c := (rfl)

/-- An element of the non-split torus not coming from `F` is not a scalar matrix: multiplication by
`x` on `E` is multiplication by an element of `F` exactly when `x` lies in `F`. -/
theorem notMem_range_scalar_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) ∉
      Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨c, hc⟩
  refine hx ⟨c, Algebra.leftMulMatrix_injective (nonSplitTorusBasis F E hE) ?_⟩
  rw [(Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes c,
    ← coe_gl2NonSplitTorusHom hE, ← hc, scalar_eq_algebraMap]

/-- **The centralizer of an elliptic element of `GL₂`.** An element of the non-split torus not
coming from `F` has that whole torus as its centralizer: the maximal torus containing it. Together
with `TauCeti.centralizer_diagGL` this says that the centralizer of a regular semisimple element of
`GL₂` is the maximal torus containing it, split or not. -/
theorem centralizer_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Subgroup.centralizer {GL2NonSplitTorusHom F E hE x} = GL2NonSplitTorus F E hE := by
  ext h
  rw [mem_centralizer_singleton_iff_commute_coe, mem_iff]
  constructor
  · intro hcomm
    obtain ⟨a, b, hab⟩ :=
      (commute_finTwo_iff (notMem_range_scalar_gl2NonSplitTorusHom hE hx)).mp hcomm
    -- The commuting matrix is multiplication by `a + b x`, which is nonzero as it is invertible.
    have hmat : (h : Matrix (Fin 2) (Fin 2) F) = Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)
        (algebraMap F E a + b • (x : E)) := by
      rw [map_add, map_smul, (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes a,
        ← coe_gl2NonSplitTorusHom hE, ← scalar_eq_algebraMap]
      exact hab
    have hy0 : algebraMap F E a + b • (x : E) ≠ 0 := by
      intro h0
      refine (Matrix.GeneralLinearGroup.det h).isUnit.ne_zero ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, hmat, h0, map_zero]
      exact Matrix.det_zero
    exact ⟨Units.mk0 _ hy0, Units.ext (by rw [coe_gl2NonSplitTorusHom, Units.val_mk0, hmat])⟩
  · rintro ⟨z, rfl⟩
    exact Commute.units_val_iff.mpr ((Commute.all x z).map (GL2NonSplitTorusHom F E hE))

variable [Fintype F]

/-- **The order of the centralizer of an elliptic element**: over a field with `q` elements the
non-split torus is a copy of `E ∖ {0}`, so it has `q² - 1` elements. -/
theorem natCard_centralizer_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Nat.card (Subgroup.centralizer {GL2NonSplitTorusHom F E hE x}) = Fintype.card F ^ 2 - 1 := by
  rw [centralizer_gl2NonSplitTorusHom hE hx, natCard_eq, Nat.card_eq_fintype_card]

/-- **The size of an elliptic conjugacy class of `GL₂(𝔽_q)`**: it is `q (q - 1) = [GL₂(𝔽_q) : T]`
for the non-split torus `T`. -/
theorem ncard_carrier_conjClasses_gl2NonSplitTorusHom
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (ConjClasses.mk (GL2NonSplitTorusHom F E hE x)).carrier.ncard =
      Fintype.card F * (Fintype.card F - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 :=
    ⟨Fintype.card F - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have hm1 : 1 ≤ m := by
    have := Fintype.one_lt_card (α := F)
    omega
  have h1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have hpos : 0 < Fintype.card F ^ 2 - 1 := by
    rw [hm, h1]
    exact Nat.mul_pos (by omega) (by omega)
  have key := Subgroup.index_mul_card (Subgroup.centralizer {GL2NonSplitTorusHom F E hE x})
  rw [natCard_centralizer_gl2NonSplitTorusHom hE hx, natCard_gl2] at key
  rw [ConjClasses.ncard_carrier_mk]
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [key, hm]
  simp only [Nat.add_sub_cancel, h1]
  ring

end GL2NonSplitTorus

end TauCeti
