/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.RepresentationTheory.SU2.Basic

/-!
# Every element of `SU(2)` is conjugate into the maximal torus

The maximal torus `T` of `SU(2)` built in `TauCeti/RepresentationTheory/SU2/Basic.lean` meets
every conjugacy class: for every `g : SU(2)` there is `u : SU(2)` with `u g u⁻¹ ∈ T`. This is the
torus-conjugacy input the compact-group roadmap asks for before the classification of the
irreducible representations of `SU(2)`, and it is what makes a class function on `SU(2)` the same
thing as a Weyl-invariant function on the circle.

The proof is unitary diagonalisation, arranged so that it only needs Mathlib's spectral theorem
for *Hermitian* matrices. Mathlib has no spectral theorem for normal or unitary matrices, but in
`SU(2)` one is not needed: writing `G` for the matrix of `g`, the determinant condition forces the
Hermitian part of `G` to be a scalar,

`G + G* = (tr G) • 1`   (`TauCeti.SU2.coe_add_star`),

because `G* = G⁻¹` is the adjugate of `G` and a `2 × 2` matrix and its adjugate add up to the
trace. So `G` differs from the Hermitian matrix `H = i (G - G*)` by a scalar matrix, and any
unitary that diagonalises `H` diagonalises `G`. The eigenvector unitary supplied by the spectral
theorem need not have determinant one, but it can be rescaled by a scalar of modulus one until it
does (`TauCeti.SU2.exists_circle_smul_mem_specialUnitaryGroup`), and rescaling by a scalar does not
change the conjugation it induces.

## Main results

* `TauCeti.SU2.star_coe_eq_adjugate`: the conjugate transpose of an element of `SU(2)` is its
  adjugate.
* `TauCeti.SU2.coe_add_star`: an element of `SU(2)` and its conjugate transpose add up to
  `(tr g) • 1`; equivalently the Hermitian part of `g` is a scalar matrix.
* `TauCeti.SU2.exists_circle_smul_mem_specialUnitaryGroup`: `U(2) = Circle · SU(2)`; every
  `2 × 2` unitary matrix becomes special unitary after multiplication by a scalar of modulus one.
* `TauCeti.SU2.exists_conj_mem_torus`: **torus conjugacy**, every element of `SU(2)` is conjugate
  into the maximal torus.
* `TauCeti.SU2.exists_isConj_torusExp`: the angle form, every element of `SU(2)` is conjugate to
  `diag (e^{iθ}, e^{-iθ})`.
* `TauCeti.SU2.isConj_inv_of_mem_torus` and `TauCeti.SU2.isConj_torusExp_neg`: the Weyl reflection,
  every element of the torus is conjugate in `SU(2)` to its inverse. With torus conjugacy this
  says the conjugacy classes of `SU(2)` are the Weyl orbits on `T`.
* `TauCeti.SU2.eq_of_eqOn_torus`: two conjugation-invariant functions on `SU(2)` that agree on the
  maximal torus are equal; a class function on `SU(2)` is determined by its restriction to `T`.
-/

public section

namespace TauCeti

namespace SU2

/-! ### The Hermitian part of a special unitary `2 × 2` matrix -/

/-- The conjugate transpose of an element of `SU(2)` is its adjugate: it is the inverse, and for
determinant one the inverse is the adjugate. This is the explicit description of `star` that both
the Hermitian-part identity below and the Weyl reflection run on. -/
theorem star_coe_eq_adjugate (g : SU2) :
    star (g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem.1
  calc star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (g : Matrix (Fin 2) (Fin 2) ℂ) *
          star (g : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [Matrix.adjugate_mul, hmem.2, one_smul, Matrix.one_mul]
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
        rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

/-- An element of `SU(2)` and its conjugate transpose add up to `(tr g) • 1`: the conjugate
transpose of `g` is its adjugate, and a `2 × 2` matrix plus its adjugate is the trace times the
identity. Equivalently, the Hermitian part of `g` is a scalar matrix -- the fact that lets
Hermitian diagonalisation diagonalise `g` itself. -/
theorem coe_add_star (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) + star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) • 1 := by
  rw [star_coe_eq_adjugate, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

/-! ### Rescaling a unitary matrix into `SU(2)` -/

/-- `U(2) = Circle · SU(2)`: every `2 × 2` unitary matrix becomes special unitary after
multiplication by a suitable scalar of modulus one. The scalar is a square root of the inverse of
the determinant, which has modulus one; a square root exists because the circle is divisible. -/
theorem exists_circle_smul_mem_specialUnitaryGroup (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ c : Circle, ((c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ)) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hUU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hnorm : ‖(U : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 := by
    have h : star ((U : Matrix (Fin 2) (Fin 2) ℂ).det) * (U : Matrix (Fin 2) (Fin 2) ℂ).det
        = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU,
        Matrix.det_one]
    have h2 := congrArg norm h
    rw [norm_mul, norm_star, norm_one] at h2
    nlinarith [norm_nonneg ((U : Matrix (Fin 2) (Fin 2) ℂ).det)]
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective
    (⟨(U : Matrix (Fin 2) (Fin 2) ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
  have hdetU : (U : Matrix (Fin 2) (Fin 2) ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
    have := congrArg (fun z : Circle => (z : ℂ)) hθ
    rw [Circle.coe_exp] at this
    exact this.symm
  have hcc : ∀ z : Circle, star (z : ℂ) * (z : ℂ) = 1 := fun z => by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
  refine ⟨Circle.exp (-(θ / 2)), Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hUU,
      hcc, one_smul]
  · rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_exp, hdetU, sq, mul_assoc, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring

/-! ### Torus conjugacy -/

/-- **Torus conjugacy for `SU(2)`**: every element of `SU(2)` is conjugate into the maximal torus.
Equivalently, every special unitary `2 × 2` matrix is diagonalised by a special unitary matrix. -/
theorem exists_conj_mem_torus (g : SU2) : ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  set H : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (G - star G) with hHdef
  -- `H` is Hermitian: conjugating negates both `Complex.I` and `G - star G`.
  have hHerm : H.IsHermitian := by
    change H.conjTranspose = H
    rw [← Matrix.star_eq_conjTranspose, hHdef, star_smul, star_sub, star_star, Complex.star_def,
      Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  -- `G` is a scalar matrix plus a multiple of `H`, so anything diagonalising `H` diagonalises `G`.
  have hdecomp : G = (Matrix.trace G / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (-Complex.I / 2) • H := by
    have hscalar : (Matrix.trace G / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = (2⁻¹ : ℂ) • (G + star G) := by
      rw [coe_add_star g, smul_smul]
      congr 1
      ring
    have hI : (-Complex.I / 2) * Complex.I = 2⁻¹ := by
      rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
      norm_num
    rw [hHdef, smul_smul, hI, hscalar]
    module
  -- Mathlib's spectral theorem diagonalises `H` by a unitary matrix.
  obtain ⟨U, hdiagH⟩ : ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      (star (U : Matrix (Fin 2) (Fin 2) ℂ) * H * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag := by
    refine ⟨hHerm.eigenvectorUnitary, ?_⟩
    have h := hHerm.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℂ)
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [h]
    exact Matrix.isDiag_diagonal _
  have hUU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  -- Conjugating by any unitary that diagonalises `H` diagonalises `G`.
  have hdiagG :
      (star (U : Matrix (Fin 2) (Fin 2) ℂ) * G * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag := by
    have hexpand : star (U : Matrix (Fin 2) (Fin 2) ℂ) * G * (U : Matrix (Fin 2) (Fin 2) ℂ)
        = (Matrix.trace G / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + (-Complex.I / 2) •
            (star (U : Matrix (Fin 2) (Fin 2) ℂ) * H * (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
      conv_lhs => rw [hdecomp]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [hUU]
    rw [hexpand]
    exact (Matrix.isDiag_one.smul _).add (hdiagH.smul _)
  -- Rescale `U` into `SU(2)`; the rescaling does not change the conjugation.
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup U
  refine ⟨(⟨(c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ), hc⟩ : SU2)⁻¹, ?_⟩
  rw [mem_torus_iff]
  have hcoe : (((⟨(c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ), hc⟩ : SU2)⁻¹ * g *
        ((⟨(c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ), hc⟩ : SU2)⁻¹)⁻¹ :
          SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = star ((c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ)) * G *
          ((c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [inv_inv]
    rfl
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [hcoe]
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcmul, one_smul]
  exact hdiagG

/-- Every element of `SU(2)` is conjugate to the torus element `diag (e^{iθ}, e^{-iθ})` for some
angle `θ`. -/
theorem exists_isConj_torusExp (g : SU2) : ∃ θ : ℝ, IsConj g (torusExp θ) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  obtain ⟨θ, hθ⟩ := mem_torus_iff_exists_torusExp.mp hu
  exact ⟨θ, isConj_iff.mpr ⟨u, hθ⟩⟩

/-! ### The Weyl reflection -/

/-- The Weyl group of `SU(2)` acts on the maximal torus by inversion: every element of the torus
is conjugate in `SU(2)` to its inverse, by the matrix `!![0, 1; -1, 0]` that swaps the two
coordinate axes. Together with `TauCeti.SU2.exists_conj_mem_torus` this says that the conjugacy
classes of `SU(2)` are the orbits of the Weyl group on the torus. -/
theorem isConj_inv_of_mem_torus {g : SU2} (hg : g ∈ torus) : IsConj g g⁻¹ := by
  have hdiag := mem_torus_iff.mp hg
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := hdiag (by decide)
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := hdiag (by decide)
  have hmem : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
    · simp [Matrix.det_fin_two]
  refine isConj_iff.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = star (g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [star_coe_eq_adjugate, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, h01, h10]

/-- Every element of the maximal torus is conjugate to its inverse in the angle parametrisation:
`diag (e^{iθ}, e^{-iθ})` and `diag (e^{-iθ}, e^{iθ})` are conjugate in `SU(2)`. -/
theorem isConj_torusExp_neg (θ : ℝ) : IsConj (torusExp θ) (torusExp (-θ)) := by
  rw [torusExp_neg]
  exact isConj_inv_of_mem_torus (torusExp_mem_torus θ)

/-! ### Class functions -/

/-- A class function on `SU(2)` is determined by its restriction to the maximal torus: two
conjugation-invariant functions that agree on `T` agree everywhere. -/
theorem eq_of_eqOn_torus {α : Type*} {f₁ f₂ : SU2 → α}
    (h₁ : ∀ u g : SU2, f₁ (u * g * u⁻¹) = f₁ g) (h₂ : ∀ u g : SU2, f₂ (u * g * u⁻¹) = f₂ g)
    (h : Set.EqOn f₁ f₂ (torus : Set SU2)) : f₁ = f₂ := by
  funext g
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  rw [← h₁ u g, ← h₂ u g]
  exact h hu

end SU2

end TauCeti
