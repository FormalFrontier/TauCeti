/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.UnitaryGroup
public import TauCeti.RepresentationTheory.SU2.Basic

/-!
# Every element of `SU(2)` is conjugate into the maximal torus

The maximal torus `T` of `SU(2)` built in `TauCeti/RepresentationTheory/SU2/Basic.lean` meets
every conjugacy class: for every `g : SU(2)` there is `u : SU(2)` with `u g u⁻¹ ∈ T`. This is the
torus-conjugacy input the compact-group roadmap asks for before the classification of the
irreducible representations of `SU(2)`, and it is what makes a class function on `SU(2)`
determined by its restriction to the circle.

The proof is unitary diagonalisation, arranged so that it only needs Mathlib's spectral theorem
for *Hermitian* matrices. Mathlib has no spectral theorem for normal or unitary matrices, but in
`SU(2)` one is not needed: writing `G` for the matrix of `g`, the determinant condition forces the
Hermitian part of `G` to be a scalar,

`G + G* = (tr G) • 1`   (`TauCeti.SU2.coe_add_star`),

because `G* = G⁻¹` is the adjugate of `G` (`TauCeti.Matrix.specialUnitaryGroup.star_eq_adjugate`)
and a `2 × 2` matrix and its adjugate add up to the trace. So `G` differs from the Hermitian
matrix `H = i (G - G*)` by a scalar matrix, and any unitary that diagonalises `H` diagonalises
`G`. The eigenvector unitary supplied by the spectral theorem need not have determinant one, but
it can be rescaled by a scalar of modulus one until it does
(`TauCeti.Matrix.exists_circle_smul_mem_specialUnitaryGroup`), and rescaling by a scalar does not
change the conjugation it induces.

## Main results

* `TauCeti.SU2.exists_conj_mem_torus`: **torus conjugacy**, every element of `SU(2)` is conjugate
  into the maximal torus.
* `TauCeti.SU2.exists_isConj_torusExp`: the angle form, every element of `SU(2)` is conjugate to
  `diag (e^{iθ}, e^{-iθ})`.
* `TauCeti.SU2.isConj_inv_of_mem_torus` and `TauCeti.SU2.isConj_torusExp_neg`: the Weyl reflection,
  every element of the torus is conjugate in `SU(2)` to its inverse. With torus conjugacy this
  says every conjugacy class of `SU(2)` meets `T` in a nonempty set closed under inversion. The
  converse, that conjugate elements of `T` are equal or inverse, is not proved here, so the
  classes are not yet identified with the Weyl orbits.
* `TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus`: two conjugation-invariant functions on `SU(2)`
  that agree on the maximal torus are equal; a class function on `SU(2)` is determined by its
  restriction to `T`.
-/

public section

namespace TauCeti

namespace SU2

/-! ### Torus conjugacy -/

/-- **Conjugating by `U` carries `a • 1 + b • H` to `a • 1 + b • (star U * H * U)`.** So whenever
`star U` is a left inverse of `U`, any `U` that diagonalises `H` also diagonalises every matrix of
that form: conjugation is linear, and it fixes the identity precisely because `star U * U = 1`. -/
private theorem isDiag_star_left_conjugate_of_eq_smul_one_add_smul {R n : Type*}
    [CommSemiring R] [Star R] [Fintype n] [DecidableEq n] {G H U : Matrix n n R} {a b : R}
    (hdecomp : G = a • (1 : Matrix n n R) + b • H)
    (hUU : star U * U = 1) (hdiagH : (star U * H * U).IsDiag) :
    (star U * G * U).IsDiag := by
  have hexpand : star U * G * U = a • (1 : Matrix n n R) + b • (star U * H * U) := by
    conv_lhs => rw [hdecomp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hUU]
  rw [hexpand]
  exact (Matrix.isDiag_one.smul _).add (hdiagH.smul _)

/-- **Torus conjugacy for `SU(2)`**: every element of `SU(2)` is conjugate into the maximal torus.
Equivalently, every special unitary `2 × 2` matrix is diagonalised by a special unitary matrix. -/
theorem exists_conj_mem_torus (g : SU2) : ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  set H : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (G - star G) with hHdef
  -- `H` is Hermitian: conjugating negates both `Complex.I` and `G - star G`.
  have hHerm : H.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint, isSelfAdjoint_iff, hHdef, star_smul, star_sub,
      star_star, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
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
      (star (U : Matrix (Fin 2) (Fin 2) ℂ) * G * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag :=
    isDiag_star_left_conjugate_of_eq_smul_one_add_smul hdecomp hUU hdiagH
  -- Rescale `U` into `SU(2)`; the rescaling does not change the conjugation.
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup U
  obtain ⟨u, hu⟩ : ∃ u : SU2,
      (u : Matrix (Fin 2) (Fin 2) ℂ) = (c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ) := ⟨⟨_, hc⟩, rfl⟩
  refine ⟨u⁻¹, mem_torus_iff.mpr ?_⟩
  -- Inversion in `SU(2)` is `star`, which commutes with the coercion to matrices.
  have hcoe : ((u⁻¹ * g * (u⁻¹)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = star (u : Matrix (Fin 2) (Fin 2) ℂ) * G * (u : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.star_eq_inv,
      Matrix.specialUnitaryGroup.coe_star]
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [hcoe, hu]
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
coordinate axes. Together with `TauCeti.SU2.exists_conj_mem_torus` this says that every conjugacy
class of `SU(2)` meets the torus in a nonempty set closed under inversion. -/
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
  refine isConj_iff.mpr ⟨⟨_, hmem⟩, ?_⟩
  -- Inversion in `SU(2)` is `star`, which commutes with the coercion to matrices.
  rw [← Matrix.star_eq_inv, ← Matrix.star_eq_inv]
  refine Subtype.ext ?_
  push_cast
  rw [Matrix.specialUnitaryGroup.star_eq_adjugate, Matrix.adjugate_fin_two]
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
theorem eq_of_conjInvariant_of_eqOn_torus {α : Type*} {f₁ f₂ : SU2 → α}
    (h₁ : ∀ u g : SU2, f₁ (u * g * u⁻¹) = f₁ g) (h₂ : ∀ u g : SU2, f₂ (u * g * u⁻¹) = f₂ g)
    (h : Set.EqOn f₁ f₂ (torus : Set SU2)) : f₁ = f₂ := by
  funext g
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  rw [← h₁ u g, ← h₂ u g]
  exact h hu

end SU2

end TauCeti
