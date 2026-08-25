/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
-- `mem_doubleCoset_natDiagGL_of_intWitness` (Shimura 3.33), used only inside the proof of
-- `atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft` below, so private.
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.BadPrimeCoset
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm
import Mathlib.Data.ZMod.Units

/-!
# The Atkin-Lehner anti-involution of the `Γ₀(N)` Hecke pair

Conjugating the transpose by `w = diag(1, N)`,
```
ι(g) = w · gᵀ · w⁻¹,
```
is an anti-automorphism of `GL₂(ℚ)` preserving both the image of `Γ₀(N)` and the submonoid
`Δ₀(N)`, so it restricts to a `HeckeAntiInvolution` of the `Γ₀(N)` Hecke datum.

At level one the transpose alone already does this — that is
`HeckeRing.GLn.transposeAntiInvolution`, and it is why the `GL_n` Hecke ring is commutative.
It does **not** survive the congruence condition: transposition carries `Γ₀(N)` to `Γ⁰(N)`,
swapping which off-diagonal entry is divisible by `N`. Conjugating by `w` swaps it back, which
is exactly what the Atkin-Lehner twist buys.

On entries the map is `(a, b; N c, e) ↦ (a, c; N b, e)`: the lower-left entry stays divisible
by `N`, the determinant is unchanged, and — the point of the construction — the upper-left
entry is untouched, so the coprimality condition cutting out `Δ₀(N)` transfers with no work.
Integrality of the new upper-right entry is precisely the hypothesis `N ∣ A 1 0`.

Beyond the anti-involution itself, this file proves that `ι` preserves determinants and fixes
the double coset of any `x ∈ Δ₀(N)` whose determinant is coprime to the level, or divides a
power of it. These are the good-prime and bad-prime extremes of the hypothesis
`HeckeCosetModule.mul_comm_of_antiInvolution` takes for commutativity of
`R(Γ₀(N), Δ₀(N))` (Shimura, Proposition 3.8); a mixed determinant requires both arguments.

A second criterion asks nothing of the determinant as a whole, only that the upper-left entry
of an integral witness be coprime to it. That one is entrywise, and it is the one the reduction
to primitive witnesses consumes: a primitive witness is exactly one the criterion applies to
after a change of representative. The bad-prime criterion is recovered from it, since inside
`Δ₀(N)` the upper-left entry is already a unit mod `N`.

## Main definitions

* `HeckeRing.GL2.atkinLehnerAntiInvolution`: the anti-involution of the `Γ₀(N)` Hecke pair.

## Main results

* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar`: how it acts, `g ↦ w · gᵀ · w⁻¹`. The bundle
  itself is opaque, so this is the elimination rule a consumer works with.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_val`: its entrywise action on a `Δ₀(N)` witness.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_det`: it preserves the determinant.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprimeDet`: it fixes the
  double coset when the determinant is coprime to the level.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft`: it fixes
  the double coset when the upper-left entry of an integral witness is coprime to the
  determinant.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_dvd_pow`: it fixes the double
  coset when the determinant divides a power of the level, the witness-free specialisation of
  the previous one.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
* Ported from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
  declarations `wN`, `Gamma0_AL_hom`, `Gamma0_AL_involutive`, `Gamma0_AL_map_H`,
  `Gamma0_AL_map_Δ` and `Gamma0_antiInvolution`, and — for the results added here —
  `Gamma0_AL_bar_det`, `bar_eq_SL2_conj`, `Gamma0_AL_in_DC_coprime`, `Gamma0_AL_in_DC_bad`
  and `Gamma0_AL_in_DC_of_gcd_a00_m_coprime`, all Apache-2.0 at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`. The source states its own transpose equivalence
  and diagonal-matrix API; here those come from `GLn/TransposeAntiInvolution.lean` and
  `GLn/DiagonalCosets.lean` instead, and the four-field bundle is assembled by
  `HeckeAntiInvolution.ofAmbient`. The source proves its own `Gamma0_AL_preserves_00` to see
  that the bar fixes the upper-left entry; here that is already visible in
  `atkinLehnerAntiInvolution_bar_val`, so the lemma is not reproduced.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- `ι(g) = w · gᵀ · w⁻¹`, as a homomorphism to the opposite group. -/
private noncomputable def atkinLehnerHom : GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (natDiagGL 2 ![1, N] *
    (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹)
  map_one' := by simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (transposeGLEquiv 2 (a * b)).unop =
        (transposeGLEquiv 2 b).unop * (transposeGLEquiv 2 a).unop := by
      simp only [map_mul, MulOpposite.unop_mul]
    rw [h1]; group

/-- **The value of `ι`**, stated once so the three consumers below and the public `bar`
lemma do not each rely on unfolding the definition. -/
@[simp] private lemma atkinLehnerHom_unop (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N g).unop =
      natDiagGL 2 ![1, N] * (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹ := (rfl)

/-- `ι` is involutive: transposition is, and the two conjugations by `w` cancel because
transposition fixes `w`. -/
private lemma atkinLehnerHom_involutive (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N (atkinLehnerHom N g).unop).unop = g := by
  simp only [atkinLehnerHom_unop]
  have h_tr : (transposeGLEquiv 2 (natDiagGL 2 ![1, N] *
      (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹)).unop =
      (transposeGLEquiv 2 (natDiagGL 2 ![1, N])⁻¹).unop *
        (transposeGLEquiv 2 (transposeGLEquiv 2 g).unop).unop *
        (transposeGLEquiv 2 (natDiagGL 2 ![1, N])).unop := by
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]
    group
  have h_inv : (transposeGLEquiv 2 (natDiagGL 2 ![1, N])⁻¹).unop =
      (natDiagGL 2 ![1, N])⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, transposeGLEquiv_natDiagGL 2 ![1, N]]
  rw [h_tr, transposeGLEquiv_transposeGLEquiv, transposeGLEquiv_natDiagGL 2 ![1, N], h_inv]
  group

/-- The entries of `ι(g)`: `(a, b; N c, e) ↦ (a, c; N b, e)`, as an integral matrix. Gives the
value lemma, the determinant lemma and the two membership proofs one spelling instead of four
copies of the literal; the public `atkinLehnerAntiInvolution_bar_val` writes the matrix out
rather than exposing this constructor. -/
private def atkinLehnerEntries (A : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]

/-- The integral matrix of `ι(g)`. Conjugating the transpose by `w = diag(1, N)` divides the
upper-right entry by `N` and multiplies the lower-left by `N`; the first is integral exactly
because `N ∣ A 1 0`, which is the `Δ₀(N)` shape. The two diagonal entries are untouched — in
particular the upper-left one, which is why every coprimality hypothesis about it survives.

This is the one computation both membership proofs below need, so it is done once here. -/
private lemma atkinLehnerHom_unop_val [NeZero N] (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (((atkinLehnerHom N g).unop : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (atkinLehnerEntries N A c).map (Int.cast : ℤ → ℚ) := by
  have hpos : ∀ i : Fin 2, 0 < (![1, N]) i := by
    intro i; fin_cases i <;> simp [NeZero.pos]
  have hNe : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hw : ((natDiagGL 2 ![1, N] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)] := by
    rw [natDiagGL_coe 2 _ hpos]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hwinv : (((natDiagGL 2 ![1, N])⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)⁻¹] := by
    rw [Matrix.coe_units_inv, hw]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hNe]
  have hcast : ((A 1 0 : ℤ) : ℚ) = (N : ℚ) * ((c : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hc
  simp only [atkinLehnerHom_unop, atkinLehnerEntries, Units.val_mul, hw, hwinv,
    transposeGLEquiv_coe, hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      Matrix.transpose_apply, hcast] <;>
    field_simp

/-- Conjugating the transpose by `w` swaps which off-diagonal entry carries the factor `N`, so
the determinant is unchanged. Both membership proofs need this, at different right-hand sides. -/
private lemma atkinLehnerEntries_det (A : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) : (atkinLehnerEntries N A c).det = A.det := by
  rw [atkinLehnerEntries, Matrix.det_fin_two_of, Matrix.det_fin_two, hc]
  ring

/-- `ι` preserves the image of `Γ₀(N)`: the transported matrix again has determinant one and
lower-left entry divisible by `N`. -/
private lemma atkinLehnerHom_mem_Gamma0Image [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ Gamma0Image N) : (atkinLehnerHom N g).unop ∈ Gamma0Image N := by
  rw [mem_Gamma0Image_iff] at hg ⊢
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ_mem
  obtain ⟨c, hc⟩ := hσ_mem
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hA_def
  set B : Matrix (Fin 2) (Fin 2) ℤ := atkinLehnerEntries N A c with hB
  have hB_det : B.det = 1 := by rw [hB, atkinLehnerEntries_det N A c hc, hA_def, σ.2]
  refine ⟨⟨B, hB_det⟩, Gamma0_mem.mpr ?_, Units.ext ?_⟩
  · simp only [hB, atkinLehnerEntries]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right _ _
  · -- the entrywise cast of an integral special-linear element, inlined as at
    -- `GL2/DiagonalCosetDegree.lean`
    have hval : ∀ μ : SpecialLinearGroup (Fin 2) ℤ,
        ((mapGL ℚ μ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
          (μ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) :=
      fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    rw [atkinLehnerHom_unop_val N _ A (hval σ) c hc, hval ⟨B, hB_det⟩]

/-- `ι` preserves `Δ₀(N)`: the determinant and the upper-left entry are unchanged, and the new
lower-left entry `N · A 0 1` is visibly divisible by `N`. -/
private lemma atkinLehnerHom_mem_Delta0 [NeZero N] (g : GL (Fin 2) ℚ) (hg : g ∈ Delta0 N) :
    (atkinLehnerHom N g).unop ∈ Delta0 N := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hg
  obtain ⟨c, hc⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ := atkinLehnerEntries N A c with hB
  have hval := atkinLehnerHom_unop_val N g A hA c hc
  have hB_det : B.det = A.det := by rw [hB, atkinLehnerEntries_det N A c hc]
  refine (mem_Delta0_iff N).mpr ⟨B, hval, ?_, ⟨A 0 1, by simp [hB, atkinLehnerEntries]⟩, ?_⟩
  · rw [hval, ← Int.cast_det, hB_det, Int.cast_det, ← hA]
    exact hdet
  · simpa [hB, atkinLehnerEntries] using hAunit

/-- **The Atkin-Lehner anti-involution** `g ↦ w · gᵀ · w⁻¹` of the `Γ₀(N)` Hecke pair, where
`w = diag(1, N)`.

`w` is the diagonal rescaling that repairs the transpose's failure to preserve `Γ₀(N)`. It is
**not** the Atkin-Lehner matrix of the operator `𝒲_Q`, which is `!![0, -1; N, 0]`.

Stated at the **unfolded** `(Gamma0 N).map (mapGL ℚ)`, which is where
`Gamma0/Basic.lean` puts the `IsHeckeTriple` instance. That matters and is not cosmetic:
`HeckeCosetModule.mul_comm_of_antiInvolution` asks for a `HeckeAntiInvolution Δ H` together
with `[IsHeckeTriple Δ H H]` at the *same* `H`, and instance search does not see through the
sealed `Gamma0Image` definition. Stated at `Gamma0Image N` the two do not compose at all —
the Hecke ring `𝕋 (Delta0 N) (Gamma0Image N) ℤ` does not even have a multiplication, since
that too comes from the instance. Measured both ways. -/
noncomputable def atkinLehnerAntiInvolution [NeZero N] :
    HeckeAntiInvolution (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerHom N) (atkinLehnerHom_involutive N)
    (fun g hg ↦ by
      rw [← Gamma0Image_def] at hg ⊢
      exact atkinLehnerHom_mem_Gamma0Image N g hg)
    (atkinLehnerHom_mem_Delta0 N)

/-- The anti-involution acts by conjugating the transpose by `w`, unfolding the sealed
definition. -/
@[simp] lemma atkinLehnerAntiInvolution_bar [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolution N).bar x hx =
      natDiagGL 2 ![1, N] * (transposeGLEquiv 2 x).unop * (natDiagGL 2 ![1, N])⁻¹ :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- **The entrywise action**, on the bundle: `(a, b; N c, e) ↦ (a, c; N b, e)`. This is the
form a consumer of `Δ₀(N)` elements needs; without it the entries can only be recovered by
redoing the diagonal-conjugation computation. -/
lemma atkinLehnerAntiInvolution_bar_val [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]).map (Int.cast : ℤ → ℚ) := by
  have hbar : ((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) = (atkinLehnerHom N x).unop :=
    HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx
  rw [hbar]
  exact atkinLehnerHom_unop_val N x A hA c hc

/-- The ambient map preserves determinants: conjugation cannot change one, and neither can
transposition. Stated for every `x : GL (Fin 2) ℚ`, since nothing here needs `Δ₀(N)`. -/
private lemma atkinLehnerHom_unop_det (x : GL (Fin 2) ℚ) :
    (((atkinLehnerHom N x).unop : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (x : Matrix (Fin 2) (Fin 2) ℚ).det := by
  simp only [atkinLehnerHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    Units.val_mul, Matrix.det_units_conj, transposeGLEquiv_coe, Matrix.det_transpose]

/-- **The bar preserves the determinant**, so a determinant hypothesis on `x` transfers to
`bar x` unchanged. -/
-- Deliberately not `@[simp]`: `atkinLehnerAntiInvolution_bar` is already `@[simp]` and its
-- left-hand side `bar x hx` is a strict subterm of this one's, so `simp` unfolds the bar first
-- and this lemma's left-hand side is never in normal form. Tagging it makes `lint-env` fail with
-- one new `simpNF` violation; measured, not assumed. Do not add the annotation.
lemma atkinLehnerAntiInvolution_bar_det [NeZero N] {x : GL (Fin 2) ℚ}
    (hx : x ∈ Delta0 N) :
    (((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = (x : Matrix (Fin 2) (Fin 2) ℚ).det := by
  have hbar : ((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) =
      (atkinLehnerHom N x).unop :=
    HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx
  rw [hbar]
  exact atkinLehnerHom_unop_det N x

/-- Common divisors of an integral matrix survive the entry swap defining the Atkin–Lehner
bar, provided they are coprime to the level. -/
private lemma dvd_atkinLehnerEntries (A : Matrix (Fin 2) (Fin 2) ℤ) (e c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) (he : ∀ i j, e ∣ A i j)
    (heN : IsCoprime e (N : ℤ)) :
    ∀ i j, e ∣ atkinLehnerEntries N A c i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [atkinLehnerEntries] using he 0 0
  · simpa [atkinLehnerEntries] using heN.dvd_of_dvd_mul_left (hc ▸ he 1 0)
  · simpa [atkinLehnerEntries] using dvd_mul_of_dvd_right (he 0 1) (N : ℤ)
  · simpa [atkinLehnerEntries] using he 1 1

/-- The integral matrices of `x` and its Atkin–Lehner bar are equivalent under determinant-one
row and column operations. Smith normal form reduces this to preservation of the determinant
and of the content; the latter is where the `Δ₀(N)` upper-left coprimality is used. -/
private lemma exists_sl2_mul_mul_eq_atkinLehnerEntries
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA_det_pos : 0 < A.det) (c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) (hAco : Int.gcd (A 0 0) N = 1) :
    ∃ P Q : SpecialLinearGroup (Fin 2) ℤ,
      (P : Matrix (Fin 2) (Fin 2) ℤ) * A * (Q : Matrix (Fin 2) (Fin 2) ℤ) =
        atkinLehnerEntries N A c := by
  set B := atkinLehnerEntries N A c with hB
  have hB_det : B.det = A.det := by rw [hB, atkinLehnerEntries_det N A c hc]
  obtain ⟨LA, RA, dA, hdA_pos, hdA_div, hA_snf⟩ :=
    A.exists_smith_normal_form_of_det_pos hA_det_pos
  obtain ⟨LB, RB, dB, hdB_pos, hdB_div, hB_snf⟩ :=
    B.exists_smith_normal_form_of_det_pos (hB_det ▸ hA_det_pos)
  have hdA_A : ∀ i j, dA 0 ∣ A i j := fun i j ↦
    Matrix.invariant_factor_zero_dvd_entries A dA (fun k ↦ hdA_div (Fin.zero_le k))
      LA.toGL RA.toGL hA_snf i j
  have hdB_B : ∀ i j, dB 0 ∣ B i j := fun i j ↦
    Matrix.invariant_factor_zero_dvd_entries B dB (fun k ↦ hdB_div (Fin.zero_le k))
      LB.toGL RB.toGL hB_snf i j
  have hAco' : IsCoprime (A 0 0) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hAco
  have hdA_B : ∀ i j, dA 0 ∣ B i j := by
    rw [hB]
    exact dvd_atkinLehnerEntries N A (dA 0) c hc hdA_A
      (hAco'.of_isCoprime_of_dvd_left (hdA_A 0 0))
  have hB00 : B 0 0 = A 0 0 := by simp [hB, atkinLehnerEntries]
  have hBc : B 1 0 = (N : ℤ) * A 0 1 := by simp [hB, atkinLehnerEntries]
  have hswap : atkinLehnerEntries N B (A 0 1) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB, atkinLehnerEntries, hc]
  have hdB_A : ∀ i j, dB 0 ∣ A i j := fun i j ↦ by
    have h := dvd_atkinLehnerEntries N B (dB 0) (A 0 1) hBc hdB_B
      (hAco'.of_isCoprime_of_dvd_left (hB00 ▸ hdB_B 0 0)) i j
    rwa [hswap] at h
  have hdA0_dvd_dB0 : dA 0 ∣ dB 0 :=
    Matrix.dvd_diag_of_dvd_entries B (dA 0) dB LB RB hB_snf hdA_B 0
  have hdB0_dvd_dA0 : dB 0 ∣ dA 0 :=
    Matrix.dvd_diag_of_dvd_entries A (dB 0) dA LA RA hA_snf hdB_A 0
  have hd0 : dA 0 = dB 0 := le_antisymm
    (Int.le_of_dvd (hdB_pos 0) hdA0_dvd_dB0)
    (Int.le_of_dvd (hdA_pos 0) hdB0_dvd_dA0)
  have hprodA : dA 0 * dA 1 = A.det := by
    have h := congrArg Matrix.det hA_snf
    simp only [Matrix.det_mul, LA.2, RA.2, one_mul, mul_one, Matrix.det_diagonal,
      Fin.prod_univ_two] at h
    exact h.symm
  have hprodB : dB 0 * dB 1 = B.det := by
    have h := congrArg Matrix.det hB_snf
    simp only [Matrix.det_mul, LB.2, RB.2, one_mul, mul_one, Matrix.det_diagonal,
      Fin.prod_univ_two] at h
    exact h.symm
  have hd1 : dA 1 = dB 1 := mul_left_cancel₀ (ne_of_gt (hdA_pos 0)) (by
    rw [hprodA, hd0, hprodB, hB_det])
  have hdiag : Matrix.diagonal dA = Matrix.diagonal dB := by
    congr 1
    funext i
    fin_cases i <;> assumption
  refine ⟨LB⁻¹ * LA, RA * RB⁻¹, ?_⟩
  have hLB : (LB⁻¹).val * LB.val = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have hRB : RB.val * (RB⁻¹).val = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  calc
    ((LB⁻¹ * LA : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A *
        ((RA * RB⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        (LB⁻¹).val * (LA.val * A * RA.val) * (RB⁻¹).val := by
          simp only [SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    _ = (LB⁻¹).val * Matrix.diagonal dB * (RB⁻¹).val := by rw [hA_snf, hdiag]
    _ = (LB⁻¹).val * (LB.val * B * RB.val) * (RB⁻¹).val := by rw [hB_snf]
    _ = B := by
      simp only [Matrix.mul_assoc]
      rw [hRB, Matrix.mul_one, ← Matrix.mul_assoc (LB⁻¹).val, hLB, Matrix.one_mul]
    _ = atkinLehnerEntries N A c := hB

/-- An integer that is a unit mod `N` is coprime to `N`. -/
private lemma int_gcd_natCast_eq_one_of_isUnit {a : ℤ} (h : IsUnit (a : ZMod N)) :
    Int.gcd a N = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp
    (isCoprime_comm.mp ((ZMod.coe_int_isUnit_iff_isCoprime _ _).mp h))

/-- **The Atkin–Lehner involution fixes a coprime-determinant double coset.** If `x ∈ Δ₀(N)`
has determinant coprime to `N`, then its bar lies in the `Γ₀(N)`-double coset of `x`. -/
-- The Smith normal forms of an integral witness for `x` and its entry-swapped bar agree: their
-- first invariant factors agree because the upper-left entry is coprime to `N`, and their second
-- invariant factors then agree because the determinants do. Thus they define the same level-one
-- double coset. Shimura's Proposition 3.31, `toLevelOneCoset_injOn`, recovers equality of the
-- `Γ₀(N)`-double cosets from that equality.
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprimeDet [NeZero N]
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (hcop : CoprimeDet N ⟨x, hx⟩) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hx
  obtain ⟨c, hc⟩ := hAN
  set a : Delta0 N := ⟨x, hx⟩
  set b : Delta0 N :=
    ⟨(atkinLehnerAntiInvolution N).bar x hx,
      (atkinLehnerAntiInvolution N).bar_mem_Δ x hx⟩
  set B := atkinLehnerEntries N A c with hB
  have hbar : ((b : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      B.map (Int.cast : ℤ → ℚ) := by
    simpa only [b, hB, atkinLehnerEntries] using
      atkinLehnerAntiInvolution_bar_val N hx A hA c hc
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hdet
  have hAco : Int.gcd (A 0 0) N = 1 := int_gcd_natCast_eq_one_of_isUnit N hAunit
  obtain ⟨P, Q, hPQ⟩ :=
    exists_sl2_mul_mul_eq_atkinLehnerEntries N A hA_det_pos c hc hAco
  have hb_cop : CoprimeDet N b := by
    rw [coprimeDet_iff N hbar, hB, atkinLehnerEntries_det N A c hc]
    exact (coprimeDet_iff N hA).mp hcop
  have hlevel : toLevelOneCoset N
      (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) a) =
      toLevelOneCoset N
        (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) b) := by
    simp only [toLevelOneCoset_mk]
    symm
    apply HeckeCoset.mk_eq_mk_of_mem
    rw [Submonoid.coe_inclusion, Submonoid.coe_inclusion]
    exact mem_doubleCoset_SLnZ_of_intMatrix_eq 2 P Q x (b : GL (Fin 2) ℚ) A B hA hbar
      (hPQ.trans hB.symm)
  have ha_cop : HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) a ∈
      {D | CoprimeDetCoset N D} := by simpa [a] using hcop
  have hb_coset_cop :
      HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) b ∈
        {D | CoprimeDetCoset N D} := by simpa using hb_cop
  have hcoset := toLevelOneCoset_injOn N ha_cop hb_coset_cop hlevel
  have hdc : DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) =
      DoubleCoset.doubleCoset (b : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) := by
    simpa only [a] using HeckeCoset.eq_iff.mp hcoset
  rw [hdc]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- **The Atkin–Lehner involution fixes a double coset whose upper-left entry is coprime to
the determinant.** If `x ∈ Δ₀(N)` has integral witness `A` and determinant `m`, and `A 0 0` is
coprime to `m`, then `bar x` lies in the `Γ₀(N)`-double coset of `x` itself.

Where the other two criteria read the determinant as a whole, this one reads a single
*entry*. Membership of `Δ₀(N)` already forces `A 0 0` to be a unit mod `N`; this asks
the same at `m`.

It is the form the reduction to primitive witnesses consumes, and the bad-prime criterion
below is its witness-free specialisation. -/
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft [NeZero N] (m : ℕ)
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) (ham : Int.gcd (A 0 0) m = 1) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨B, hB, -, hBN, -⟩ := (mem_Delta0_iff N).mp hx
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ A 1 0 := by
    rwa [Matrix.map_injective (Int.cast_injective (α := ℚ)) (hB.symm.trans hA)] at hBN
  rw [DoubleCoset.doubleCoset_eq_of_mem
    (mem_doubleCoset_natDiagGL_of_intWitness N m x A hA ⟨c, hc⟩ hdet ham)]
  exact mem_doubleCoset_natDiagGL_of_intWitness N m _ !![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]
    (atkinLehnerAntiInvolution_bar_val N hx A hA c hc) (by simp)
    ((atkinLehnerAntiInvolution_bar_det N hx).trans hdet) (by simpa using ham)

/-- **The Atkin–Lehner involution fixes a bad-prime double coset.** If `x ∈ Δ₀(N)` has
determinant `m` with `m ∣ N ^ k`, then `bar x` lies in the `Γ₀(N)`-double coset of `x` itself.

This is the *bad* case, where `m` shares its primes with the level; the coprime case is
separate. It supplies the bad-prime half of the fixing hypothesis that
`HeckeCosetModule.mul_comm_of_antiInvolution` requires, and is the statement to quote when no
integral witness is in hand. -/
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_dvd_pow [NeZero N] (m k : ℕ)
    (hm_dvd : m ∣ N ^ k) (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N)
    (hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, -, -, hAunit⟩ := (mem_Delta0_iff N).mp hx
  refine atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft N m x hx A hA hdet ?_
  have hmN : (m : ℤ) ∣ (N : ℤ) ^ k := by exact_mod_cast Int.natCast_dvd_natCast.mpr hm_dvd
  exact Int.isCoprime_iff_gcd_eq_one.mp
    ((Int.isCoprime_iff_gcd_eq_one.mpr
      (int_gcd_natCast_eq_one_of_isUnit N hAunit)).pow_right.of_isCoprime_of_dvd_right hmN)

end HeckeRing.GL2
