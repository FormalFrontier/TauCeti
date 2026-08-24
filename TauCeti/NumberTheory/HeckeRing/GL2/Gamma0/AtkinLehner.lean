/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution

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

This file builds the anti-involution only. Commutativity of `R(Γ₀(N), Δ₀(N))` needs the further
input that `ι` fixes every double coset, which `HeckeCosetModule.mul_comm_of_antiInvolution`
takes as a separate hypothesis (Shimura, Proposition 3.8).

Ported from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
[`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
declarations `wN`, `Gamma0_AL_hom`, `Gamma0_AL_involutive`, `Gamma0_AL_map_H`,
`Gamma0_AL_map_Δ` and `Gamma0_antiInvolution`. The source states its own transpose equivalence
and diagonal-matrix API; here those come from `GLn/TransposeAntiInvolution.lean` and
`GLn/DiagonalCosets.lean` instead, and the four-field bundle is assembled by
`HeckeAntiInvolution.ofAmbient`.

## Main definitions

* `HeckeRing.GL2.atkinLehnerAntiInvolution`: the anti-involution of the `Γ₀(N)` Hecke pair.

## Main results

* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar`: how it acts, `g ↦ w · gᵀ · w⁻¹`. The bundle
  itself is opaque, so this is the elimination rule a consumer works with.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
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

end HeckeRing.GL2
