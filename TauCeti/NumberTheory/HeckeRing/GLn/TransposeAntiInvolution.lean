/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# Commutativity of the `GL_n` Hecke ring

Transposition `ξ ↦ ᵗξ` is an anti-automorphism of `GL_n(ℚ)` preserving both `SL_n(ℤ)` and
the submonoid `Δ` of integral matrices of positive determinant, so it restricts to a
`HeckeAntiInvolution` of the arithmetic Hecke datum. Every double coset has a diagonal
representative and transposition fixes a diagonal matrix, so the involution it induces on
`SL_n(ℤ) \ Δ / SL_n(ℤ)` is the identity. Shimura's Proposition 3.8 then applies: the
integral Hecke ring of `GL_n` is commutative.

## Main definitions

* `HeckeRing.GLn.transposeGLEquiv`: transposition as an isomorphism `GL_n(ℚ) ≃* GL_n(ℚ)ᵐᵒᵖ`.
* `HeckeRing.GLn.transposeAntiInvolution`: the induced `HeckeAntiInvolution` of `(Δ, SL_n(ℤ))`.

## Main results

* `HeckeRing.GLn.transposeAntiInvolution_onHeckeCoset_eq_self`: transposition fixes every
  double coset.
* `HeckeRing.GLn.commSemiringHeckeRing`: **Shimura's Proposition 3.8 for `GL_n`** — the
  Hecke ring is commutative over any commutative semiring of coefficients, with
  `HeckeRing.GLn.commSemiringIntegralHeckeRing` the integral case.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/TransposeAntiInvolution.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing HeckeCosetModule

namespace HeckeRing.GLn

variable (n : ℕ)

/-- Transposition as an isomorphism `GL_n(ℚ) ≃* GL_n(ℚ)ᵐᵒᵖ`: it reverses products, so it
lands in the opposite group. -/
def transposeGLEquiv : GL (Fin n) ℚ ≃* (GL (Fin n) ℚ)ᵐᵒᵖ :=
  (Units.mapEquiv (Matrix.transposeRingEquiv (Fin n) ℚ).toMulEquiv).trans Units.opEquiv

/-- Transposition acts on the underlying matrix as `Matrix.transpose`. -/
@[simp] lemma transposeGLEquiv_coe (g : GL (Fin n) ℚ) :
    ((transposeGLEquiv n g).unop : Matrix (Fin n) (Fin n) ℚ) =
      (↑g : Matrix (Fin n) (Fin n) ℚ)ᵀ := by
  simp [transposeGLEquiv, Units.opEquiv, Units.mapEquiv, Matrix.transposeRingEquiv]

/-- Transposing twice is the identity. -/
@[simp] lemma transposeGLEquiv_transposeGLEquiv (g : GL (Fin n) ℚ) :
    (transposeGLEquiv n (transposeGLEquiv n g).unop).unop = g :=
  Units.ext (by ext i j; simp)

/-- Transposition preserves `SL_n(ℤ)`: the transpose of an integral matrix of determinant
one again has determinant one. -/
lemma transposeGLEquiv_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    (transposeGLEquiv n g).unop ∈ SLnZ n := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff n).mp hg
  refine (mem_SLnZ_iff n).mpr ⟨σ.transpose, Units.ext ?_⟩
  ext i j
  simp [mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.coe_transpose]

/-- Transposition preserves `Δ`: it transposes the integral witness and leaves the
determinant unchanged. -/
lemma transposeGLEquiv_mem_posDetInt {g : GL (Fin n) ℚ} (hg : g ∈ posDetInt n) :
    (transposeGLEquiv n g).unop ∈ posDetInt n := by
  obtain ⟨hint, hdet⟩ := (mem_posDetInt_iff n).mp hg
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp hint
  refine (mem_posDetInt_iff n).mpr ⟨(hasIntEntries_iff n).mpr ⟨Aᵀ, ?_⟩, ?_⟩
  · rw [transposeGLEquiv_coe, hA, Matrix.transpose_map]
  · rwa [transposeGLEquiv_coe, Matrix.det_transpose]

/-- Transposition fixes every diagonal matrix, including the junk value `1` taken when
some entry vanishes. -/
@[simp] lemma transposeGLEquiv_natDiagGL (a : Fin n → ℕ) :
    (transposeGLEquiv n (natDiagGL n a)).unop = natDiagGL n a := by
  by_cases ha : ∀ i, 0 < a i
  · exact Units.ext (by simp [natDiagGL_coe n a ha])
  · rw [natDiagGL_of_not_pos n ha]
    exact Units.ext (by simp)

/-- Transposition as an anti-involution of the arithmetic Hecke datum `(Δ, SL_n(ℤ))`. -/
noncomputable def transposeAntiInvolution :
    HeckeAntiInvolution (posDetInt n) (SLnZ n) :=
  HeckeAntiInvolution.ofAmbient (transposeGLEquiv n).toMonoidHom
    (transposeGLEquiv_transposeGLEquiv n)
    (fun _ hg ↦ transposeGLEquiv_mem_SLnZ n hg)
    (fun _ hg ↦ transposeGLEquiv_mem_posDetInt n hg)

/-- The anti-involution acts as transposition, unfolding the sealed definition. -/
@[simp] lemma transposeAntiInvolution_bar {x : GL (Fin n) ℚ} (hx : x ∈ posDetInt n) :
    (transposeAntiInvolution n).bar x hx = (transposeGLEquiv n x).unop :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

variable [NeZero n]

/-- Transposition fixes every double coset: each one has a diagonal representative, and
transposition fixes diagonal matrices. -/
@[simp] lemma transposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    (transposeAntiInvolution n).onHeckeCoset D = D := by
  obtain ⟨a, -, -, rfl⟩ := exists_diagonal_representative D
  rw [diagCoset_def, (transposeAntiInvolution n).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (SLnZ n) (SLnZ n))
    (Subtype.ext ((transposeAntiInvolution_bar n _).trans (transposeGLEquiv_natDiagGL n a)))

/-- **Shimura's Proposition 3.8 for `GL_n`**: the Hecke ring of `GL_n` over any commutative
semiring is commutative, transposition being an anti-involution that fixes every double
coset. -/
@[instance_reducible]
noncomputable def commSemiringHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (posDetInt n) (SLnZ n) R) :=
  commSemiringOfAntiInvolution R (transposeAntiInvolution n)
    (transposeAntiInvolution_onHeckeCoset_eq_self n)

/-- The integral Hecke ring of `GL_n` is commutative. -/
@[instance_reducible]
noncomputable def commSemiringIntegralHeckeRing : CommSemiring (IntegralHeckeRing n) :=
  commSemiringHeckeRing n ℤ

end HeckeRing.GLn
