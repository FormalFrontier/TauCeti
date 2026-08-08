/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Degree
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution

/-!
# Scalar multiplication in the `GL_n` Hecke ring

One row of the multiplication table of the integral Hecke ring of the arithmetic Hecke
triple (Shimura, Proposition 3.17): the scalar double coset `T(c, …, c)` has degree `1`, so
multiplying by it merely rescales diagonal cosets,
`T(c, …, c) · T(b₁, …, bₙ) = T(cb₁, …, cbₙ)`.

Degree one is what makes this elementary: the double coset of a scalar matrix is a single
left coset, so the convolution has exactly one term and the structure constant is `1`. The
mirror identity then follows from commutativity of the Hecke ring rather than a second
multiplicity computation.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), scalar row.

## Main results

* `HeckeRing.GLn.diagElem_const_mul` and `diagElem_mul_const`: `T(c, …, c) · T(b) = T(c·b)`
  and its mirror.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.17.
-/

public section

open Matrix HeckeRing DoubleCoset Finset Matrix.SpecialLinearGroup
open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section Scalar

variable [NeZero n]

private lemma mulMap_const_eq (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (p : DecompQuotient (SLnZ n) (SLnZ n)
        (((diagCoset fun _ : Fin n ↦ c).rep : GL (Fin n) ℚ)) ×
      DecompQuotient (SLnZ n) (SLnZ n) (((diagCoset b).rep : GL (Fin n) ℚ))) :
    HeckeCoset.mulMap (SLnZ n) (SLnZ n) (SLnZ n)
      (diagCoset fun _ : Fin n ↦ c).rep (diagCoset b).rep p =
      diagCoset ((fun _ ↦ c) * b) := by
  obtain ⟨L₁, hL₁, R₁, hR₁, hα⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (fun _ : Fin n ↦ c)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  have hprod : (p.1.out : GL (Fin n) ℚ) *
      ((diagCoset fun _ : Fin n ↦ c).rep : GL (Fin n) ℚ) *
      ((p.2.out : GL (Fin n) ℚ) * ((diagCoset b).rep : GL (Fin n) ℚ)) =
      ((p.1.out : GL (Fin n) ℚ) * L₁ * R₁ * p.2.out * L₂) *
        natDiagGL n ((fun _ ↦ c) * b) * R₂ := by
    -- name the coerced representatives: their types are plain `GL (Fin n) ℚ`, so the
    -- rewrites below do not have to abstract the sealed `rep` inside `p`'s type
    set σ := (p.1.out : GL (Fin n) ℚ)
    set τ := (p.2.out : GL (Fin n) ℚ)
    rw [hα, hβ, ← natDiagGL_mul n _ b (fun _ ↦ hc) hb]
    calc σ * (L₁ * natDiagGL n (fun _ ↦ c) * R₁) * (τ * (L₂ * natDiagGL n b * R₂))
        = σ * L₁ * (natDiagGL n (fun _ ↦ c) * (R₁ * τ * L₂)) * (natDiagGL n b * R₂) := by
          group
      _ = σ * L₁ * ((R₁ * τ * L₂) * natDiagGL n (fun _ ↦ c)) * (natDiagGL n b * R₂) := by
          rw [natDiagGL_const_comm n c]
      _ = σ * L₁ * R₁ * τ * L₂ * (natDiagGL n (fun _ ↦ c) * natDiagGL n b) * R₂ := by
          group
  rw [HeckeCoset.mulMap_eq_mk]
  exact (HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr
    ⟨(p.1.out : GL (Fin n) ℚ) * L₁ * R₁ * p.2.out * L₂,
      (SLnZ n).mul_mem ((SLnZ n).mul_mem ((SLnZ n).mul_mem
        ((SLnZ n).mul_mem p.1.out.2 hL₁) hR₁) p.2.out.2) hL₂,
      R₂, hR₂, hprod⟩)).trans (diagCoset_def _).symm

private lemma multiplicity_const_le_one (c : ℕ) (b : Fin n → ℕ)
    (A : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    multiplicity (SLnZ n) (SLnZ n) (SLnZ n)
      (((diagCoset fun _ : Fin n ↦ c).rep : GL (Fin n) ℚ))
      (((diagCoset b).rep : GL (Fin n) ℚ)) ((A.rep : GL (Fin n) ℚ)) ≤ 1 := by
  classical
  have hcard : Fintype.card (DecompQuotient (SLnZ n) (SLnZ n)
      (((diagCoset fun _ : Fin n ↦ c).rep : GL (Fin n) ℚ))) = 1 := by
    rw [← HeckeCoset.degree_eq_card_decompQuotient]
    exact degree_diagCoset_const n _
  have hsub : Subsingleton (DecompQuotient (SLnZ n) (SLnZ n)
      (((diagCoset fun _ : Fin n ↦ c).rep : GL (Fin n) ℚ))) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  rw [multiplicity_def, Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.mpr ?_
  constructor
  rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
  simp only [Set.mem_ofPred_eq] at hp₁ hp₂
  obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
  obtain rfl : j₁ = j₂ := DoubleCoset.snd_eq_of_fst_eq hp₁ hp₂
  rfl

/-- Scalar multiplication in the Hecke ring (Shimura, Proposition 3.17):
`T(c,...,c) · T(b) = T(c·b)`. -/
@[simp]
theorem diagElem_const_mul (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb : ∀ i, 0 < b i) :
    diagElem (fun _ : Fin n ↦ c) * diagElem b = diagElem ((fun _ ↦ c) * b) :=
  diagElem_mul_of_mulMap_eq _ _ _ (mulMap_const_eq n c hc b hb)
    (multiplicity_const_le_one n c b _)

/-- **The scalar product, on the right**: `T(b) · T(c,...,c) = T(b·c)`. The Hecke ring of
`GL_n` is commutative (transposition fixes every diagonal double coset), so this is the
left-hand case read backwards. -/
@[simp]
theorem diagElem_mul_const (b : Fin n → ℕ) (hb : ∀ i, 0 < b i) (c : ℕ) (hc : 0 < c) :
    diagElem b * diagElem (fun _ ↦ c) = diagElem (b * fun _ ↦ c) := by
  rw [HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n),
    diagElem_const_mul n c hc b hb, mul_comm (fun _ : Fin n ↦ c) b]

end Scalar

end HeckeRing.GLn
