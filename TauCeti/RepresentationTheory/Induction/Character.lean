/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional

/-!
# Characters of induced representations

This file proves the coset-representative formula for the character of a representation induced
from a finite-index subgroup. The formula is valid over any field and has no division by the
subgroup order.

## Main result

* `TauCeti.character_indFDRep_sum_quotient` expresses an induced character as a sum over left
  cosets.
* `TauCeti.indClassFun_ofFDRep_character` and `TauCeti.ClassFunction.ind_ofFDRep` identify that
  coset sum with `TauCeti.indClassFun`, the induced class function.
* `TauCeti.character_ind` rewrites the coset sum as an average over the whole group when the
  subgroup order is invertible in the coefficient field; it is the specialization of
  `TauCeti.indClassFun_eq_natCard_inv_mul_sum` to a character.

## References

* [Induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  Layer 2.
* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

namespace Rep

variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}

private abbrev RightCosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

/-- The right-to-left-coset equivalence sends the right coset of `x` to the left coset of
`x⁻¹`. Mathlib does not currently expose a computation lemma for this equivalence, so keep
the necessary unfolding of its `Quotient.map'` implementation isolated here. -/
private theorem quotientRightRelEquivQuotientLeftRel_mk (S : Subgroup G) (x : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel S (Quotient.mk'' x) =
      QuotientGroup.mk x⁻¹ := by
  change @Quotient.map' G G (QuotientGroup.rightRel S) (QuotientGroup.leftRel S)
    (fun y => y⁻¹) (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply]
      exact fun h => (congrArg (· ∈ S) (by simp)).mp (S.inv_mem h))
      (@Quotient.mk'' G (QuotientGroup.rightRel S) x) =
      @Quotient.mk'' G (QuotientGroup.leftRel S) x⁻¹
  apply Quotient.map'_mk''

/-- A character is a class function, so `TauCeti.indTerm` applies to it. -/
private theorem character_mem_classFunction {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k S V) : ρ.character ∈ ClassFunction k S :=
  ClassFunction.mem_iff.mpr ρ.char_conj

open scoped Classical in
/-- The trace of the induced action, computed on the right-coset model. -/
private theorem trace_ind_eq_sum_rightCosets [S.FiniteIndex] [Fintype (RightCosets S)]
    (A : Rep.{u} k S) [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : RightCosets S,
        if Quotient.mk'' (q.out * g) = q then
          LinearMap.trace k A (A.ρ (rightCosetFactor (S := S) (q.out * g)))
        else 0 := by
  let e := indSubtypeEquivPi A
  rw [← LinearMap.trace_conj' ((Rep.ind S.subtype A).ρ g) e]
  have hT (x : RightCosets S → A) (q : RightCosets S) :
      e.conj ((Rep.ind S.subtype A).ρ g) x q =
        A.ρ (rightCosetFactor (S := S) (q.out * g))
          (x (Quotient.mk'' (q.out * g))) := by
    have he : indSubtypeEquivPi A (e.symm x) = x := by
      simpa only [e] using e.apply_symm_apply x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [indSubtypeEquivPi_ρ_apply]
    exact congrArg (A.ρ (rightCosetFactor (S := S) (q.out * g)))
      (congrFun he (Quotient.mk'' (q.out * g)))
  rw [LinearMap.trace_pi_of_apply_eq
    (T := e.conj ((Rep.ind S.subtype A).ρ g))
    (σ := fun q => Quotient.mk'' (q.out * g))
    (f := fun q => A.ρ (rightCosetFactor (S := S) (q.out * g))) hT]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Quotient.mk'' (q.out * g) = q <;> simp [hq]

open scoped Classical in
/-- The trace computation expressed as the standard character summand, still indexed by right
cosets. -/
private theorem trace_ind_eq_sum_terms [S.FiniteIndex] [Fintype (RightCosets S)]
    (A : Rep.{u} k S) [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : RightCosets S, indTerm A.ρ.character g q.out⁻¹ := by
  rw [trace_ind_eq_sum_rightCosets A g]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Quotient.mk'' (q.out * g) = q
  · have hmem : q.out * g * q.out⁻¹ ∈ S := by
      have hq' :
          Quotient.mk'' (q.out * g) = (Quotient.mk'' q.out : RightCosets S) :=
        hq.trans (Quotient.out_eq' q).symm
      have hinv : q.out * g⁻¹ * q.out⁻¹ ∈ S := by
        simpa [mul_assoc] using
          (QuotientGroup.rightRel_apply.mp (Quotient.exact' hq'))
      simpa [mul_assoc] using S.inv_mem hinv
    rw [ite_eq_left hq, indTerm_apply, dite_eq_left (by simpa [mul_assoc] using hmem)]
    have hfactor :
        rightCosetFactor (S := S) (q.out * g) =
          ⟨q.out * g * q.out⁻¹, hmem⟩ := by
      apply Subtype.ext
      have hout :
          Quotient.out (Quotient.mk'' (q.out * g) : RightCosets S) = q.out :=
        congrArg Quotient.out hq
      calc
        (rightCosetFactor (S := S) (q.out * g) : G) =
            (rightCosetFactor (S := S) (q.out * g) : G) *
              Quotient.out (Quotient.mk'' (q.out * g) : RightCosets S) * q.out⁻¹ := by
                rw [hout]
                simp
        _ = q.out * g * q.out⁻¹ := by rw [rightCosetFactor_mul_out]
    rw [hfactor]
    simp only [Representation.character, inv_inv]
  · have hmem : q.out * g * q.out⁻¹ ∉ S := by
      intro h
      apply hq
      refine (Quotient.sound' ?_).trans (Quotient.out_eq' q)
      rw [QuotientGroup.rightRel_apply]
      simpa [mul_assoc] using S.inv_mem h
    rw [ite_eq_right hq, indTerm_apply, dite_eq_right (by simpa [mul_assoc] using hmem)]

end Rep

section Forget

variable {k : Type u} {G : Type v} [Field k] [Group G] (A : FDRep k G)

/-- Forgetting finite-dimensionality keeps the same underlying module, so it keeps the
`FiniteDimensional` instance. -/
private instance : FiniteDimensional k ((forget₂ (FDRep k G) (Rep k G)).obj A) :=
  inferInstanceAs (FiniteDimensional k A)

/-- The forgetful functor `FDRep k G ⥤ Rep k G` preserves characters. -/
private theorem character_forget₂ (g : G) :
    ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ.character g = A.character g := by
  rw [FDRep.character, Representation.character, FDRep.forget₂_ρ]
  -- The remaining `rfl` only identifies the two names of the single underlying module, the same
  -- definitional identification that lets `FDRep.forget₂_ρ` be stated at all. Keeping it here
  -- means no other proof in this file needs to unfold `forget₂`.
  rfl

end Forget

open scoped Classical in
/-- The induced character at `g` is the sum of the original character over those left coset
representatives `t` for which `t⁻¹ g t` belongs to the subgroup. -/
theorem character_indFDRep_sum_quotient {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) (g : G) :
    (indFDRep (k := k) (G := G) A).character g =
      letI := Fintype.ofFinite (G ⧸ S)
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          A.character ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 := by
  have hindCharacter :
    (indFDRep (k := k) (G := G) A).character g =
        (Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)).ρ.character g :=
    (character_forget₂ (indFDRep (k := k) (G := G) A) g).symm.trans (congrFun
      (Representation.char_iso (indFDRepForgetEquiv A)) g)
  let := Fintype.ofFinite (G ⧸ S)
  let A' : Rep.{u} k S := (forget₂ (FDRep k S) (Rep k S)).obj A
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let : Fintype (Rep.RightCosets S) := QuotientGroup.fintypeQuotientRightRel
  have hforgetCharacter (s : S) : A'.ρ.character s = A.character s := character_forget₂ A s
  have hcharacter :
      (indFDRep (k := k) (G := G) A).character g =
        LinearMap.trace k (Rep.ind S.subtype A') ((Rep.ind S.subtype A').ρ g) := by
    rw [hindCharacter, Representation.character]
  rw [hcharacter, Rep.trace_ind_eq_sum_terms A' g]
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel S
  calc
    (∑ q : Rep.RightCosets S, indTerm A'.ρ.character g q.out⁻¹) =
        ∑ t : G ⧸ S, indTerm A'.ρ.character g t.out := by
      apply Fintype.sum_equiv e
      intro q
      refine indTerm_eq_of_mk_eq (Rep.character_mem_classFunction A'.ρ) _ _ _ ?_
      have heq : e q = QuotientGroup.mk q.out⁻¹ := by
        calc
          e q = e (Quotient.mk'' q.out) :=
            congrArg e (Quotient.out_eq' q).symm
          _ = QuotientGroup.mk q.out⁻¹ :=
            Rep.quotientRightRelEquivQuotientLeftRel_mk S q.out
      exact heq.symm.trans (Quotient.out_eq' (e q)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [indTerm_apply]
      by_cases hmem : t.out⁻¹ * g * t.out ∈ S
      · rw [dite_eq_left hmem, dite_eq_left hmem, hforgetCharacter]
      · rw [dite_eq_right hmem, dite_eq_right hmem]

section ClassFun

variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}

/-- The character of an induced representation is the induced class function of its character. -/
@[simp]
theorem indClassFun_ofFDRep_character [S.FiniteIndex] (A : FDRep k S) :
    indClassFun S A.character = (indFDRep (k := k) (G := G) A).character := by
  funext g
  rw [indClassFun_apply]
  exact (character_indFDRep_sum_quotient A g).symm

/-- Inducing the class function of a finite-dimensional representation gives the class function of
the induced representation. -/
@[simp]
theorem ClassFunction.ind_ofFDRep [S.FiniteIndex] (A : FDRep k S) :
    ClassFunction.ind S (ClassFunction.ofFDRep A) =
      ClassFunction.ofFDRep (indFDRep (k := k) (G := G) A) := by
  have hcoe : ((ClassFunction.ofFDRep A : ClassFunction k S) : S → k) = A.character :=
    funext fun s => ClassFunction.ofFDRep_apply A s
  refine Subtype.ext (funext fun g => ?_)
  rw [ClassFunction.ind_apply, hcoe, indClassFun_ofFDRep_character, ClassFunction.ofFDRep_apply]

open scoped Classical in
/-- The induced character at `g`, written as an average over the whole group. The subgroup
order must be invertible in the coefficient field; without this hypothesis,
`character_indFDRep_sum_quotient` is the division-free formula to use.

This is the specialization of `TauCeti.indClassFun_eq_natCard_inv_mul_sum` to a character. -/
theorem character_ind [Fintype G] (hS : IsUnit (Nat.card S : k)) (A : FDRep k S) (g : G) :
    (indFDRep (k := k) (G := G) A).character g =
      (Nat.card S : k)⁻¹ * ∑ x : G,
        if h : x⁻¹ * g * x ∈ S then A.character ⟨x⁻¹ * g * x, h⟩ else 0 := by
  rw [← indClassFun_ofFDRep_character A]
  exact indClassFun_eq_natCard_inv_mul_sum hS
    (ClassFunction.mem_iff.mpr fun s t => A.char_conj s t) g

end ClassFun

end TauCeti
