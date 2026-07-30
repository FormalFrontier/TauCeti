/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional

/-!
# Characters of induced representations

This file proves the coset-representative formula for the character of a representation induced
from a finite-index subgroup. The formula is valid over any field and has no division by the
subgroup order.

## Main result

* `TauCeti.character_indFDRep_sum_quotient` expresses an induced character as a sum over left
  cosets.

## References

* [Induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  Layer 2.
* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

namespace Rep

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G}

private abbrev RightCosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

open scoped Classical in
/-- The contribution of a group element to the induced-character sum at a representative `x`. -/
private noncomputable def inducedCharacterTerm {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k S V) (g x : G) : k :=
  if h : x⁻¹ * g * x ∈ S then ρ.character ⟨x⁻¹ * g * x, h⟩ else 0

/-- The induced-character summand is unchanged on replacing a representative by another
representative of the same left coset. -/
private theorem inducedCharacterTerm_mul {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k S V) (g x : G) (s : S) :
    inducedCharacterTerm ρ g (x * s) = inducedCharacterTerm ρ g x := by
  by_cases hx : x⁻¹ * g * x ∈ S
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∈ S := by
      simpa [mul_assoc] using S.mul_mem (S.mul_mem (S.inv_mem s.2) hx) s.2
    rw [inducedCharacterTerm, dif_pos hxs, inducedCharacterTerm, dif_pos hx]
    have helem :
        (⟨(x * (s : G))⁻¹ * g * (x * s), hxs⟩ : S) =
          s⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [helem]
    simpa only [inv_inv] using ρ.char_conj ⟨x⁻¹ * g * x, hx⟩ s⁻¹
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∉ S := by
      intro h
      apply hx
      simpa [mul_assoc] using S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2)
    rw [inducedCharacterTerm, dif_neg hxs, inducedCharacterTerm, dif_neg hx]

/-- The induced-character summand depends only on the left coset of its representative. -/
private theorem inducedCharacterTerm_eq_of_mk_eq {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k S V) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    inducedCharacterTerm ρ g x = inducedCharacterTerm ρ g y := by
  have hs : x⁻¹ * y ∈ S :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact' hxy)
  let s : S := ⟨x⁻¹ * y, hs⟩
  have hy : x * (s : G) = y := by simp [s]
  rw [← hy, inducedCharacterTerm_mul]

open scoped Classical in
/-- The trace of the induced action, computed on the right-coset model. -/
private theorem trace_ind_eq_sum_rightCosets [S.FiniteIndex] [Fintype (RightCosets S)]
    (A : Rep.{u} k S)
    [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : RightCosets S,
        if Quotient.mk'' (q.out * g) = q then
          LinearMap.trace k A (A.ρ (rightCosetFactor (S := S) (q.out * g)))
        else 0 := by
  let e := indSubtypeEquivPi A
  rw [← LinearMap.trace_conj' ((Rep.ind S.subtype A).ρ g) e]
  refine LinearMap.trace_pi_of_apply_eq
    (T := e.conj ((Rep.ind S.subtype A).ρ g))
    (σ := fun q => Quotient.mk'' (q.out * g))
    (f := fun q => A.ρ (rightCosetFactor (S := S) (q.out * g))) ?_
  intro x q
  have he : indSubtypeEquivPi A (e.symm x) = x := by
    simpa only [e] using e.apply_symm_apply x
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [indSubtypeEquivPi_ρ_apply]
  exact congrArg (A.ρ (rightCosetFactor (S := S) (q.out * g)))
    (congrFun he (Quotient.mk'' (q.out * g)))

open scoped Classical in
/-- The trace computation expressed as the standard character summand, still indexed by right
cosets. -/
private theorem trace_ind_eq_sum_terms [S.FiniteIndex] [Fintype (RightCosets S)]
    (A : Rep.{u} k S) [FiniteDimensional k A] (g : G) :
    LinearMap.trace k (Rep.ind S.subtype A) ((Rep.ind S.subtype A).ρ g) =
      ∑ q : RightCosets S, inducedCharacterTerm A.ρ g q.out⁻¹ := by
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
    rw [if_pos hq, inducedCharacterTerm, dif_pos (by simpa [mul_assoc] using hmem)]
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
    rw [if_neg hq, inducedCharacterTerm, dif_neg (by simpa [mul_assoc] using hmem)]

end Rep

open scoped Classical in
/-- The induced character at `g` is the sum of the original character over those left coset
representatives `t` for which `t⁻¹ g t` belongs to the subgroup. -/
theorem character_indFDRep_sum_quotient {k G : Type u} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] [Fintype (G ⧸ S)] (A : FDRep k S) (g : G) :
    (indFDRep (k := k) (G := G) A).character g =
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          A.character ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 := by
  let A' : Rep.{u} k S := (forget₂ (FDRep k S) (Rep k S)).obj A
  letI : FiniteDimensional k A' := by
    -- The forgetful object's carrier is the same vector space, hidden behind category wrappers.
    change FiniteDimensional k A
    infer_instance
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  letI : Fintype (Rep.RightCosets S) := QuotientGroup.fintypeQuotientRightRel
  have hcharacter :
      (indFDRep (k := k) (G := G) A).character g =
        LinearMap.trace k (Rep.ind S.subtype A') ((Rep.ind S.subtype A').ρ g) := by
    simp only [indFDRep_character_eq, Representation.character, A']
  rw [hcharacter, Rep.trace_ind_eq_sum_terms A' g]
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel S
  calc
    (∑ q : Rep.RightCosets S, Rep.inducedCharacterTerm A'.ρ g q.out⁻¹) =
        ∑ t : G ⧸ S, Rep.inducedCharacterTerm A'.ρ g t.out := by
      apply Fintype.sum_equiv e
      intro q
      apply Rep.inducedCharacterTerm_eq_of_mk_eq
      have heq : e q = QuotientGroup.mk q.out⁻¹ := by
        calc
          e q = e (Quotient.mk'' q.out) :=
            congrArg e (Quotient.out_eq' q).symm
          _ = QuotientGroup.mk q.out⁻¹ := rfl
      exact heq.symm.trans (Quotient.out_eq' (e q)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Rep.inducedCharacterTerm]
      rfl

end TauCeti
