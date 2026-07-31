/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import Mathlib.RepresentationTheory.Character

/-!
# Characters of induced representations

This file proves the coset-representative formula for the character of a representation induced
from a finite-index subgroup. The formula is valid over any field and has no division by the
subgroup order.

## Main result

* `TauCeti.character_indFDRep_sum_quotient` expresses an induced character as a sum over left
  cosets.
* `TauCeti.character_ind` rewrites the coset sum as an average over the whole group when the
  subgroup order is invertible in the coefficient field.

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

section Forget

variable {k G : Type u} [Field k] [Group G] (A : FDRep k G)

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
theorem character_indFDRep_sum_quotient {k G : Type u} [Field k] [Group G]
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
      (Representation.char_iso (Representation.equivOfIso (indFDRepForgetIso A))) g)
  letI := Fintype.ofFinite (G ⧸ S)
  let A' : Rep.{u} k S := (forget₂ (FDRep k S) (Rep k S)).obj A
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  letI : Fintype (Rep.RightCosets S) := QuotientGroup.fintypeQuotientRightRel
  have hforgetCharacter (s : S) : A'.ρ.character s = A.character s := character_forget₂ A s
  have hcharacter :
      (indFDRep (k := k) (G := G) A).character g =
        LinearMap.trace k (Rep.ind S.subtype A') ((Rep.ind S.subtype A').ρ g) := by
    rw [hindCharacter, Representation.character]
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
          _ = QuotientGroup.mk q.out⁻¹ :=
            Rep.quotientRightRelEquivQuotientLeftRel_mk S q.out
      exact heq.symm.trans (Quotient.out_eq' (e q)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Rep.inducedCharacterTerm]
      by_cases hmem : t.out⁻¹ * g * t.out ∈ S
      · rw [dif_pos hmem, dif_pos hmem, hforgetCharacter]
      · rw [dif_neg hmem, dif_neg hmem]

open scoped Classical in
/-- The induced character at `g`, written as an average over the whole group. The subgroup
order must be invertible in the coefficient field; without this hypothesis,
`character_indFDRep_sum_quotient` is the division-free formula to use. -/
theorem character_ind {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [Fintype G] (hS : IsUnit (Nat.card S : k)) (A : FDRep k S) (g : G) :
    (indFDRep (k := k) (G := G) A).character g =
      (Nat.card S : k)⁻¹ * ∑ x : G,
        if h : x⁻¹ * g * x ∈ S then A.character ⟨x⁻¹ * g * x, h⟩ else 0 := by
  letI : Fintype (G ⧸ S) := Fintype.ofFinite _
  let e : G ≃ (G ⧸ S) × S := Subgroup.groupEquivQuotientProdSubgroup
  let A' : Rep k S := (forget₂ (FDRep k S) (Rep k S)).obj A
  let term : G → k := fun x ↦ Rep.inducedCharacterTerm A'.ρ g x
  have he_mk (q : G ⧸ S) (s : S) :
      QuotientGroup.mk (e.symm (q, s)) = q := by
    exact congrArg Prod.fst (e.apply_symm_apply (q, s))
  have hterm (q : G ⧸ S) (s : S) :
      term (e.symm (q, s)) = term q.out := by
    apply Rep.inducedCharacterTerm_eq_of_mk_eq
    exact (he_mk q s).trans (Quotient.out_eq' q).symm
  have hsum :
      (∑ x : G, term x) = (Nat.card S : k) * ∑ q : G ⧸ S, term q.out := by
    rw [← e.symm.sum_comp term, Fintype.sum_prod_type]
    calc
      (∑ q : G ⧸ S, ∑ s : S, term (e.symm (q, s))) =
          ∑ q : G ⧸ S, ∑ _s : S, term q.out := by
            apply Finset.sum_congr rfl
            intro q _
            apply Finset.sum_congr rfl
            intro s _
            exact hterm q s
      _ = (Nat.card S : k) * ∑ q : G ⧸ S, term q.out := by
        simp [Finset.mul_sum]
  have haverage :
      (∑ q : G ⧸ S, term q.out) = (Nat.card S : k)⁻¹ * ∑ x : G, term x := by
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ hS.ne_zero, one_mul]
  have hcharacter (s : S) : A'.ρ.character s = A.character s := character_forget₂ A s
  rw [character_indFDRep_sum_quotient]
  simpa only [term, Rep.inducedCharacterTerm, hcharacter] using haverage

end TauCeti
