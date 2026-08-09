/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.TrivialIntersection
public import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity

/-!
# Induction from a trivial-intersection subgroup

Let `H` be a trivial-intersection subgroup of a finite group `G`: one meeting each of its distinct
conjugates trivially (`TauCeti.IsTISubgroup`).  A class function on `H` that vanishes at the
identity then induces to `G` *without changing its values on `H`*, and therefore without changing
its norm, as long as the relevant group order is invertible in the coefficient field `k` — the
characteristic of `k` must not divide it, as everywhere in this theory, because induction divides
by that order.  Concretely, if `f` is a class function on `H` with `f 1 = 0` then

`Res_H (Ind_H^G f) = f`  when `(|H| : k)` is a unit,  hence  `⟨Ind f, Ind f⟩_G = ⟨f, f⟩_H`  when
`(|G| : k)` is (which gives the former, by `TauCeti.isUnit_natCard_subgroup`).  All the statements
below carry that hypothesis.

The first statement is `TauCeti.ClassFunction.comap_subtype_ind_eq_self` and the second is
`TauCeti.characterPairing_ind_ind`.  This is the isometry that the exceptional-character route to
Frobenius's theorem runs on: it is what makes a difference `χᵢ - χⱼ` of two *distinct* ordinary
irreducible characters of `H` *of the same degree*, which then vanishes at `1` and has norm `2`,
induce to a norm-`2` virtual character of `G`, so that it is `±` a difference of two irreducible
characters of `G`.  (Both qualifications are needed: `(χᵢ - χⱼ) 1 = χᵢ 1 - χⱼ 1` is the difference
of the two degrees, and the norm is `2` by orthonormality only for distinct ordinary characters.)

The hypothesis is not the tautology that `f` vanishes off `H`, which holds for every class function
on `H` and gives no such conclusion.  What is used is the trivial-intersection condition: for
`y ∉ H`, an element of `H` conjugated by `y` back into `H` must be the identity, where `f` vanishes.
So exactly the terms of the group sum coming from outside `H` drop out, and the remaining `|H|`
terms all equal `f x`.

## Main statements

* `TauCeti.indClassFun_apply_coe`: the induced class function agrees with `f` on `H`.
* `TauCeti.ClassFunction.comap_subtype_ind_eq_self`: restriction undoes induction, `Res ∘ Ind = id`.
* `TauCeti.characterPairing_ind_ind`: induction preserves the character pairing.
* `TauCeti.characterPairing_ind_ind_of_isTISet` and `TauCeti.isometry_ind_of_isTISet`: the same,
  for a class function supported on a trivial-intersection set of a proper trivial-intersection
  subgroup, which is the form Frobenius's theorem uses (applied there to a Frobenius complement).

## Implementation notes

Only `f₂ 1 = 0` is needed for `TauCeti.characterPairing_ind_ind`, not the same hypothesis on `f₁`:
the proof is Frobenius reciprocity `⟨Ind f₁, Ind f₂⟩ = ⟨f₁, Res (Ind f₂)⟩` followed by
`Res (Ind f₂) = f₂`, and only the second factor is restricted.  Since
`TauCeti.ClassFunction.characterPairing_symm` says the pairing is symmetric, the hypothesis may be
put on either argument.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 7, Lemma 7.2 and Theorem 7.5.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8 (`isometry_ind_of_isTISet`).
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] {H : Subgroup G} {S : Set G}

/-- **A class function vanishing at the identity of a trivial-intersection subgroup induces to a
function agreeing with it on the subgroup.**

In the group-sum form `|H| · (Ind f)(x) = ∑_{y ∈ G} f (y⁻¹ x y)` (terms with `y⁻¹ x y ∉ H` read as
`0`), a term with `y ∉ H` contributes nothing: if `y⁻¹ x y ∈ H` then the trivial-intersection
condition forces `x = 1`, and `f` vanishes there.  The `|H|` terms with `y ∈ H` each equal `f x`,
because `f` is a class function. -/
theorem indClassFun_apply_coe [Finite G] (hH : IsTISubgroup H) (hk : IsUnit (Nat.card H : k))
    {f : H → k} (hf : f ∈ ClassFunction k H) (hf1 : f 1 = 0) (x : H) :
    indClassFun H f (x : G) = f x := by
  classical
  let := Fintype.ofFinite G
  -- A representative outside `H` contributes nothing.
  have hout : ∀ y : G, y ∉ H → indTerm f (x : G) y = 0 := by
    intro y hy
    rw [indTerm_apply]
    by_cases h : y⁻¹ * (x : G) * y ∈ H
    · rw [dif_pos h]
      have hx1 : (x : G) = 1 := hH.eq_one (g := y⁻¹) (by simpa using hy) x.2 (by simpa using h)
      have hone : (⟨y⁻¹ * (x : G) * y, h⟩ : H) = 1 := by
        ext
        simp [hx1]
      rw [hone, hf1]
    · rw [dif_neg h]
  -- A representative inside `H` contributes `f x`, since `f` is a class function.
  have hin : ∀ y : H, indTerm f (x : G) (y : G) = f x := by
    intro y
    have hmem : (y : G)⁻¹ * (x : G) * (y : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem y.2) x.2) y.2
    have hcoe : (⟨(y : G)⁻¹ * (x : G) * (y : G), hmem⟩ : H) = y⁻¹ * x * y⁻¹⁻¹ := by
      ext
      simp
    rw [indTerm_apply, dif_pos hmem, hcoe]
    exact ClassFunction.mem_iff.mp hf x y⁻¹
  refine mul_left_cancel₀ hk.ne_zero ?_
  rw [natCard_mul_indClassFun hf]
  simp only [← indTerm_apply]
  calc ∑ y : G, indTerm f (x : G) y
      = ∑ y ∈ Finset.univ.filter fun y : G => y ∈ H, indTerm f (x : G) y :=
        (Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy =>
          hout y (by simpa using hy)).symm
    _ = ∑ y : H, indTerm f (x : G) (y : G) := Finset.sum_subtype _ (by simp) _
    _ = ∑ _y : H, f x := Finset.sum_congr rfl fun y _ => hin y
    _ = (Nat.card H : k) * f x := by simp [Nat.card_eq_fintype_card]

/-- **Restriction undoes induction, for a class function on a trivial-intersection subgroup that
vanishes at the identity.**  This is the bundled form of `TauCeti.indClassFun_apply_coe`. -/
theorem ClassFunction.comap_subtype_ind_eq_self [Finite G] (hH : IsTISubgroup H)
    (hk : IsUnit (Nat.card H : k)) (f : ClassFunction k H) (hf1 : f.1 1 = 0) :
    ClassFunction.comap H.subtype (ClassFunction.ind H f) = f := by
  refine Subtype.ext (funext fun x => ?_)
  simp only [ClassFunction.comap_apply, ClassFunction.ind_apply, Subgroup.coe_subtype]
  exact indClassFun_apply_coe hH hk f.2 hf1 x

open scoped Classical in
/-- **Induction from a trivial-intersection subgroup preserves the character pairing**, provided
the second argument vanishes at the identity.  This is the isometry the exceptional-character
argument for Frobenius's theorem rests on; taking `f₁ = f₂` gives the preservation of the norm. -/
theorem characterPairing_ind_ind [Fintype G] (hG : IsUnit (Nat.card G : k))
    (hH : IsTISubgroup H) (f₁ f₂ : ClassFunction k H) (hf₂ : f₂.1 1 = 0) :
    ClassFunction.characterPairing (ClassFunction.ind H f₁) (ClassFunction.ind H f₂) =
      ClassFunction.characterPairing f₁ f₂ := by
  rw [characterPairing_ind hG,
    ClassFunction.comap_subtype_ind_eq_self hH (isUnit_natCard_subgroup H hG) f₂ hf₂]

open scoped Classical in
/-- **A class function supported on a trivial-intersection set of a proper trivial-intersection
subgroup induces isometrically.**  The support condition supplies the vanishing at the identity
that `TauCeti.characterPairing_ind_ind` asks for, because a trivial-intersection set for a proper
subgroup does not contain the identity.  Nontriviality of `H` plays no part, so this asks only for
the two halves of `TauCeti.IsFrobeniusComplement` that the argument uses; for a Frobenius
complement `hH`, pass `hH.isTISubgroup` and `hH.ne_top`. -/
theorem characterPairing_ind_ind_of_isTISet [Fintype G] (hG : IsUnit (Nat.card G : k))
    (hH : IsTISubgroup H) (hne_top : H ≠ ⊤) (hS : IsTISet S H) (f₁ f₂ : ClassFunction k H)
    (hf₂ : ∀ y : H, (y : G) ∉ S → f₂.1 y = 0) :
    ClassFunction.characterPairing (ClassFunction.ind H f₁) (ClassFunction.ind H f₂) =
      ClassFunction.characterPairing f₁ f₂ :=
  characterPairing_ind_ind hG hH f₁ f₂ (hf₂ 1 (by simpa using hS.one_notMem hne_top))

open scoped Classical in
/-- **Induction from a trivial-intersection set preserves the norm**, the special case of
`TauCeti.characterPairing_ind_ind_of_isTISet` at equal arguments.  A difference of two distinct
ordinary irreducible characters of `H` of the same degree is supported off the identity and has
norm `2`, so it induces to a norm-`2` virtual character of `G`; that is the step the
exceptional-character correspondence begins with.

The name is the one the character-theory roadmap pins for this result: preserving the pairing at
equal arguments is preservation of the norm, which is what "isometry" refers to. -/
theorem isometry_ind_of_isTISet [Fintype G] (hG : IsUnit (Nat.card G : k))
    (hH : IsTISubgroup H) (hne_top : H ≠ ⊤) (hS : IsTISet S H) (f : ClassFunction k H)
    (hf : ∀ y : H, (y : G) ∉ S → f.1 y = 0) :
    ClassFunction.characterPairing (ClassFunction.ind H f) (ClassFunction.ind H f) =
      ClassFunction.characterPairing f f :=
  characterPairing_ind_ind_of_isTISet hG hH hne_top hS f f hf

end TauCeti
