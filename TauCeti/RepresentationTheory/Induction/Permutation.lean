/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Induced

/-!
# The permutation representation as an induced representation

For a subgroup `H` of a group `G`, inducing the trivial `H`-representation along `H.subtype`
gives the permutation representation of `G` on the left cosets `G ⧸ H`, and its character counts
fixed cosets.

## Main definitions

* `TauCeti.indTrivialEquiv`: the equivalence of representations `Ind_H^G (trivial) ≃ k[G ⧸ H]`.
* `TauCeti.indTrivialIso`: the same statement in `Rep k G`.

## Main statements

* `TauCeti.indV_mk_mul`: the relation defining `Representation.IndV`, on the generators
  `Representation.IndV.mk`.
* `TauCeti.character_ofMulAction`: the character of a permutation representation at `g` counts
  the points fixed by `g`.
* `TauCeti.character_ind_trivial`: the character of `Ind_H^G (trivial)` at `g` counts the cosets
  fixed by `g`.

## Implementation notes

Mathlib's `Representation.ind` is built as the coinvariants of `k[G] ⊗[k] A`, so the coset
orientation is a proof obligation rather than a convention: the `H`-action being quotiented out is
left translation on `k[G]`, whose orbits are the *right* cosets `Hx`, while `G` acts by right
translation by the inverse. The equivalence below therefore sends `⟦single x r ⊗ₜ a⟧` to
`single ⟦x⁻¹⟧ (a • r)`; inversion is what converts right cosets carrying a right action into
Mathlib's left-coset quotient `G ⧸ H` with its left action.

## References

This is the "permutation character" item of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, whose `Suggested.lean`
records the isomorphism as `indTrivialIso`.
-/

public section

open Representation TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section IndV

variable {k : Type u} [CommRing k] {G : Type v} {G' : Type w} [Group G] [Group G']
  (φ : G →* G') {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k G A)

/-- The defining relation of the induced representation `Ind_φ ρ`: translating the group
coordinate of a generator by `φ g` is undone by acting by `g` on the coefficient. -/
theorem indV_mk_mul (g : G) (h : G') (a : A) :
    IndV.mk φ ρ (φ g * h) (ρ g a) = IndV.mk φ ρ h a := by
  refine Eq.trans (congrArg
    (Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G').comp φ) ρ)) ?_)
    (Coinvariants.mk_self_apply _ g (MonoidAlgebra.single h 1 ⊗ₜ a))
  simp [leftRegular]

end IndV

section Induced

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (H : Subgroup G)

/-- The `H`-representation on `k[G] ⊗[k] k` whose coinvariants define `Ind_H^G (trivial)`:
left translation by `H` on `k[G]`, and the trivial action on `k`. -/
private noncomputable abbrev indTrivialSource : Representation k H (k[G] ⊗[k] k) :=
  Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
    (Representation.trivial k H k)

/-- Sending `x : G` to the coset `⟦x⁻¹⟧` turns left translation by `H` into the identity. -/
private theorem mapDomain_inv_comp_leftRegular (s : H) :
    MonoidAlgebra.mapDomainLinearMap k k (fun x : G ↦ (QuotientGroup.mk x⁻¹ : G ⧸ H)) ∘ₗ
        Representation.leftRegular k G (s : G) =
      MonoidAlgebra.mapDomainLinearMap k k (fun x : G ↦ (QuotientGroup.mk x⁻¹ : G ⧸ H)) := by
  refine MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply,
    leftRegular, ofMulAction_single, smul_eq_mul, MonoidAlgebra.mapDomainLinearMap_single]
  exact congrArg (MonoidAlgebra.single · (1 : k)) (QuotientGroup.eq.2 (by simp))

/-- The linear map `k[G] ⊗[k] k →ₗ[k] k[G ⧸ H]` sending `single x r ⊗ₜ a` to
`single ⟦x⁻¹⟧ (a • r)`. -/
private noncomputable def indTrivialLift : (k[G] ⊗[k] k) →ₗ[k] k[G ⧸ H] :=
  MonoidAlgebra.mapDomainLinearMap k k (fun x : G ↦ (QuotientGroup.mk x⁻¹ : G ⧸ H)) ∘ₗ
    (TensorProduct.rid k k[G]).toLinearMap

private theorem indTrivialLift_tmul (x : G) (r a : k) :
    indTrivialLift k H (MonoidAlgebra.single x r ⊗ₜ a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) (a • r) := by
  simp [indTrivialLift]

private theorem indTrivialLift_comp (s : H) :
    indTrivialLift k H ∘ₗ indTrivialSource k H s = indTrivialLift k H := by
  refine TensorProduct.ext' fun y a ↦ ?_
  have h := LinearMap.congr_fun (mapDomain_inv_comp_leftRegular k H s) y
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  simp [indTrivialLift, h]

/-- The forward map of `TauCeti.indTrivialEquiv`, from `Ind_H^G (trivial)` to `k[G ⧸ H]`. -/
private noncomputable def indTrivialToQuotient :
    IndV H.subtype (Representation.trivial k H k) →ₗ[k] k[G ⧸ H] :=
  Coinvariants.lift _ (indTrivialLift k H) (indTrivialLift_comp k H)

private theorem indTrivialToQuotient_mk (x : G) (a : k) :
    indTrivialToQuotient k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a := by
  change indTrivialLift k H (MonoidAlgebra.single x 1 ⊗ₜ a) = _
  rw [indTrivialLift_tmul, smul_eq_mul, mul_one]

/-- Left translation by `H` is invisible in `Ind_H^G (trivial)`. -/
private theorem indV_mk_smul (s : H) (x : G) (a : k) :
    IndV.mk H.subtype (Representation.trivial k H k) ((s : G) * x) a =
      IndV.mk H.subtype (Representation.trivial k H k) x a :=
  indV_mk_mul H.subtype (Representation.trivial k H k) s x a

/-- The image of a coset `⟦x⟧` in `Ind_H^G (trivial)`, namely `⟦single x⁻¹ 1 ⊗ₜ 1⟧`. -/
private noncomputable def indTrivialMk (q : G ⧸ H) :
    IndV H.subtype (Representation.trivial k H k) :=
  Quotient.liftOn' q
    (fun x : G ↦ IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k))
    fun a b hab ↦ by
      have hs : b⁻¹ * a ∈ H := by
        simpa using H.inv_mem (QuotientGroup.leftRel_apply.1 hab)
      have h := indV_mk_smul k H ⟨b⁻¹ * a, hs⟩ a⁻¹ (1 : k)
      rw [show ((⟨b⁻¹ * a, hs⟩ : H) : G) * a⁻¹ = b⁻¹ by simp] at h
      exact h.symm

private theorem indTrivialMk_mk (x : G) :
    indTrivialMk k H (QuotientGroup.mk x) =
      IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  rfl

/-- The inverse map of `TauCeti.indTrivialEquiv`, from `k[G ⧸ H]` to `Ind_H^G (trivial)`. -/
private noncomputable def quotientToIndTrivial :
    k[G ⧸ H] →ₗ[k] IndV H.subtype (Representation.trivial k H k) :=
  Finsupp.linearCombination k (indTrivialMk k H) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem quotientToIndTrivial_single (q : G ⧸ H) (r : k) :
    quotientToIndTrivial k H (MonoidAlgebra.single q r) = r • indTrivialMk k H q := by
  simp [quotientToIndTrivial]

/-- **The permutation representation.** Inducing the trivial representation of a subgroup `H ≤ G`
along `H.subtype` gives the permutation representation of `G` on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialEquiv :
    ((Representation.trivial k H k).ind H.subtype).Equiv
      (Representation.ofMulAction k G (G ⧸ H)) := by
  refine Representation.Equiv.mk
    (LinearEquiv.ofLinear (indTrivialToQuotient k H) (quotientToIndTrivial k H) ?_ ?_) ?_
  · refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change indTrivialToQuotient k H (quotientToIndTrivial k H
          (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) (1 : k))) = _
      rw [quotientToIndTrivial_single, one_smul, indTrivialMk_mk, indTrivialToQuotient_mk,
        inv_inv]
      rfl
  · refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    change quotientToIndTrivial k H (indTrivialToQuotient k H
        (IndV.mk H.subtype (Representation.trivial k H k) x (1 : k))) = _
    rw [indTrivialToQuotient_mk, quotientToIndTrivial_single, one_smul, indTrivialMk_mk, inv_inv]
    rfl
  · intro g
    refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    change indTrivialToQuotient k H ((Representation.trivial k H k).ind H.subtype g
        (IndV.mk H.subtype (Representation.trivial k H k) x (1 : k))) =
      Representation.ofMulAction k G (G ⧸ H) g (indTrivialToQuotient k H
        (IndV.mk H.subtype (Representation.trivial k H k) x (1 : k)))
    rw [Representation.ind_mk, indTrivialToQuotient_mk, indTrivialToQuotient_mk,
      ofMulAction_single]
    congr 1
    simp [mul_inv_rev]

/-- The generator computation rule for `indTrivialEquiv`. Not a `simp` lemma: `simp` unfolds the
reducible `Representation.IndV.mk`, so the left-hand side is not in `simp`-normal form. -/
theorem indTrivialEquiv_apply_mk (x : G) (a : k) :
    indTrivialEquiv k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a :=
  indTrivialToQuotient_mk k H x a

/-- The generator computation rule for the inverse of `indTrivialEquiv`. -/
theorem indTrivialEquiv_symm_apply_single (x : G) (r : k) :
    (indTrivialEquiv k H).symm (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) r) =
      r • IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  quotientToIndTrivial_single k H _ r

/-- **The permutation representation**, in `Rep k G`: inducing the trivial representation of a
subgroup `H ≤ G` gives the permutation representation on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialIso :
    Rep.ind H.subtype (Rep.trivial k H k) ≅ Rep.ofMulAction k G (G ⧸ H) :=
  Rep.mkIso (indTrivialEquiv k H)

/-- `Ind_H^G (trivial)` is a finite module whenever `H` has finite index, by transport along
`TauCeti.indTrivialEquiv`; over a field this is the `FiniteDimensional` instance that lets one
even state its character. -/
instance instFiniteIndTrivial [Finite (G ⧸ H)] :
    Module.Finite k (IndV H.subtype (Representation.trivial k H k)) :=
  Module.Finite.equiv (indTrivialEquiv k H).toLinearEquiv.symm

end Induced

section Character

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- **The permutation character.** The character of the permutation representation `k[X]` at `g`
is the number of points of `X` fixed by `g`. -/
theorem character_ofMulAction (X : Type w) [MulAction G X] [Finite X] (g : G) :
    (Representation.ofMulAction k G X).character g = Nat.card {x : X // g • x = x} := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis X k), Matrix.trace]
  have key : ∀ i : X, LinearMap.toMatrix (MonoidAlgebra.basis X k) (MonoidAlgebra.basis X k)
      (Representation.ofMulAction k G X g) i i = if g • i = i then 1 else 0 := fun i ↦ by
    rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
      ofMulAction_single, ← MonoidAlgebra.basis_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  simp [key, Fintype.card_subtype]

variable (H : Subgroup G)

/-- **The permutation character of an induced trivial representation.** The character of
`Ind_H^G (trivial)` at `g` is the number of cosets in `G ⧸ H` fixed by `g`. -/
theorem character_ind_trivial [Finite (G ⧸ H)] (g : G) :
    ((Representation.trivial k H k).ind H.subtype).character g =
      Nat.card {q : G ⧸ H // g • q = q} := by
  rw [Representation.char_iso (indTrivialEquiv k H), character_ofMulAction]

end Character

end TauCeti
