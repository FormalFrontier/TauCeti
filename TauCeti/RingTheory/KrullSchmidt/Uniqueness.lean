/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Cardinal.NatCard
public import TauCeti.RingTheory.KrullSchmidt.Exchange

/-!
# The Krull-Schmidt theorem

`TauCeti.exists_indecomposable_decomposition` writes a module of finite length as an internal
direct sum of indecomposable submodules. This file proves that the decomposition is **unique**:
any two of them have the same number of summands, matched up to isomorphism by a bijection of the
index sets.

The proof is the exchange induction. Given decompositions `⨆ i, P i = ⊤ = ⨆ j, Q j`, pick an index
`i₀`. The summand `P i₀` is an indecomposable direct summand of `M`, so Azumaya's exchange lemma
`TauCeti.exists_linearEquiv_and_isCompl_biSup_ne` produces a `j₀` with `P i₀ ≃ₗ Q j₀` and with `M`
the direct sum of `P i₀` and `⨆ j ≠ j₀, Q j`. Both `⨆ i ≠ i₀, P i` and `⨆ j ≠ j₀, Q j` are then
complements of `P i₀`, hence isomorphic; transporting the first decomposition along that
isomorphism gives two decompositions of one module with one fewer summand, and the induction
closes.

## Main results

* `TauCeti.exists_equiv_linearEquiv_of_iSupIndep`: **the Krull-Schmidt theorem**, for two families
  of indecomposable submodules indexed by finite types.
* `TauCeti.exists_equiv_linearEquiv_of_finset`: the same in the `Finset` packaging produced by
  `TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq`.
* `TauCeti.card_eq_card_of_iSupIndep` and `TauCeti.card_eq_card_of_finset`: in particular the two
  decompositions have the same number of summands.

## Implementation notes

The decompositions are spelled as `iSupIndep` together with `⨆ i, P i = ⊤` rather than as
`DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on the index type that the
statement does not need; the two are interchanged inside the proofs by
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`. The finiteness of `M` is carried as
the instance pair `[IsNoetherian A M] [IsArtinian A M]` on the results indexed by a type, and in the
`IsFiniteLength A M` spelling on the `Finset` results, which is the form
`TauCeti.exists_indecomposable_decomposition` produces them in.

The induction is on `Nat.card` of the first index type, and it changes the ambient module: the
recursive call is made on `↥(⨆ j ≠ j₀, Q j)`. That is why it is packaged as a private auxiliary
statement quantifying over the module as well, rather than run inside the theorem below.
Restricting a decomposition to the submodule it spans is Mathlib's
`DirectSum.isInternal_biSup_submodule_of_iSupIndep`; transporting one along a linear equivalence is
`TauCeti.iSupIndep_map_of_linearEquiv` and `TauCeti.iSup_map_of_linearEquiv_eq_top` below.

## References

This implements the uniqueness bullet of Layer 2 ("the Krull-Schmidt theorem") of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v w x

variable {A : Type u} [Ring A]

/-! ### Transporting a decomposition along a linear equivalence -/

section Transport

variable {M : Type v} {M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
variable {ι : Type w} {P : ι → Submodule A M}

/-- Independence of a family of submodules is preserved by the image along a linear
equivalence. -/
theorem iSupIndep_map_of_linearEquiv (e : M ≃ₗ[A] M') (h : iSupIndep P) :
    iSupIndep fun i ↦ (P i).map (e : M →ₗ[A] M') :=
  (iSupIndep_map_orderIso_iff (Submodule.orderIsoMapComap e)).mpr h

/-- A family of submodules spanning the whole module still spans it after taking images along a
linear equivalence. -/
theorem iSup_map_of_linearEquiv_eq_top (e : M ≃ₗ[A] M') (h : ⨆ i, P i = ⊤) :
    ⨆ i, (P i).map (e : M →ₗ[A] M') = ⊤ := by
  rw [← Submodule.map_iSup, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

end Transport

/-! ### The exchange induction -/

/-- The induction behind `TauCeti.exists_equiv_linearEquiv_of_iSupIndep`, stated with the ambient
module universally quantified because the inductive step passes to a proper submodule of it. -/
private theorem exists_equiv_linearEquiv_aux :
    ∀ (n : ℕ) {M : Type v} [AddCommGroup M] [Module A M] [IsNoetherian A M] [IsArtinian A M]
      {ι : Type w} {κ : Type x} [Finite ι] [Finite κ] {P : ι → Submodule A M}
      {Q : κ → Submodule A M}, Nat.card ι = n → iSupIndep P → ⨆ i, P i = ⊤ →
      (∀ i, IsIndecomposableModule A (P i)) → iSupIndep Q → ⨆ j, Q j = ⊤ →
      (∀ j, IsIndecomposableModule A (Q j)) →
      ∃ e : ι ≃ κ, ∀ i, Nonempty (P i ≃ₗ[A] Q (e i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ ι κ _ _ P Q hcard hP hPt hPind hQ hQt hQind
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · -- With no summands the module is trivial, so the other decomposition is empty too.
    have hbot : (⊤ : Submodule A M) = ⊥ := by rw [← hPt, iSup_of_empty]
    have : IsEmpty κ := by
      refine ⟨fun j ↦ ?_⟩
      refine Submodule.nontrivial_iff_ne_bot.mp (hQind j).nontrivial ?_
      simpa [hbot] using (le_top : Q j ≤ ⊤)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i ↦ isEmptyElim i⟩
  -- The summand `P i₀` is complemented by the other `P`s.
  set s : Set ι := {i | i ≠ i₀} with hs
  set S : Submodule A M := ⨆ i ∈ s, P i with hS
  have hcomplP : IsCompl (P i₀) S := by
    refine ⟨hP i₀, codisjoint_iff.mpr ?_⟩
    rw [hS, ← hPt]
    exact (iSup_split_single P i₀).symm
  -- Exchange it for a summand of the second decomposition.
  obtain ⟨j₀, ⟨e₀⟩, hexch⟩ :=
    exists_linearEquiv_and_isCompl_biSup_ne hQ hQt hQind hcomplP (hPind i₀)
  set t : Set κ := {j | j ≠ j₀}
  set T : Submodule A M := ⨆ j ∈ t, Q j
  -- The two complements of `P i₀` are isomorphic.
  set φ : S ≃ₗ[A] T :=
    (Submodule.quotientEquivOfIsCompl (P i₀) S hcomplP).symm ≪≫ₗ
      Submodule.quotientEquivOfIsCompl (P i₀) T hexch
  -- Read both decompositions inside `T`.
  have hPle : ∀ i : s, P i ≤ S := fun i ↦ le_biSup P i.2
  have hQle : ∀ j : t, Q j ≤ T := fun j ↦ le_biSup Q j.2
  obtain ⟨hPi, hPs⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
    (DirectSum.isInternal_biSup_submodule_of_iSupIndep s (hP.comp Subtype.val_injective))
  obtain ⟨hQi, hQs⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
    (DirectSum.isInternal_biSup_submodule_of_iSupIndep t (hQ.comp Subtype.val_injective))
  set P' : s → Submodule A T := fun i ↦ ((P i).comap S.subtype).map (φ : S →ₗ[A] T)
  set Q' : t → Submodule A T := fun j ↦ (Q j).comap T.subtype
  have hPP' : ∀ i : s, Nonempty (P i ≃ₗ[A] P' i) := fun i ↦
    ⟨(Submodule.comapSubtypeEquivOfLe (hPle i)).symm ≪≫ₗ
      Submodule.equivMapOfInjective (φ : S →ₗ[A] T) φ.injective _⟩
  have hQQ' : ∀ j : t, Nonempty (Q' j ≃ₗ[A] Q j) := fun j ↦
    ⟨Submodule.comapSubtypeEquivOfLe (hQle j)⟩
  -- The inductive hypothesis, on one fewer summand.
  obtain ⟨e', he'⟩ := ih (Nat.card s)
    (hcard ▸ Finite.card_subtype_lt (p := fun i ↦ i ∈ s) (x := i₀) (by simp [hs]))
    (M := T) (ι := s) (κ := t) (P := P') (Q := Q') rfl
    (iSupIndep_map_of_linearEquiv φ hPi) (iSup_map_of_linearEquiv_eq_top φ hPs)
    (fun i ↦ (hPind i).of_linearEquiv (hPP' i).some) hQi hQs
    (fun j ↦ (hQind j).of_linearEquiv (hQQ' j).some.symm)
  -- Extend the matching by `i₀ ↦ j₀`.
  refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans
    ((Equiv.optionCongr e').trans (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · refine ⟨?_⟩
    have hnone : ((Equiv.optionSubtypeNe i).symm.trans
        ((Equiv.optionCongr e').trans (Equiv.optionSubtypeNe j₀))) i = j₀ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self]
      rfl
    rw [hnone]
    exact e₀
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi,
      Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
    exact ⟨(hPP' ⟨i, hi⟩).some ≪≫ₗ (he' ⟨i, hi⟩).some ≪≫ₗ (hQQ' (e' ⟨i, hi⟩)).some⟩

/-! ### The Krull-Schmidt theorem -/

variable {M : Type v} [AddCommGroup M] [Module A M]

/-- **The Krull-Schmidt theorem.** Two decompositions of a module of finite length into
indecomposable submodules are matched by a bijection of their index sets under which corresponding
summands are isomorphic.

Existence of such a decomposition is `TauCeti.exists_indecomposable_decomposition`. -/
theorem exists_equiv_linearEquiv_of_iSupIndep [IsNoetherian A M] [IsArtinian A M]
    {ι : Type w} {κ : Type x} [Finite ι] [Finite κ] {P : ι → Submodule A M}
    {Q : κ → Submodule A M} (hP : iSupIndep P) (hPt : ⨆ i, P i = ⊤)
    (hPind : ∀ i, IsIndecomposableModule A (P i)) (hQ : iSupIndep Q) (hQt : ⨆ j, Q j = ⊤)
    (hQind : ∀ j, IsIndecomposableModule A (Q j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (P i ≃ₗ[A] Q (e i)) :=
  exists_equiv_linearEquiv_aux (Nat.card ι) rfl hP hPt hPind hQ hQt hQind

/-- Two decompositions of a module of finite length into indecomposable submodules have the same
number of summands. -/
theorem card_eq_card_of_iSupIndep [IsNoetherian A M] [IsArtinian A M]
    {ι : Type w} {κ : Type x} [Finite ι] [Finite κ] {P : ι → Submodule A M}
    {Q : κ → Submodule A M} (hP : iSupIndep P) (hPt : ⨆ i, P i = ⊤)
    (hPind : ∀ i, IsIndecomposableModule A (P i)) (hQ : iSupIndep Q) (hQt : ⨆ j, Q j = ⊤)
    (hQind : ∀ j, IsIndecomposableModule A (Q j)) : Nat.card ι = Nat.card κ :=
  let ⟨e, _⟩ := exists_equiv_linearEquiv_of_iSupIndep hP hPt hPind hQ hQt hQind
  Nat.card_eq_of_bijective e e.bijective

/-- **The Krull-Schmidt theorem**, in the `Finset` packaging that
`TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq` produces: two `Finset`s of
indecomposable submodules that are independent with supremum the whole module are matched by a
bijection under which corresponding summands are isomorphic. -/
theorem exists_equiv_linearEquiv_of_finset (hM : IsFiniteLength A M)
    {s t : Finset (Submodule A M)} (hs : ∀ N ∈ s, IsIndecomposableModule A N)
    (hsi : s.SupIndep id) (hst : s.sup id = ⊤) (ht : ∀ N ∈ t, IsIndecomposableModule A N)
    (hti : t.SupIndep id) (htt : t.sup id = ⊤) :
    ∃ e : s ≃ t, ∀ N : s, Nonempty ((N : Submodule A M) ≃ₗ[A] (e N : Submodule A M)) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  refine exists_equiv_linearEquiv_of_iSupIndep (P := fun N : s ↦ (N : Submodule A M))
    (Q := fun N : t ↦ (N : Submodule A M)) hsi.independent ?_ (fun N ↦ hs N N.2)
    hti.independent ?_ (fun N ↦ ht N N.2)
  · simpa only [Finset.sup_eq_iSup, iSup_subtype, id_eq] using hst
  · simpa only [Finset.sup_eq_iSup, iSup_subtype, id_eq] using htt

/-- Two indecomposable decompositions of a module of finite length, in the `Finset` packaging
`TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq` produces, consist of the same number
of summands. -/
theorem card_eq_card_of_finset (hM : IsFiniteLength A M) {s t : Finset (Submodule A M)}
    (hs : ∀ N ∈ s, IsIndecomposableModule A N) (hsi : s.SupIndep id) (hst : s.sup id = ⊤)
    (ht : ∀ N ∈ t, IsIndecomposableModule A N) (hti : t.SupIndep id) (htt : t.sup id = ⊤) :
    s.card = t.card :=
  let ⟨e, _⟩ := exists_equiv_linearEquiv_of_finset hM hs hsi hst ht hti htt
  by simpa only [Fintype.card_coe] using Fintype.card_congr e

end TauCeti
