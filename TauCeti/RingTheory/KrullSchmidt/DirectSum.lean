/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KrullSchmidt.Existence
public import TauCeti.RingTheory.KrullSchmidt.Uniqueness

/-!
# The Krull-Schmidt theorem for external direct sums

`TauCeti.exists_indecomposable_decomposition` and
`TauCeti.exists_equiv_linearEquiv_of_iSupIndep` state the two halves of the Krull-Schmidt theorem
for families of *submodules* of one fixed module. A client that starts from an external
decomposition `M ≃ₗ[A] ⨁ i, N i`, with the summands `N i` abstract modules of their own, cannot
apply them without first transporting every summand into the submodule lattice of `M` and rebuilding
the independence data by hand. This file does that transport once and restates both halves against
external direct sums.

## Main results

* `TauCeti.exists_iSupIndep_linearEquiv_of_directSum`: an external decomposition
  `M ≃ₗ[A] ⨁ i, N i` induces an internal one, a family of submodules of `M` that is `iSupIndep`,
  spans `M`, and whose `i`-th member is isomorphic to `N i`. This is the transport the two theorems
  below run on, and it is stated separately because it is what a client needs in order to reach any
  other statement about internal decompositions.
* `TauCeti.exists_linearEquiv_directSum_isIndecomposableModule`: **existence**, externally: an
  Artinian module is isomorphic to a direct sum of indecomposable modules.
* `TauCeti.exists_equiv_linearEquiv_of_directSum`: **the Krull-Schmidt theorem**, externally: two
  decompositions `M ≃ₗ[A] ⨁ i, N i` and `M ≃ₗ[A] ⨁ j, Q j` of a module of finite length into
  indecomposable summands are matched by a bijection `ι ≃ κ` under which corresponding summands are
  isomorphic, with `TauCeti.exists_equiv_linearEquiv_of_directSum_of_isLocalRing_end` in Azumaya's
  generality and `TauCeti.card_eq_card_of_directSum` for the number of summands.
* `TauCeti.exists_equiv_linearEquiv_of_directSumEquiv`: the same for two abstract families of
  summands compared by an isomorphism `(⨁ i, N i) ≃ₗ[A] ⨁ j, Q j`, with no ambient module.

## Implementation notes

The transport goes through `LinearMap.range (DirectSum.lof A ι N i)`, the copy of `N i` inside
`⨁ i, N i`. That these ranges span is Mathlib's `DFinsupp.iSup_range_lsingle`, `DirectSum.lof`
being by definition `DFinsupp.lsingle`; that they are
independent is the one private lemma below, read off the components. Their images under `e.symm`
are the internal decomposition of `M`, independent by `LinearMap.iSupIndep_map`. The transport is
stated existentially rather than as a named family of submodules, so that `DecidableEq ι` — which
`DirectSum.lof` needs but no statement here does — can be produced by `classical` inside the proof
instead of appearing as a hypothesis. This matches the choice made in
`TauCeti/RingTheory/KrullSchmidt/Uniqueness.lean` to spell decompositions as `iSupIndep` together
with `⨆ i, P i = ⊤` rather than as `DirectSum.IsInternal`.

Comparing two abstract families `N` and `Q` directly, with no ambient module, is the case
`M := ⨁ i, N i`, taking the first equivalence to be `LinearEquiv.refl`; that is
`TauCeti.exists_equiv_linearEquiv_of_directSumEquiv`. The statements are given with an ambient `M`
rather than only in that special case because the finiteness hypothesis is then read on the direct
sum itself, which is not where a client holds it.

The transport lemmas need no subtraction, so they are stated for a semimodule over a semiring; the
decomposition theorems are over a ring, which is the generality of the internal statements they
consume.

## References

This supplies the external interface to Layer 2 ("the Krull-Schmidt theorem") of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose uniqueness bullet asks
for the theorem to be proved "at the module level with submodules and linear equivalences", then
transported.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

open DirectSum

universe u v w x y z

/-! ### An external decomposition induces an internal one -/

section Transport

variable {A : Type u} [Semiring A] {M : Type v} [AddCommMonoid M] [Module A M]
variable {ι : Type w} {N : ι → Type y} [∀ i, AddCommMonoid (N i)] [∀ i, Module A (N i)]

/-- The copies of the summands inside an external direct sum are independent: an element of the
`i`-th copy meeting the span of the others has vanishing `i`-th component. -/
private theorem iSupIndep_range_lof [DecidableEq ι] :
    iSupIndep fun i ↦ LinearMap.range (lof A ι N i) := by
  intro i
  rw [Submodule.disjoint_def]
  rintro x ⟨b, rfl⟩ hx
  have hle : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (lof A ι N j)) ≤
      LinearMap.ker (component A ι N i) := by
    refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
    rw [LinearMap.range_le_ker_iff]
    simp [component_comp_lof, hj]
  have hb : b = 0 := by simpa using hle hx
  rw [hb, map_zero]

/-- **An external direct-sum decomposition induces an internal one.** An isomorphism
`M ≃ₗ[A] ⨁ i, N i` carries the copies of the summands to a family of submodules of `M` that is
independent, spans `M`, and reproduces the `N i` up to isomorphism.

This is the transport that lets the internal statements of the Krull-Schmidt theorem be applied to
an external decomposition; `TauCeti.exists_equiv_linearEquiv_of_directSum` is that application. -/
theorem exists_iSupIndep_linearEquiv_of_directSum (e : M ≃ₗ[A] ⨁ i, N i) :
    ∃ P : ι → Submodule A M, iSupIndep P ∧ ⨆ i, P i = ⊤ ∧ ∀ i, Nonempty (N i ≃ₗ[A] P i) := by
  classical
  refine ⟨fun i ↦ (LinearMap.range (lof A ι N i)).map (e.symm : (⨁ i, N i) →ₗ[A] M), ?_, ?_,
    fun i ↦ ⟨?_⟩⟩
  · exact LinearMap.iSupIndep_map _ e.symm.injective iSupIndep_range_lof
  · -- `DirectSum.lof` is by definition `DFinsupp.lsingle`, but `rw` does not unfold it, so
    -- Mathlib's spanning statement is transferred by ascription rather than rewritten in place.
    have htop : ⨆ i, LinearMap.range (lof A ι N i) = ⊤ := DFinsupp.iSup_range_lsingle
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.symm.surjective
  · exact (LinearEquiv.ofInjective (lof A ι N i) DFinsupp.single_injective).trans
      (Submodule.equivMapOfInjective _ e.symm.injective _)

end Transport

/-! ### The two halves of the Krull-Schmidt theorem, externally -/

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

/-- **Existence of an indecomposable decomposition**, externally: an Artinian module — in
particular one of finite length — is isomorphic to the direct sum of a finite family of
indecomposable modules.

The summands are produced as submodules of `M`, by
`TauCeti.exists_isInternal_isIndecomposableModule`; the point of this form is that the conclusion
is a linear equivalence with a direct sum, which is what
`TauCeti.exists_equiv_linearEquiv_of_directSum` consumes. -/
theorem exists_linearEquiv_directSum_isIndecomposableModule [IsArtinian A M] :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      Nonempty (M ≃ₗ[A] ⨁ N : s, (N : Submodule A M)) := by
  obtain ⟨s, hs, hsi⟩ := exists_isInternal_isIndecomposableModule (A := A) (M := M)
  exact ⟨s, hs, ⟨(LinearEquiv.ofBijective (coeLinearMap fun N : s ↦ (N : Submodule A M)) hsi).symm⟩⟩

variable {ι : Type w} {κ : Type x} [Finite ι] [Finite κ]
variable {N : ι → Type y} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
variable {Q : κ → Type z} [∀ j, AddCommGroup (Q j)] [∀ j, Module A (Q j)]

/-- **The Krull-Schmidt theorem for external direct sums**, in Azumaya's generality: if a module is
isomorphic to a finite direct sum of modules with local endomorphism rings, and also to a finite
direct sum of indecomposable modules, then the two families are matched by a bijection of their
index sets under which corresponding summands are isomorphic.

No finiteness hypothesis on `M` is needed; for a module of finite length Fitting's lemma supplies
the locality hypothesis, which is `TauCeti.exists_equiv_linearEquiv_of_directSum` below. -/
theorem exists_equiv_linearEquiv_of_directSum_of_isLocalRing_end
    (eN : M ≃ₗ[A] ⨁ i, N i) (eQ : M ≃ₗ[A] ⨁ j, Q j)
    (hN : ∀ i, IsLocalRing (Module.End A (N i)))
    (hQ : ∀ j, IsIndecomposableModule A (Q j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[A] Q (e i)) := by
  obtain ⟨P, hPi, hPt, hPe⟩ := exists_iSupIndep_linearEquiv_of_directSum eN
  obtain ⟨R, hRi, hRt, hRe⟩ := exists_iSupIndep_linearEquiv_of_directSum eQ
  obtain ⟨e, he⟩ := exists_equiv_linearEquiv_of_isLocalRing_end hPi hPt
    (fun i ↦ have := hN i; IsLocalRing.of_ringEquiv (hPe i).some.conjRingEquiv) hRi hRt
    (fun j ↦ (hQ j).of_linearEquiv (hRe j).some)
  exact ⟨e, fun i ↦ ⟨(hPe i).some ≪≫ₗ (he i).some ≪≫ₗ (hRe (e i)).some.symm⟩⟩

/-- **The Krull-Schmidt theorem for two abstract families of summands**: a direct sum of modules
with local endomorphism rings that is isomorphic to a direct sum of indecomposable modules has its
summands matched by a bijection of the index sets.

This is `TauCeti.exists_equiv_linearEquiv_of_directSum_of_isLocalRing_end` with the ambient module
taken to be the first direct sum; it is the form to use when no ambient module is in play. -/
theorem exists_equiv_linearEquiv_of_directSumEquiv (e : (⨁ i, N i) ≃ₗ[A] ⨁ j, Q j)
    (hN : ∀ i, IsLocalRing (Module.End A (N i)))
    (hQ : ∀ j, IsIndecomposableModule A (Q j)) :
    ∃ f : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[A] Q (f i)) :=
  exists_equiv_linearEquiv_of_directSum_of_isLocalRing_end (LinearEquiv.refl A _) e hN hQ

/-- **The Krull-Schmidt theorem for external direct sums.** Two decompositions of a module of finite
length as a direct sum of indecomposable modules are matched by a bijection of their index sets
under which corresponding summands are isomorphic.

`TauCeti.exists_linearEquiv_directSum_isIndecomposableModule` supplies such a decomposition, and
`TauCeti.exists_equiv_linearEquiv_of_iSupIndep` is the same statement for families of submodules of
`M`. -/
theorem exists_equiv_linearEquiv_of_directSum [IsNoetherian A M] [IsArtinian A M]
    (eN : M ≃ₗ[A] ⨁ i, N i) (eQ : M ≃ₗ[A] ⨁ j, Q j)
    (hN : ∀ i, IsIndecomposableModule A (N i))
    (hQ : ∀ j, IsIndecomposableModule A (Q j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[A] Q (e i)) := by
  -- Each summand is isomorphic to a submodule of `M`, hence of finite length, so Fitting's lemma
  -- makes its endomorphism ring local.
  obtain ⟨P, -, -, hPe⟩ := exists_iSupIndep_linearEquiv_of_directSum eN
  refine exists_equiv_linearEquiv_of_directSum_of_isLocalRing_end eN eQ (fun i ↦ ?_) hQ
  have e := (hPe i).some.symm
  exact isLocalRing_end_of_isIndecomposable
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_linearEquiv e, isArtinian_of_linearEquiv e⟩) (hN i)

/-- Two decompositions of a module of finite length as a direct sum of indecomposable modules have
the same number of summands. -/
theorem card_eq_card_of_directSum [IsNoetherian A M] [IsArtinian A M]
    (eN : M ≃ₗ[A] ⨁ i, N i) (eQ : M ≃ₗ[A] ⨁ j, Q j)
    (hN : ∀ i, IsIndecomposableModule A (N i))
    (hQ : ∀ j, IsIndecomposableModule A (Q j)) : Nat.card ι = Nat.card κ :=
  let ⟨e, _⟩ := exists_equiv_linearEquiv_of_directSum eN eQ hN hQ
  Nat.card_eq_of_bijective e e.bijective

end TauCeti
