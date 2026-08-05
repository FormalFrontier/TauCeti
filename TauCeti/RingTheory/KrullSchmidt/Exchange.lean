/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Projection
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Azumaya's exchange lemma

This file proves the step that drives the uniqueness half of the Krull-Schmidt theorem. Suppose a
module `M` is the internal direct sum of a finite family `Q` of indecomposable submodules, and
suppose `N` is an indecomposable direct summand of `M`. Then `N` is isomorphic to one of the
summands `Q i₀`, and it may be *exchanged* for it: `M` is also the direct sum of `N` and the
remaining summands `⨆ j ≠ i₀, Q j`.

The argument is the classical one. Writing `p` for the projection of `M` onto `N`, the
endomorphisms of `N` obtained by projecting `N` into `Q i` and back sum to the identity, because the
projections `TauCeti.internalProjection` onto the summands do
(`TauCeti.sum_coe_internalProjection`). The hypothesis is that `Module.End A N` is local, and in a
local ring a finite sum can only be a unit if one of its terms is
(`IsLocalRing.exists_of_isUnit_sum`); so one of those endomorphisms is an isomorphism. It factors
through `Q i₀`, and a split injection into an *indecomposable* module is already an isomorphism
(`TauCeti.IsIndecomposableModule.bijective_of_bijective_comp`), so `N ≃ₗ Q i₀`. The exchange is then
read off from the injectivity and surjectivity of that isomorphism. Locality of `Module.End A N` is
what Fitting's lemma `TauCeti.isLocalRing_end_of_isIndecomposable` supplies when `M` has finite
length.

## Main results

* `TauCeti.exists_linearEquiv_and_isCompl_biSup_ne`: **the exchange lemma**.

## Implementation notes

The exchange lemma states the decomposition of `M` as `iSupIndep` together with `⨆ i, Q i = ⊤`
rather than as `DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on the index type
that the statement does not otherwise need; that is also the form the projections of
`TauCeti/LinearAlgebra/Projection.lean` are built from. The lemma asks for `N` to come with an
explicit complement `S`, rather than deducing one, because that is how it is used: `N` is one
summand of a second decomposition of `M`, whose other summands supply `S`.

Of `N` the proof needs only that `Module.End A N` is local, so that is the hypothesis; it already
makes `N` nonzero (`TauCeti.nontrivial_of_isLocalRing_end`) and indecomposable
(`TauCeti.isIndecomposableModule_of_isLocalRing_end`), and indecomposability is never used.

## References

This implements the exchange argument behind the uniqueness bullet of Layer 2 ("the Krull-Schmidt
theorem") of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v w

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-- **Azumaya's exchange lemma.** Let `M` be the internal direct sum of a finite family `Q` of
indecomposable submodules, and let `N` be a direct summand of `M` whose endomorphism ring is local
(so in particular `N` is nonzero). Then `N` is isomorphic to one of the `Q i₀`, and can be exchanged
for it: `N` and the remaining summands `⨆ j ≠ i₀, Q j` are complementary in `M`.

The locality of `Module.End A N` is what Fitting's lemma
`TauCeti.isLocalRing_end_of_isIndecomposable` supplies when `M` has finite length. -/
theorem exists_linearEquiv_and_isCompl_biSup_ne
    {ι : Type w} [Finite ι] {Q : ι → Submodule A M} (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤)
    (hQind : ∀ i, IsIndecomposableModule A (Q i)) {N S : Submodule A M}
    [IsLocalRing (Module.End A N)] (hNS : IsCompl N S) :
    ∃ i₀ : ι, Nonempty (N ≃ₗ[A] Q i₀) ∧ IsCompl N (⨆ j, ⨆ (_ : j ≠ i₀), Q j) := by
  have _ : Fintype ι := Fintype.ofFinite ι
  have _ : Nontrivial N := nontrivial_of_isLocalRing_end (A := A)
  set p : M →ₗ[A] N := N.projectionOnto S hNS with hp
  set f : ι → Module.End A N :=
    fun i ↦ (p ∘ₗ (Q i).subtype) ∘ₗ (internalProjection hQi hQt i ∘ₗ N.subtype) with hf
  -- The components of the identity of `N` along the decomposition `Q`.
  have hsum : ∑ i, f i = 1 := by
    refine LinearMap.ext fun x ↦ ?_
    have hx : p (∑ i, ((internalProjection hQi hQt i (x : M) : M))) = x := by
      rw [sum_coe_internalProjection hQi hQt, hp, Submodule.projectionOnto_apply_left]
    rw [map_sum] at hx
    rw [LinearMap.sum_apply]
    exact hx
  -- Locality of `Module.End A N` picks out an index whose component is invertible.
  obtain ⟨i₀, -, hunit⟩ : ∃ i₀ ∈ Finset.univ, IsUnit (f i₀) :=
    IsLocalRing.exists_of_isUnit_sum (by rw [hsum]; exact isUnit_one)
  set α : N →ₗ[A] Q i₀ := internalProjection hQi hQt i₀ ∘ₗ N.subtype with hα
  have hbij : Function.Bijective α :=
    (hQind i₀).bijective_of_bijective_comp (g := p ∘ₗ (Q i₀).subtype)
      ((Module.End.isUnit_iff _).mp hunit)
  refine ⟨i₀, ⟨LinearEquiv.ofBijective α hbij⟩, ?_⟩
  set T : Submodule A M := ⨆ j, ⨆ (_ : j ≠ i₀), Q j with hT
  -- `T` is exactly what the `i₀`-projection kills.
  have hTker : T = LinearMap.ker (internalProjection hQi hQt i₀) := by
    rw [hT, ker_internalProjection]
  -- Each element of `M` differs from its `i₀`-component by an element of `T`.
  have hrest : ∀ x : M, x - ((internalProjection hQi hQt i₀ x : M)) ∈ T := fun x ↦ by
    rw [hTker, LinearMap.mem_ker, map_sub, internalProjection_apply, sub_self]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxN hxT
    have hzero : α ⟨x, hxN⟩ = 0 := by
      rw [hα, LinearMap.comp_apply, Submodule.subtype_apply, ← LinearMap.mem_ker, ← hTker]
      exact hxT
    have hx0 := hbij.1 (hzero.trans (map_zero α).symm)
    simpa using congrArg Subtype.val hx0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    obtain ⟨n, hn⟩ := hbij.2 (internalProjection hQi hQt i₀ m)
    have hcomp : ((internalProjection hQi hQt i₀ (n : M) : M)) =
        ((internalProjection hQi hQt i₀ m : M)) := by
      rw [← hn, hα, LinearMap.comp_apply, Submodule.subtype_apply]
    have hmem : ((internalProjection hQi hQt i₀ m : M)) ∈ N ⊔ T := by
      rw [← hcomp, ← sub_sub_cancel (n : M) ((internalProjection hQi hQt i₀ (n : M) : M))]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left n.2)
        (Submodule.mem_sup_right (hrest (n : M)))
    rw [← sub_add_cancel m ((internalProjection hQi hQt i₀ m : M))]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (hrest m)) hmem

end TauCeti
