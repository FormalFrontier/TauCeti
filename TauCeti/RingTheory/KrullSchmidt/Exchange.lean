/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

The argument is the classical one. The endomorphisms of `N` obtained by projecting `N` into `Q i`
and back sum to the identity, because the
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

/-- The components of the identity of `N` along the decomposition `Q`: projecting `N` into the
summand `Q i` and back onto `N` along its complement `S` gives a family of endomorphisms of `N`
summing to the identity, because the projections onto the summands sum to the identity of `M`. -/
private theorem sum_projectionOnto_comp_internalProjection_eq_one {ι : Type w} [Fintype ι]
    {Q : ι → Submodule A M} (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {N S : Submodule A M}
    (hNS : IsCompl N S) :
    ∑ i, ((N.projectionOnto S hNS ∘ₗ (Q i).subtype) ∘ₗ
      (internalProjection hQi hQt i).domRestrict N) = 1 := by
  refine LinearMap.ext fun x ↦ ?_
  have hx : N.projectionOnto S hNS (∑ i, ((internalProjection hQi hQt i (x : M) : M))) = x := by
    rw [sum_coe_internalProjection hQi hQt, Submodule.projectionOnto_apply_left]
  rw [map_sum] at hx
  rw [LinearMap.sum_apply]
  simpa only [LinearMap.comp_apply, LinearMap.domRestrict_apply, Submodule.subtype_apply,
    Module.End.one_apply] using hx

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
  -- Locality of `Module.End A N` picks out an index whose component is invertible.
  obtain ⟨i₀, -, hunit⟩ : ∃ i₀ ∈ Finset.univ, IsUnit ((N.projectionOnto S hNS ∘ₗ (Q i₀).subtype)
      ∘ₗ (internalProjection hQi hQt i₀).domRestrict N) :=
    IsLocalRing.exists_of_isUnit_sum
      (by rw [sum_projectionOnto_comp_internalProjection_eq_one]; exact isUnit_one)
  -- A split injection into the indecomposable `Q i₀` is already an isomorphism.
  have hbij : Function.Bijective ((internalProjection hQi hQt i₀).domRestrict N) :=
    (hQind i₀).bijective_of_bijective_comp (g := N.projectionOnto S hNS ∘ₗ (Q i₀).subtype)
      ((Module.End.isUnit_iff _).mp hunit)
  -- The exchange is the kernel characterisation of injectivity and surjectivity on `N`,
  -- since the remaining summands are exactly the kernel of the `i₀`-projection.
  refine ⟨i₀, ⟨LinearEquiv.ofBijective _ hbij⟩, ?_, ?_⟩
  · rw [← ker_internalProjection hQi hQt i₀]
    exact LinearMap.injective_domRestrict_iff.mp hbij.1
  · rw [← ker_internalProjection hQi hQt i₀]
    exact (LinearMap.surjective_domRestrict_iff
      (internalProjection_surjective hQi hQt i₀)).mp hbij.2

end TauCeti
