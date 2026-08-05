/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.RingTheory.KrullSchmidt.Existence

/-!
# Azumaya's exchange lemma

This file proves the step that drives the uniqueness half of the Krull-Schmidt theorem. Suppose a
module `M` is the internal direct sum of a finite family `Q` of indecomposable submodules, and
suppose `N` is an indecomposable direct summand of `M`. Then `N` is isomorphic to one of the
summands `Q i₀`, and it may be *exchanged* for it: `M` is also the direct sum of `N` and the
remaining summands `⨆ j ≠ i₀, Q j`.

The argument is the classical one. Writing `p` for the projection of `M` onto `N`, the
endomorphisms of `N` obtained by projecting `N` into `Q i` and back sum to the identity. Fitting's
lemma makes `Module.End A N` local (`TauCeti.isLocalRing_end_of_isIndecomposable`), and in a local
ring a finite sum can only be a unit if one of its terms is
(`IsLocalRing.exists_of_isUnit_sum`); so one of those endomorphisms is an
isomorphism. It factors through `Q i₀`, and a split injection into an *indecomposable* module is
already an isomorphism, so `N ≃ₗ Q i₀`. The exchange is then read off from the injectivity and
surjectivity of that isomorphism.

## Main definitions

* `TauCeti.internalProjection`: the projection of `M` onto one summand of an internal direct sum
  decomposition, as a linear map `M →ₗ[A] Q i`.

## Main results

* `TauCeti.IsIndecomposableModule.bijective_of_bijective_comp`: if `g ∘ₗ f` is bijective and the
  module `f` lands in is indecomposable, then `f` is bijective.
* `TauCeti.exists_linearEquiv_and_isCompl_biSup_ne`: **the exchange lemma**.

## Implementation notes

The projections `TauCeti.internalProjection` are built from Mathlib's linear equivalence
`LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h`, so that Mathlib's evaluation lemmas
`DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem` and `_of_mem_ne` apply on the nose; the one
fact added here is that they sum to the identity over a finite index type.

The exchange lemma states the decomposition of `M` as `iSupIndep` together with `⨆ i, Q i = ⊤`
rather than as `DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on the index type
that the statement does not otherwise need; the two are interchanged inside the proof by
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`. It asks for `N` to come with an
explicit complement `S`, rather than deducing one, because that is how it is used: `N` is one
summand of a second decomposition of `M`, whose other summands supply `S`.

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

/-! ### Splitting off an indecomposable module -/

/-- **A split injection into an indecomposable module is an isomorphism.** If `g ∘ₗ f` is bijective
then `f ∘ₗ (g ∘ₗ f)⁻¹ ∘ₗ g` is an idempotent endomorphism of the indecomposable module `f` lands
in, hence is `0` or `1`; it cannot be `0`, because that would force `f` to vanish on a nontrivial
module, so it is the identity and `f` is surjective. -/
theorem IsIndecomposableModule.bijective_of_bijective_comp {N P : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] [Nontrivial N]
    (hP : IsIndecomposableModule A P) {f : N →ₗ[A] P} {g : P →ₗ[A] N}
    (h : Function.Bijective (g ∘ₗ f)) : Function.Bijective f := by
  set u : N ≃ₗ[A] N := LinearEquiv.ofBijective (g ∘ₗ f) h with hu
  have hgf : ∀ x : N, u.symm (g (f x)) = x := fun x ↦ u.symm_apply_apply x
  set e : Module.End A P := f ∘ₗ (u.symm : N →ₗ[A] N) ∘ₗ g with he
  have hidem : IsIdempotentElem e := by
    ext x
    simp only [he, Module.End.mul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    rw [hgf]
  have hinjf : Function.Injective f := fun x y hxy ↦ h.1 (by
    simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  rcases hP.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · exfalso
    have hzero : ∀ x : N, f x = 0 := fun x ↦ by
      have hx := congrArg (fun t : Module.End A P ↦ t (f x)) h0
      simpa [he, hgf] using hx
    obtain ⟨x, y, hxy⟩ := exists_pair_ne N
    exact hxy (hinjf (by rw [hzero x, hzero y]))
  · refine ⟨hinjf, fun y ↦ ⟨u.symm (g y), ?_⟩⟩
    have hy := congrArg (fun t : Module.End A P ↦ t y) h1
    simpa [he] using hy

/-! ### The projections attached to an internal direct sum -/

section Projection

variable {ι : Type w} [DecidableEq ι] {Q : ι → Submodule A M}

/-- The projection of `M` onto the summand `Q i` of an internal direct sum decomposition. -/
noncomputable def internalProjection (h : DirectSum.IsInternal Q) (i : ι) : M →ₗ[A] Q i :=
  (DirectSum.component A ι (fun j ↦ (Q j : Type v)) i).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h).symm.toLinearMap

/-- The projection onto `Q i` fixes the elements of `Q i`. -/
theorem internalProjection_of_mem (h : DirectSum.IsInternal Q) {i : ι} {x : M} (hx : x ∈ Q i) :
    internalProjection h i x = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_of_mem hx

/-- The projection onto `Q j` kills the elements of any other summand `Q i`. -/
theorem internalProjection_eq_zero_of_mem_of_ne (h : DirectSum.IsInternal Q) {i j : ι}
    (hij : i ≠ j) {x : M} (hx : x ∈ Q i) : internalProjection h j x = 0 :=
  h.ofBijective_coeLinearMap_of_mem_ne hij hx

/-- Over a finite index type the projections onto the summands sum to the identity. -/
theorem sum_coe_internalProjection [Fintype ι] (h : DirectSum.IsInternal Q) (x : M) :
    ∑ i, ((internalProjection h i x : M)) = x := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h with he
  have hsum := congrArg (DirectSum.coeLinearMap Q)
    (DirectSum.sum_univ_of (β := fun j ↦ (Q j : Type v)) (e.symm x))
  rw [map_sum] at hsum
  simp only [DirectSum.coeLinearMap_of] at hsum
  rw [show (DirectSum.coeLinearMap Q) (e.symm x) = e (e.symm x) from rfl,
    e.apply_symm_apply] at hsum
  exact hsum

end Projection

/-! ### The exchange lemma -/

/-- **Azumaya's exchange lemma.** Let `M` be the internal direct sum of a finite family `Q` of
indecomposable submodules, and let `N` be an indecomposable direct summand of `M`. Then `N` is
isomorphic to one of the `Q i₀`, and can be exchanged for it: `N` and the remaining summands
`⨆ j ≠ i₀, Q j` are complementary in `M`.

The finiteness hypotheses on `M` are what makes `Module.End A N` local, by Fitting's lemma. -/
theorem exists_linearEquiv_and_isCompl_biSup_ne [IsNoetherian A M] [IsArtinian A M]
    {ι : Type w} [Finite ι] {Q : ι → Submodule A M} (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤)
    (hQind : ∀ i, IsIndecomposableModule A (Q i)) {N S : Submodule A M} (hNS : IsCompl N S)
    (hN : IsIndecomposableModule A N) :
    ∃ i₀ : ι, Nonempty (N ≃ₗ[A] Q i₀) ∧ IsCompl N (⨆ j, ⨆ (_ : j ≠ i₀), Q j) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have hQ : DirectSum.IsInternal Q :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hQi hQt
  have hNtriv := hN.nontrivial
  have hloc : IsLocalRing (Module.End A N) :=
    isLocalRing_end_of_isIndecomposable
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) hN
  set p : M →ₗ[A] N := N.projectionOnto S hNS with hp
  set f : ι → Module.End A N :=
    fun i ↦ (p ∘ₗ (Q i).subtype) ∘ₗ (internalProjection hQ i ∘ₗ N.subtype) with hf
  -- The components of the identity of `N` along the decomposition `Q`.
  have hsum : ∑ i, f i = 1 := by
    refine LinearMap.ext fun x ↦ ?_
    have hx : p (∑ i, ((internalProjection hQ i (x : M) : M))) = x := by
      rw [sum_coe_internalProjection hQ, hp, Submodule.projectionOnto_apply_left]
    rw [map_sum] at hx
    rw [LinearMap.sum_apply]
    exact hx
  -- Locality of `Module.End A N` picks out an index whose component is invertible.
  obtain ⟨i₀, -, hunit⟩ : ∃ i₀ ∈ Finset.univ, IsUnit (f i₀) :=
    IsLocalRing.exists_of_isUnit_sum (by rw [hsum]; exact isUnit_one)
  set α : N →ₗ[A] Q i₀ := internalProjection hQ i₀ ∘ₗ N.subtype with hα
  have hbij : Function.Bijective α :=
    (hQind i₀).bijective_of_bijective_comp (g := p ∘ₗ (Q i₀).subtype)
      ((Module.End.isUnit_iff _).mp hunit)
  refine ⟨i₀, ⟨LinearEquiv.ofBijective α hbij⟩, ?_⟩
  set T : Submodule A M := ⨆ j, ⨆ (_ : j ≠ i₀), Q j with hT
  -- Everything outside the `i₀`-summand is killed by the `i₀`-projection.
  have hTker : T ≤ LinearMap.ker (internalProjection hQ i₀) :=
    iSup₂_le fun j hj _ hx ↦ internalProjection_eq_zero_of_mem_of_ne hQ hj hx
  -- Each element of `M` differs from its `i₀`-component by an element of `T`.
  have hrest : ∀ x : M, x - ((internalProjection hQ i₀ x : M)) ∈ T := by
    intro x
    have hsplit : ((internalProjection hQ i₀ x : M)) + ∑ i ∈ Finset.univ.erase i₀,
        ((internalProjection hQ i x : M)) = x :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).trans (sum_coe_internalProjection hQ x)
    rw [sub_eq_of_eq_add' hsplit.symm]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    exact (le_iSup₂ (f := fun j (_ : j ≠ i₀) ↦ Q j) i (Finset.ne_of_mem_erase hi))
      (internalProjection hQ i x).2
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxN hxT
    have hzero : α ⟨x, hxN⟩ = 0 := LinearMap.mem_ker.mp (hTker hxT)
    have hx0 := hbij.1 (hzero.trans (map_zero α).symm)
    simpa using congrArg Subtype.val hx0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    obtain ⟨n, hn⟩ := hbij.2 (internalProjection hQ i₀ m)
    have hcomp : ((internalProjection hQ i₀ (n : M) : M)) = ((internalProjection hQ i₀ m : M)) := by
      rw [← hn]; rfl
    have hmem : ((internalProjection hQ i₀ m : M)) ∈ N ⊔ T := by
      rw [← hcomp, ← sub_sub_cancel (n : M) ((internalProjection hQ i₀ (n : M) : M))]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left n.2)
        (Submodule.mem_sup_right (hrest (n : M)))
    rw [← sub_add_cancel m ((internalProjection hQ i₀ m : M))]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (hrest m)) hmem

end TauCeti
