/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Azumaya's exchange lemma

This file proves the step that drives the uniqueness half of the Krull-Schmidt theorem. Suppose a
module `M` is the internal direct sum of a finite family `Q` of indecomposable submodules, and
suppose `N` is an indecomposable direct summand of `M`. Then `N` is isomorphic to one of the
summands `Q i₀`, and it may be *exchanged* for it: `M` is also the direct sum of `N` and the
remaining summands `⨆ j ≠ i₀, Q j`.

The argument is the classical one. Writing `p` for the projection of `M` onto `N`, the
endomorphisms of `N` obtained by projecting `N` into `Q i` and back sum to the identity. The
hypothesis is that `Module.End A N` is local, and in a local ring a finite sum can only be a unit
if one of its terms is (`IsLocalRing.exists_of_isUnit_sum`); so one of those endomorphisms is an
isomorphism. It factors through `Q i₀`, and a split injection into an *indecomposable* module is
already an isomorphism, so `N ≃ₗ Q i₀`. The exchange is then read off from the injectivity and
surjectivity of that isomorphism. Locality of `Module.End A N` is what Fitting's lemma
`TauCeti.isLocalRing_end_of_isIndecomposable` supplies when `M` has finite length.

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
`DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem` and `_of_mem_ne` apply on the nose; the facts
added here are that they sum to the identity over a finite index type, that each is surjective, and
that the kernel of the `i`-th one is the supremum of the other summands.

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

/-- The projection onto `Q i` restricts to the identity on `Q i`. -/
@[simp]
theorem internalProjection_coe (h : DirectSum.IsInternal Q) {i : ι} (x : Q i) :
    internalProjection h i (x : M) = x :=
  Subtype.ext (congrArg Subtype.val (internalProjection_of_mem h x.2))

/-- The projection onto `Q j` restricts to `0` on any other summand `Q i`. -/
@[simp]
theorem internalProjection_coe_of_ne (h : DirectSum.IsInternal Q) {i j : ι} (hij : i ≠ j)
    (x : Q i) : internalProjection h j (x : M) = 0 :=
  internalProjection_eq_zero_of_mem_of_ne h hij x.2

/-- The projection onto `Q i` is surjective, since it restricts to the identity on `Q i`. -/
theorem internalProjection_surjective (h : DirectSum.IsInternal Q) (i : ι) :
    Function.Surjective (internalProjection h i) :=
  fun x ↦ ⟨(x : M), internalProjection_coe h x⟩

/-- The projection onto `Q i` is surjective, stated for its range. -/
@[simp]
theorem range_internalProjection (h : DirectSum.IsInternal Q) (i : ι) :
    LinearMap.range (internalProjection h i) = ⊤ :=
  LinearMap.range_eq_top.mpr (internalProjection_surjective h i)

/-- Over a finite index type the projections onto the summands sum to the identity. -/
theorem sum_coe_internalProjection [Fintype ι] (h : DirectSum.IsInternal Q) (x : M) :
    ∑ i, ((internalProjection h i x : M)) = x := by
  have hcoe : (DirectSum.coeLinearMap Q)
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h).symm x) = x :=
    LinearEquiv.apply_ofBijective_symm_apply (DirectSum.coeLinearMap Q) (h := h) x
  have hsum := congrArg (DirectSum.coeLinearMap Q)
    (DirectSum.sum_univ_of (β := fun j ↦ (Q j : Type v))
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) h).symm x))
  rw [map_sum, hcoe] at hsum
  simp only [DirectSum.coeLinearMap_of] at hsum
  exact hsum

/-- The kernel of the projection onto `Q i` is the supremum of the other summands. -/
theorem ker_internalProjection [Finite ι] (h : DirectSum.IsInternal Q) (i : ι) :
    LinearMap.ker (internalProjection h i) = ⨆ j, ⨆ (_ : j ≠ i), Q j := by
  have _ : Fintype ι := Fintype.ofFinite ι
  refine le_antisymm (fun x hx ↦ ?_) (iSup₂_le fun j hj _ hy ↦
    internalProjection_eq_zero_of_mem_of_ne h hj hy)
  have hx0 : ((internalProjection h i x : M)) = 0 := by simp [LinearMap.mem_ker.mp hx]
  have hxsum : ((internalProjection h i x : M)) + ∑ j ∈ Finset.univ.erase i,
      ((internalProjection h j x : M)) = x :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).trans (sum_coe_internalProjection h x)
  rw [hx0, zero_add] at hxsum
  have hmem : (∑ j ∈ Finset.univ.erase i, ((internalProjection h j x : M))) ∈
      ⨆ j, ⨆ (_ : j ≠ i), Q j :=
    Submodule.sum_mem _ fun j hj ↦
      (le_iSup₂ (f := fun k (_ : k ≠ i) ↦ Q k) j (Finset.ne_of_mem_erase hj))
        (internalProjection h j x).2
  rwa [hxsum] at hmem

end Projection

/-! ### The exchange lemma -/

/-- **Azumaya's exchange lemma.** Let `M` be the internal direct sum of a finite family `Q` of
indecomposable submodules, and let `N` be an indecomposable direct summand of `M`. Then `N` is
isomorphic to one of the `Q i₀`, and can be exchanged for it: `N` and the remaining summands
`⨆ j ≠ i₀, Q j` are complementary in `M`.

The locality of `Module.End A N` is what Fitting's lemma
`TauCeti.isLocalRing_end_of_isIndecomposable` supplies when `M` has finite length. -/
theorem exists_linearEquiv_and_isCompl_biSup_ne
    {ι : Type w} [Finite ι] {Q : ι → Submodule A M} (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤)
    (hQind : ∀ i, IsIndecomposableModule A (Q i)) {N S : Submodule A M}
    [IsLocalRing (Module.End A N)] (hNS : IsCompl N S)
    (hN : IsIndecomposableModule A N) :
    ∃ i₀ : ι, Nonempty (N ≃ₗ[A] Q i₀) ∧ IsCompl N (⨆ j, ⨆ (_ : j ≠ i₀), Q j) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have hQ : DirectSum.IsInternal Q :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hQi hQt
  have hNtriv := hN.nontrivial
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
  -- `T` is exactly what the `i₀`-projection kills.
  have hTker : T = LinearMap.ker (internalProjection hQ i₀) := by
    rw [hT, ker_internalProjection]
  -- Each element of `M` differs from its `i₀`-component by an element of `T`.
  have hrest : ∀ x : M, x - ((internalProjection hQ i₀ x : M)) ∈ T := fun x ↦ by
    rw [hTker, LinearMap.mem_ker, map_sub, internalProjection_coe, sub_self]
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
    obtain ⟨n, hn⟩ := hbij.2 (internalProjection hQ i₀ m)
    have hcomp : ((internalProjection hQ i₀ (n : M) : M)) = ((internalProjection hQ i₀ m : M)) := by
      rw [← hn, hα, LinearMap.comp_apply, Submodule.subtype_apply]
    have hmem : ((internalProjection hQ i₀ m : M)) ∈ N ⊔ T := by
      rw [← hcomp, ← sub_sub_cancel (n : M) ((internalProjection hQ i₀ (n : M) : M))]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left n.2)
        (Submodule.mem_sup_right (hrest (n : M)))
    rw [← sub_add_cancel m ((internalProjection hQ i₀ m : M))]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (hrest m)) hmem

end TauCeti
