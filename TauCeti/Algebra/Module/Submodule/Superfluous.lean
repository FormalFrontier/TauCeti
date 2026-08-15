/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.Radical
public import Mathlib.RingTheory.Jacobson.Radical
public import TauCeti.RingTheory.Jacobson.Module

/-!
# Superfluous submodules

A submodule `N` of `M` is **superfluous** (also called *small*) when it is dispensable for
generating `M`: whenever `N ⊔ K = ⊤` for a submodule `K`, already `K = ⊤`. Superfluous submodules
are the dual notion to essential submodules, and an epimorphism `P ↠ M` is a projective cover
exactly when `P` is projective and its kernel is superfluous in `P`.

Mathlib has neither this predicate nor projective covers. This file supplies the predicate with
its lattice API and identifies it, on the modules where the comparison is available, with being
contained in the radical `Module.jacobson`.

## Main definitions

* `TauCeti.IsSuperfluous`: `N ⊔ K = ⊤` forces `K = ⊤`.

## Main results

* `TauCeti.isSuperfluous_iff`: the definition, restated so that superfluity can be proved
  downstream.
* `TauCeti.isSuperfluous_bot`, `TauCeti.IsSuperfluous.mono`, `TauCeti.isSuperfluous_sup_iff`: the
  superfluous submodules of `M` are closed downwards and under binary suprema, and contain `⊥`.
* `TauCeti.isSuperfluous_top_iff`: `⊤` is superfluous exactly for the zero module.
* `TauCeti.IsSuperfluous.map`: the image of a superfluous submodule under any linear map is
  superfluous; `TauCeti.isSuperfluous_map_equiv_iff` records that along an equivalence this is an
  equivalence.
* `TauCeti.IsSuperfluous.comap`: the preimage of a superfluous submodule under a surjection whose
  kernel is superfluous is again superfluous. This is what makes projective covers compose.
* `TauCeti.IsSuperfluous.surjective_of_surjective_comp` and
  `TauCeti.isSuperfluous_ker_iff_forall_surjective`: a surjection has superfluous kernel exactly
  when it is an *essential epimorphism*, that is, when every map into its source whose composite
  with it is onto is itself onto. This is the minimality that makes a projective cover a
  projective cover. Both directions need differences, so they are stated for modules over a
  semiring that are additive groups.
* `TauCeti.IsSuperfluous.le_coatom` and `TauCeti.IsSuperfluous.le_jacobson`: a superfluous
  submodule lies in every coatom, hence in the radical `Module.jacobson R M`.
* `TauCeti.isSuperfluous_iff_le_jacobson`: over a module whose submodule lattice is coatomic — in
  particular over a finitely generated module — the converse holds, so the superfluous submodules
  are exactly the submodules of the radical, and
  `TauCeti.isSuperfluous_jacobson` records that the radical itself is then superfluous.

## References

This is the superfluous-kernel vocabulary behind the projective-cover bullet of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose statement of it is
"a projective `P` with an essential epimorphism `P ↠ M` (superfluous kernel)".

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4, and T. Y. Lam, *A First Course in Noncommutative Rings*, §24.
-/

public section

namespace TauCeti

universe u v w

section Semiring

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- A submodule `N` of `M` is **superfluous** (or *small*) when it is dispensable for generating
`M`: any submodule `K` with `N ⊔ K = ⊤` is already `⊤`. -/
def IsSuperfluous (N : Submodule R M) : Prop :=
  ∀ K : Submodule R M, N ⊔ K = ⊤ → K = ⊤

/-- Superfluity, restated: this is the introduction rule for `TauCeti.IsSuperfluous`, whose body is
not exposed outside this module. -/
theorem isSuperfluous_iff {N : Submodule R M} :
    IsSuperfluous N ↔ ∀ K : Submodule R M, N ⊔ K = ⊤ → K = ⊤ :=
  (Iff.rfl)

/-- The defining property of a superfluous submodule, in the shape it is consumed in. -/
theorem IsSuperfluous.eq_top_of_sup_eq_top {N K : Submodule R M} (hN : IsSuperfluous N)
    (h : N ⊔ K = ⊤) : K = ⊤ :=
  hN K h

/-- The zero submodule is superfluous. -/
@[simp]
theorem isSuperfluous_bot : IsSuperfluous (⊥ : Submodule R M) := by
  intro K hK
  simpa using hK

/-- A submodule of a superfluous submodule is superfluous. -/
theorem IsSuperfluous.mono {N N' : Submodule R M} (hN' : IsSuperfluous N') (h : N ≤ N') :
    IsSuperfluous N := by
  intro K hK
  refine hN'.eq_top_of_sup_eq_top (top_le_iff.mp ?_)
  rw [← hK]
  exact sup_le_sup_right h K

/-- The supremum of two superfluous submodules is superfluous. -/
theorem IsSuperfluous.sup {N N' : Submodule R M} (hN : IsSuperfluous N) (hN' : IsSuperfluous N') :
    IsSuperfluous (N ⊔ N') := by
  intro K hK
  refine hN'.eq_top_of_sup_eq_top (hN.eq_top_of_sup_eq_top ?_)
  rwa [← sup_assoc]

/-- A supremum of two submodules is superfluous exactly when both of them are. -/
@[simp]
theorem isSuperfluous_sup_iff {N N' : Submodule R M} :
    IsSuperfluous (N ⊔ N') ↔ IsSuperfluous N ∧ IsSuperfluous N' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

/-- The whole module is superfluous in itself exactly when it is zero: superfluity of `⊤` says
precisely that `⊥ = ⊤`. -/
@[simp]
theorem isSuperfluous_top_iff : IsSuperfluous (⊤ : Submodule R M) ↔ Subsingleton M := by
  refine ⟨fun h => (Submodule.subsingleton_iff R).mp (subsingleton_iff_bot_eq_top.mp ?_),
    fun _ K _ => Subsingleton.elim K ⊤⟩
  exact h.eq_top_of_sup_eq_top (by simp)

/-- The whole module is not superfluous in a nonzero module. -/
theorem not_isSuperfluous_top [Nontrivial M] : ¬ IsSuperfluous (⊤ : Submodule R M) := fun h =>
  not_subsingleton M (isSuperfluous_top_iff.mp h)

/-- A superfluous submodule of a nonzero module is proper. -/
theorem IsSuperfluous.ne_top [Nontrivial M] {N : Submodule R M} (hN : IsSuperfluous N) : N ≠ ⊤ := by
  rintro rfl
  exact not_isSuperfluous_top hN

/-- Transport along a linear equivalence both preserves and reflects superfluity. -/
@[simp]
theorem isSuperfluous_map_equiv_iff {N : Submodule R M} (e : M ≃ₗ[R] M₂) :
    IsSuperfluous (N.map (e : M →ₗ[R] M₂)) ↔ IsSuperfluous N := by
  -- Superfluity mentions only `⊔` and `⊤`, both of which `e` preserves and reflects.
  have key : ∀ K : Submodule R M,
      N.map (e : M →ₗ[R] M₂) ⊔ K.map (e : M →ₗ[R] M₂) = ⊤ ↔ N ⊔ K = ⊤ := fun K => by
    rw [← Submodule.map_sup, Submodule.map_eq_top_iff]
  refine ⟨fun h K hK => Submodule.map_eq_top_iff.mp (h _ ((key K).mpr hK)), fun h K hK => ?_⟩
  have hcomap : K.comap (e : M →ₗ[R] M₂) = ⊤ := by
    refine h _ ((key _).mp ?_)
    rwa [Submodule.map_comap_eq_of_surjective e.surjective]
  rw [← Submodule.map_comap_eq_of_surjective e.surjective K, hcomap]
  exact Submodule.map_eq_top_iff.mpr rfl

/-- A superfluous submodule is contained in every maximal submodule. -/
theorem IsSuperfluous.le_coatom {N m : Submodule R M} (hN : IsSuperfluous N) (hm : IsCoatom m) :
    N ≤ m := by
  by_contra hle
  -- Otherwise `N ⊔ m` strictly exceeds the coatom `m`, so is `⊤`, forcing `m = ⊤`.
  have hlt : m < N ⊔ m := by
    refine lt_of_le_of_ne le_sup_right fun heq => hle ?_
    rw [heq]
    exact le_sup_left
  exact hm.1 (hN.eq_top_of_sup_eq_top (hm.2 _ hlt))

end Semiring

section AddCommGroup

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

/-- The image of a superfluous submodule under a linear map is superfluous. -/
theorem IsSuperfluous.map {N : Submodule R M} (hN : IsSuperfluous N) (f : M →ₗ[R] M₂) :
    IsSuperfluous (N.map f) := by
  intro K hK
  -- Pulling `K` back gives a complement of `N` upstairs, so the preimage of `K` is everything.
  have hsup : Submodule.map f (N ⊔ K.comap f) ⊔ K = ⊤ := by
    rw [eq_top_iff, ← hK]
    exact sup_le_sup_right (Submodule.map_mono le_sup_left) K
  have hcomap : N ⊔ K.comap f = ⊤ := by
    rw [← Submodule.comap_map_sup_of_comap_le (f := f) (q := K) le_sup_right, hsup,
      Submodule.comap_top]
  have hcomapK : K.comap f = ⊤ := hN.eq_top_of_sup_eq_top hcomap
  -- Hence `K` already contains the image of `N`, and absorbs it in `hK`.
  have hle : N.map f ≤ K := Submodule.map_le_iff_le_comap.mpr (by rw [hcomapK]; exact le_top)
  rw [← hK]
  exact (sup_eq_right.mpr hle).symm

/-- The preimage of a superfluous submodule under a surjection whose kernel is itself superfluous
is superfluous. This is what makes projective covers compose. -/
theorem IsSuperfluous.comap {K : Submodule R M₂} (hK : IsSuperfluous K) {f : M →ₗ[R] M₂}
    (hf : Function.Surjective f) (hker : IsSuperfluous (LinearMap.ker f)) :
    IsSuperfluous (K.comap f) := by
  intro L hL
  -- Pushing the complement `L` forward makes it a complement of `K` downstairs, ...
  have hmapL : L.map f = ⊤ := by
    refine hK.eq_top_of_sup_eq_top ?_
    rw [← Submodule.map_comap_eq_of_surjective hf K, ← Submodule.map_sup, hL, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  -- ... and pulling that equality back costs exactly the kernel.
  exact hker.eq_top_of_sup_eq_top
    (by rw [sup_comm, ← Submodule.comap_map_eq, hmapL, Submodule.comap_top])

/-- **A superfluous kernel is a minimality condition.** If `f : M →ₗ[R] M₂` has superfluous kernel
and `h : M₃ →ₗ[R] M` is such that `f ∘ₗ h` is onto, then `h` is already onto.

This is what makes a projective cover minimal; it is `TauCeti.IsProjectiveCover`'s workhorse, and
uses nothing about `f` beyond its kernel. -/
theorem IsSuperfluous.surjective_of_surjective_comp {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
    {f : M →ₗ[R] M₂} (hf : IsSuperfluous (LinearMap.ker f)) {h : M₃ →ₗ[R] M}
    (hfh : Function.Surjective (f ∘ₗ h)) : Function.Surjective h := by
  rw [← LinearMap.range_eq_top]
  -- The range of `h` together with the superfluous `ker f` spans `M`, so the range is everything.
  exact hf.eq_top_of_sup_eq_top (by
    rw [sup_comm, ← Submodule.comap_map_eq, ← LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hfh, Submodule.comap_top])

/-- **Superfluous kernels are exactly the essential epimorphisms.** A surjection `f : M →ₗ[R] M₂`
has superfluous kernel precisely when no map into `M` can compose onto `M₂` without already being
onto; the submodule inclusions of `M` witness the nontrivial direction, so it suffices to quantify
over sources in the universe of `M` (over larger sources the implication is
`TauCeti.IsSuperfluous.surjective_of_surjective_comp`). -/
theorem isSuperfluous_ker_iff_forall_surjective {f : M →ₗ[R] M₂} (hf : Function.Surjective f) :
    IsSuperfluous (LinearMap.ker f) ↔
      ∀ {M₃ : Type v} [AddCommMonoid M₃] [Module R M₃] (h : M₃ →ₗ[R] M),
        Function.Surjective (f ∘ₗ h) → Function.Surjective h := by
  constructor
  · intro hker _ _ _ h hfh
    exact hker.surjective_of_surjective_comp hfh
  · intro H K hK
    have hmapK : Submodule.map f K = ⊤ := by
      have hall : Submodule.map f (LinearMap.ker f ⊔ K) = ⊤ := by
        rw [hK, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
      rwa [Submodule.map_sup, LinearMap.le_ker_iff_map.mp le_rfl, bot_sup_eq] at hall
    have hs : Function.Surjective (f ∘ₗ K.subtype) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype, hmapK]
    have hsub : Function.Surjective (K.subtype) := H (M₃ := K) K.subtype hs
    exact (Submodule.range_subtype K).symm.trans (LinearMap.range_eq_top.mpr hsub)

end AddCommGroup

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- A superfluous submodule is contained in the radical. -/
theorem IsSuperfluous.le_jacobson {N : Submodule R M} (hN : IsSuperfluous N) :
    N ≤ Module.jacobson R M := by
  rw [Module.jacobson_eq_radical]
  exact le_iInf₂ fun _ hm => hN.le_coatom hm

/-- Conversely, when every proper submodule of `M` sits under a maximal one, every submodule of the
radical is superfluous. -/
theorem isSuperfluous_of_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M}
    (h : N ≤ Module.jacobson R M) : IsSuperfluous N := by
  intro K hK
  -- This is the nongenerating property of the order radical of a coatomic lattice.
  refine Order.radical_nongenerating (top_le_iff.mp ?_)
  rw [← hK, ← Module.jacobson_eq_radical]
  exact sup_le (le_sup_of_le_right h) le_sup_left

/-- Over a module with coatomic submodule lattice — for instance a finitely generated one — the
superfluous submodules are exactly the submodules of the radical. -/
theorem isSuperfluous_iff_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M} :
    IsSuperfluous N ↔ N ≤ Module.jacobson R M :=
  ⟨IsSuperfluous.le_jacobson, isSuperfluous_of_le_jacobson⟩

/-- The radical of a module with coatomic submodule lattice — for instance a finitely generated
one — is superfluous; this is the form of Nakayama's lemma that the theory of projective covers
runs on. -/
theorem isSuperfluous_jacobson [IsCoatomic (Submodule R M)] :
    IsSuperfluous (Module.jacobson R M) :=
  isSuperfluous_of_le_jacobson le_rfl

end Ring

end TauCeti
