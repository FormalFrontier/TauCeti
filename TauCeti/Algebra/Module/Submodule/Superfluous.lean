/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.Radical
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Superfluous submodules

A submodule `N` of `M` is **superfluous** (also called *small*) when it is dispensable for
generating `M`: whenever `N ⊔ K = ⊤` for a submodule `K`, already `K = ⊤`. Superfluous submodules
are the dual notion to essential submodules, and they are what makes a *projective cover* a
minimal projective presentation: an epimorphism `P ↠ M` is a projective cover exactly when `P` is
projective and its kernel is superfluous in `P`.

Mathlib has neither this predicate nor projective covers. This file supplies the predicate with
its lattice API and identifies it, on the modules where the comparison is available, with being
contained in the radical `Module.jacobson`.

## Main definitions

* `TauCeti.IsSuperfluous`: `N ⊔ K = ⊤` forces `K = ⊤`.

## Main results

* `TauCeti.isSuperfluous_bot`, `TauCeti.IsSuperfluous.mono`, `TauCeti.IsSuperfluous.sup`: the
  superfluous submodules of `M` are closed downwards and under binary suprema, and contain `⊥`.
* `TauCeti.IsSuperfluous.le_jacobson`: a superfluous submodule lies in every coatom, hence in the
  radical `Module.jacobson R M`.
* `TauCeti.isSuperfluous_iff_le_jacobson`: over a module whose submodule lattice is coatomic — in
  particular over a finitely generated module — the converse holds, so the superfluous submodules
  are exactly the submodules of the radical, and
  `TauCeti.isSuperfluous_jacobson` records that the radical itself is then superfluous.
* `TauCeti.IsSuperfluous.map`: the image of a superfluous submodule under a surjection is
  superfluous.
* `TauCeti.IsSuperfluous.comap`: the preimage of a superfluous submodule under a surjection whose
  kernel is superfluous is again superfluous. This is what makes projective covers compose.
* `TauCeti.IsSuperfluous.surjective_of_surjective_comp`: a map into the source of a linear map with
  superfluous kernel whose composite with that map is surjective is itself surjective. This is the
  minimality that makes a projective cover a projective cover.

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

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A submodule `N` of `M` is **superfluous** (or *small*) when it is dispensable for generating
`M`: any submodule `K` with `N ⊔ K = ⊤` is already `⊤`. -/
def IsSuperfluous (N : Submodule R M) : Prop :=
  ∀ K : Submodule R M, N ⊔ K = ⊤ → K = ⊤

/-- The defining property of a superfluous submodule, in the shape it is consumed in. -/
theorem IsSuperfluous.eq_top {N K : Submodule R M} (hN : IsSuperfluous N) (h : N ⊔ K = ⊤) :
    K = ⊤ :=
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
  refine hN'.eq_top (top_le_iff.mp ?_)
  rw [← hK]
  exact sup_le_sup_right h K

/-- The supremum of two superfluous submodules is superfluous. -/
theorem IsSuperfluous.sup {N N' : Submodule R M} (hN : IsSuperfluous N) (hN' : IsSuperfluous N') :
    IsSuperfluous (N ⊔ N') := by
  intro K hK
  refine hN'.eq_top (hN.eq_top ?_)
  rwa [← sup_assoc]

/-- The whole module is superfluous in itself only when it is zero: `⊥ = ⊤` is exactly what
superfluity of `⊤` says. -/
@[simp]
theorem not_isSuperfluous_top [Nontrivial M] : ¬ IsSuperfluous (⊤ : Submodule R M) := by
  intro h
  exact absurd (h.eq_top (by simp)) (bot_ne_top (α := Submodule R M))

/-- A superfluous submodule of a nonzero module is proper. -/
theorem IsSuperfluous.ne_top [Nontrivial M] {N : Submodule R M} (hN : IsSuperfluous N) : N ≠ ⊤ := by
  rintro rfl
  exact not_isSuperfluous_top hN

end Semiring

section Ring

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

/-- A superfluous submodule is contained in every maximal submodule, hence in the radical: if it
were not contained in the coatom `m`, then `N ⊔ m` would strictly exceed `m`, so be `⊤`, forcing
`m = ⊤`. -/
theorem IsSuperfluous.le_jacobson {N : Submodule R M} (hN : IsSuperfluous N) :
    N ≤ Module.jacobson R M := by
  refine le_sInf fun m hm => ?_
  by_contra hle
  have hlt : m < N ⊔ m := by
    refine lt_of_le_of_ne le_sup_right fun heq => hle ?_
    rw [heq]
    exact le_sup_left
  exact hm.1 (hN.eq_top (hm.2 _ hlt))

/-- Conversely, when every proper submodule of `M` sits under a maximal one, every submodule of the
radical is superfluous. This is `Order.radical_nongenerating`, the nongenerating property of the
order radical of a coatomic lattice, read through the fact that `Module.jacobson R M` *is* the
order radical of `Submodule R M`: both are the infimum of the coatoms. -/
theorem isSuperfluous_of_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M}
    (h : N ≤ Module.jacobson R M) : IsSuperfluous N := by
  have hrad : Module.jacobson R M = Order.radical (Submodule R M) := sInf_eq_iInf
  intro K hK
  refine Order.radical_nongenerating (top_le_iff.mp ?_)
  rw [← hK, ← hrad]
  exact sup_le (le_sup_of_le_right h) le_sup_left

/-- Over a module with coatomic submodule lattice — for instance a finitely generated one — the
superfluous submodules are exactly the submodules of the radical. -/
@[simp]
theorem isSuperfluous_iff_le_jacobson [IsCoatomic (Submodule R M)] {N : Submodule R M} :
    IsSuperfluous N ↔ N ≤ Module.jacobson R M :=
  ⟨IsSuperfluous.le_jacobson, isSuperfluous_of_le_jacobson⟩

/-- The radical of a finitely generated module is superfluous; this is the form of Nakayama's
lemma that the theory of projective covers runs on. -/
theorem isSuperfluous_jacobson [Module.Finite R M] :
    IsSuperfluous (Module.jacobson R M) :=
  isSuperfluous_of_le_jacobson le_rfl

/-- The image of a superfluous submodule under a surjection is superfluous. -/
theorem IsSuperfluous.map {N : Submodule R M} (hN : IsSuperfluous N) {f : M →ₗ[R] M₂}
    (hf : Function.Surjective f) : IsSuperfluous (N.map f) := by
  intro K hK
  have hcomap : N ⊔ K.comap f = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun m => ?_
    have hfm : f m ∈ N.map f ⊔ K := by rw [hK]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfm
    obtain ⟨n, hn, rfl⟩ := hy
    have hmem : m - n ∈ K.comap f := by
      simp only [Submodule.mem_comap, map_sub, ← hyz]
      simpa using hz
    simpa using Submodule.add_mem_sup hn hmem
  have hcomapK : K.comap f = ⊤ := hN.eq_top hcomap
  have hmapcomap := Submodule.map_comap_eq_of_surjective hf K
  rw [hcomapK, Submodule.map_top, LinearMap.range_eq_top.mpr hf] at hmapcomap
  exact hmapcomap.symm

/-- A superfluous submodule stays superfluous after transport along a linear equivalence. -/
theorem IsSuperfluous.map_equiv {N : Submodule R M} (hN : IsSuperfluous N) (e : M ≃ₗ[R] M₂) :
    IsSuperfluous (N.map (e : M →ₗ[R] M₂)) :=
  hN.map e.surjective

/-- The preimage of a superfluous submodule under a surjection whose kernel is itself superfluous
is superfluous. Pushing a complement forward makes it a complement of the superfluous submodule
downstairs, and pulling the resulting equality back costs exactly the kernel. -/
theorem IsSuperfluous.comap {K : Submodule R M₂} (hK : IsSuperfluous K) {f : M →ₗ[R] M₂}
    (hf : Function.Surjective f) (hker : IsSuperfluous (LinearMap.ker f)) :
    IsSuperfluous (K.comap f) := by
  intro L hL
  have hmapL : L.map f = ⊤ := by
    refine hK.eq_top ?_
    rw [← Submodule.map_comap_eq_of_surjective hf K, ← Submodule.map_sup, hL, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  refine hker.eq_top (Submodule.eq_top_iff'.mpr fun m => ?_)
  have hfm : f m ∈ L.map f := by rw [hmapL]; exact Submodule.mem_top
  obtain ⟨l, hl, hfl⟩ := hfm
  have hmem : m - l ∈ LinearMap.ker f := by
    simp [LinearMap.mem_ker, map_sub, hfl]
  simpa using Submodule.add_mem_sup hmem hl

/-- **A superfluous kernel is a minimality condition.** If `f : M →ₗ[R] M₂` has superfluous kernel
and `h : M₃ →ₗ[R] M` is such that `f ∘ₗ h` is onto, then `h` is already onto: the range of `h`
together with the superfluous `ker f` spans `M`, so the range is everything.

This is what makes a projective cover minimal; it is `TauCeti.IsProjectiveCover`'s workhorse, and
uses nothing about `f` beyond its kernel. -/
theorem IsSuperfluous.surjective_of_surjective_comp {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {f : M →ₗ[R] M₂} (hf : IsSuperfluous (LinearMap.ker f)) {h : M₃ →ₗ[R] M}
    (hfh : Function.Surjective (f ∘ₗ h)) : Function.Surjective h := by
  rw [← LinearMap.range_eq_top]
  refine hf.eq_top (Submodule.eq_top_iff'.mpr fun m => ?_)
  obtain ⟨x, hx⟩ := hfh (f m)
  have hfhx : f (h x) = f m := by simpa using hx
  have hker : m - h x ∈ LinearMap.ker f := by
    simp [LinearMap.mem_ker, map_sub, hfhx]
  simpa using Submodule.add_mem_sup hker (LinearMap.mem_range_self h x)

end Ring

end TauCeti
