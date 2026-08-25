/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Order.Atoms

/-!
# Essential submodules

A submodule `N` of `M` is **essential** (also called *large*) when it is indispensable for
separating points of `M`: whenever `N ⊓ K = ⊥` for a submodule `K`, already `K = ⊥`. Essential
submodules are the notion dual to the superfluous submodules of
`TauCeti/Algebra/Module/Submodule/Superfluous.lean`, and a monomorphism `M ↪ Q` is an injective
envelope exactly when `Q` is injective and the image is essential in `Q`.

Mathlib has neither this predicate nor injective envelopes. This file supplies the predicate with
its lattice API and identifies it, on the modules where the comparison is available, with
containing every simple submodule.

The duality with superfluity is not formal — there is no order isomorphism between the submodule
lattices of a module and of a dual object — so the statements are proved, not transported. Two of
them are genuinely less symmetric than their superfluous counterparts: the image of an essential
submodule is essential only along an embedding whose own image is essential
(`TauCeti.IsEssential.map`, the analogue of `TauCeti.IsSuperfluous.comap`), while the preimage is
essential along **any** linear map (`TauCeti.IsEssential.comap`, the analogue of
`TauCeti.IsSuperfluous.map`).

## Main definitions

* `TauCeti.IsEssential`: `N ⊓ K = ⊥` forces `K = ⊥`.

## Main results

* `TauCeti.isEssential_iff`: the definition, restated so that essentiality can be proved and used
  downstream.
* `TauCeti.isEssential_top`, `TauCeti.IsEssential.mono`, `TauCeti.isEssential_inf_iff`: the
  essential submodules of `M` are closed upwards and under binary infima, and contain `⊤`.
* `TauCeti.isEssential_bot_iff`: `⊥` is essential exactly for the zero module.
* `TauCeti.IsEssential.comap`: the preimage of an essential submodule under any linear map is
  essential.
* `TauCeti.IsEssential.map`: the image of an essential submodule under an embedding whose range is
  itself essential is essential; `TauCeti.isEssential_map_equiv_iff` records that along an
  equivalence this is an equivalence. This is what makes injective envelopes compose.
* `TauCeti.IsEssential.injective_of_injective_comp` and
  `TauCeti.isEssential_range_iff_forall_injective`: an embedding has essential range exactly when
  it is an *essential monomorphism*, that is, when every map out of its target whose composite with
  it is injective is itself injective. This is the minimality that makes an injective envelope an
  injective envelope.
* `TauCeti.IsEssential.atom_le` and `TauCeti.isEssential_iff_forall_atom_le`: an essential
  submodule contains every atom of the submodule lattice — every simple submodule — and over an
  atomic submodule lattice that property characterizes essentiality.

## References

This is the essential-image vocabulary behind the injective-envelope half of the "projective covers
and injective envelopes" bullet of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for
`injectiveEnvelope M` dually to a projective cover.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4, and T. Y. Lam, *Lectures on Modules and Rings*, §3.
-/

public section

namespace TauCeti

universe u v w

section Semiring

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- A submodule `N` of `M` is **essential** (or *large*) when it meets every nonzero submodule:
any submodule `K` with `N ⊓ K = ⊥` is already `⊥`. -/
def IsEssential (N : Submodule R M) : Prop :=
  ∀ K : Submodule R M, N ⊓ K = ⊥ → K = ⊥

/-- Essentiality, restated. The body of `TauCeti.IsEssential` is not exposed outside this module,
so this is the interface through which essentiality is both proved and used. -/
theorem isEssential_iff {N : Submodule R M} :
    IsEssential N ↔ ∀ K : Submodule R M, N ⊓ K = ⊥ → K = ⊥ :=
  (Iff.rfl)

/-- The whole module is essential in itself. -/
@[simp]
theorem isEssential_top : IsEssential (⊤ : Submodule R M) := by
  intro K hK
  simpa using hK

/-- A submodule containing an essential submodule is essential. -/
theorem IsEssential.mono {N N' : Submodule R M} (hN : IsEssential N) (h : N ≤ N') :
    IsEssential N' := by
  intro K hK
  refine isEssential_iff.mp hN _ (le_bot_iff.mp ?_)
  rw [← hK]
  exact inf_le_inf_right K h

/-- The infimum of two essential submodules is essential. -/
theorem IsEssential.inf {N N' : Submodule R M} (hN : IsEssential N) (hN' : IsEssential N') :
    IsEssential (N ⊓ N') := by
  intro K hK
  refine isEssential_iff.mp hN' _ (isEssential_iff.mp hN _ ?_)
  rwa [← inf_assoc]

/-- An infimum of two submodules is essential exactly when both of them are. -/
@[simp]
theorem isEssential_inf_iff {N N' : Submodule R M} :
    IsEssential (N ⊓ N') ↔ IsEssential N ∧ IsEssential N' :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun h => h.1.inf h.2⟩

/-- The zero submodule is essential exactly in the zero module: essentiality of `⊥` says precisely
that `⊤ = ⊥`. -/
@[simp]
theorem isEssential_bot_iff : IsEssential (⊥ : Submodule R M) ↔ Subsingleton M := by
  refine ⟨fun h => (Submodule.subsingleton_iff R).mp (subsingleton_iff_bot_eq_top.mp ?_),
    fun _ K _ => Subsingleton.elim K ⊥⟩
  exact (isEssential_iff.mp h _ (by simp)).symm

/-- The zero submodule is not essential in a nonzero module. -/
theorem not_isEssential_bot [Nontrivial M] : ¬ IsEssential (⊥ : Submodule R M) := fun h =>
  not_subsingleton M (isEssential_bot_iff.mp h)

/-- An essential submodule of a nonzero module is nonzero. -/
theorem IsEssential.ne_bot [Nontrivial M] {N : Submodule R M} (hN : IsEssential N) : N ≠ ⊥ := by
  rintro rfl
  exact not_isEssential_bot hN

/-- The preimage of an essential submodule under any linear map is essential. -/
theorem IsEssential.comap {N : Submodule R M₂} (hN : IsEssential N) (f : M →ₗ[R] M₂) :
    IsEssential (N.comap f) := by
  intro K hK
  rw [Submodule.eq_bot_iff] at hK
  -- The image of `K` meets `N` only in `0`, hence vanishes, ...
  have hmap : K.map f = ⊥ := by
    refine isEssential_iff.mp hN _ ((Submodule.eq_bot_iff _).mpr fun y hy => ?_)
    obtain ⟨x, hxK, rfl⟩ := hy.2
    rw [hK x ⟨hy.1, hxK⟩, map_zero]
  -- ... so `K` lies in the kernel, which is contained in the preimage of `N`.
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hfx : f x = 0 := (Submodule.eq_bot_iff _).mp hmap (f x) (Submodule.mem_map_of_mem hx)
  exact hK x ⟨Submodule.mem_comap.mpr (by rw [hfx]; exact N.zero_mem), hx⟩

/-- The image of an essential submodule under an embedding whose range is itself essential is
essential. This is what makes injective envelopes compose; unlike the preimage
(`TauCeti.IsEssential.comap`), the image needs both hypotheses on the map: the image of `⊤` under
the inclusion of a non-essential submodule is that submodule, which is not essential. -/
theorem IsEssential.map {N : Submodule R M} (hN : IsEssential N) {f : M →ₗ[R] M₂}
    (hf : Function.Injective f) (hrange : IsEssential (LinearMap.range f)) :
    IsEssential (N.map f) := by
  intro K hK
  rw [Submodule.eq_bot_iff] at hK
  -- Upstairs, `N` meets the preimage of `K` only in `0`, so that preimage vanishes, ...
  have hcomap : K.comap f = ⊥ := by
    refine isEssential_iff.mp hN _ ((Submodule.eq_bot_iff _).mpr fun x hx => ?_)
    exact hf (by simpa using hK (f x) ⟨Submodule.mem_map_of_mem hx.1, hx.2⟩)
  -- ... hence `K` meets the range of `f` only in `0`, and the range is essential.
  refine isEssential_iff.mp hrange _ ((Submodule.eq_bot_iff _).mpr fun y hy => ?_)
  obtain ⟨x, hx⟩ := hy.1
  have hx0 : x = 0 :=
    (Submodule.eq_bot_iff _).mp hcomap x (Submodule.mem_comap.mpr (by rw [hx]; exact hy.2))
  rw [← hx, hx0, map_zero]

/-- Transport along a linear equivalence both preserves and reflects essentiality. -/
@[simp]
theorem isEssential_map_equiv_iff {N : Submodule R M} (e : M ≃ₗ[R] M₂) :
    IsEssential (N.map (e : M →ₗ[R] M₂)) ↔ IsEssential N := by
  -- An equivalence has essential range, namely `⊤`, so `TauCeti.IsEssential.map` applies both ways.
  refine ⟨fun h => ?_, fun h => h.map e.injective ?_⟩
  · have h' := h.map e.symm.injective
      (by rw [LinearMap.range_eq_top_of_surjective _ e.symm.surjective]; exact isEssential_top)
    rwa [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
      Submodule.comap_map_eq_of_injective e.injective] at h'
  · rw [LinearMap.range_eq_top_of_surjective _ e.surjective]
    exact isEssential_top

/-- An essential submodule contains every atom of the submodule lattice, that is, every simple
submodule. -/
theorem IsEssential.atom_le {N a : Submodule R M} (hN : IsEssential N) (ha : IsAtom a) : a ≤ N := by
  by_contra hle
  -- Otherwise `N ⊓ a` is strictly below the atom `a`, hence `⊥`, contradicting essentiality.
  have hlt : N ⊓ a < a :=
    lt_of_le_of_ne inf_le_right fun heq => hle ((le_of_eq heq.symm).trans inf_le_left)
  exact ha.1 (isEssential_iff.mp hN _ (ha.2 _ hlt))

/-- Conversely, when every nonzero submodule of `M` contains a simple one, a submodule containing
every simple submodule is essential. -/
theorem isEssential_of_forall_atom_le [IsAtomic (Submodule R M)] {N : Submodule R M}
    (h : ∀ a : Submodule R M, IsAtom a → a ≤ N) : IsEssential N := by
  intro K hK
  rcases eq_bot_or_exists_atom_le K with hbot | ⟨a, ha, hle⟩
  · exact hbot
  · have hab : a ≤ N ⊓ K := le_inf (h a ha) hle
    rw [hK] at hab
    exact absurd (le_bot_iff.mp hab) ha.1

/-- Over a module with atomic submodule lattice — for instance an Artinian one — the essential
submodules are exactly the submodules containing every simple submodule. -/
theorem isEssential_iff_forall_atom_le [IsAtomic (Submodule R M)] {N : Submodule R M} :
    IsEssential N ↔ ∀ a : Submodule R M, IsAtom a → a ≤ N :=
  ⟨fun h _ ha => h.atom_le ha, isEssential_of_forall_atom_le⟩

end Semiring

section Ring

variable {R : Type u} {M : Type v} {M₂ : Type w}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

/-- **An essential range is a minimality condition.** If `f : M →ₗ[R] M₂` has essential range and
`h : M₂ →ₗ[R] M₃` is such that `h ∘ₗ f` is injective, then `h` is already injective.

This is what makes an injective envelope minimal; it is `TauCeti.IsInjectiveEnvelope`'s workhorse,
and uses nothing about `f` beyond its range. -/
theorem IsEssential.injective_of_injective_comp {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {f : M →ₗ[R] M₂} (hf : IsEssential (LinearMap.range f)) {h : M₂ →ₗ[R] M₃}
    (hhf : Function.Injective (h ∘ₗ f)) : Function.Injective h := by
  rw [← LinearMap.ker_eq_bot]
  -- A nonzero element of the kernel would come from a nonzero element killed by `h ∘ₗ f`.
  refine isEssential_iff.mp hf _ ((Submodule.eq_bot_iff _).mpr fun y hy => ?_)
  obtain ⟨x, hx⟩ := hy.1
  have hy2 : h y = 0 := hy.2
  have hx0 : x = 0 := hhf (by simp [LinearMap.comp_apply, hx, hy2])
  rw [← hx, hx0, map_zero]

/-- **Essential ranges are exactly the essential monomorphisms.** An embedding `f : M →ₗ[R] M₂` has
essential range precisely when no map out of `M₂` can precompose to an embedding without already
being one; the quotient maps of `M₂` witness the nontrivial direction, so it suffices to quantify
over targets in the universe of `M₂` (over larger targets the implication is
`TauCeti.IsEssential.injective_of_injective_comp`). -/
theorem isEssential_range_iff_forall_injective {f : M →ₗ[R] M₂} (hf : Function.Injective f) :
    IsEssential (LinearMap.range f) ↔
      ∀ {M₃ : Type w} [AddCommGroup M₃] [Module R M₃] (h : M₂ →ₗ[R] M₃),
        Function.Injective (h ∘ₗ f) → Function.Injective h := by
  constructor
  · intro hrange _ _ _ h hhf
    exact hrange.injective_of_injective_comp hhf
  · intro H K hK
    -- The quotient by `K` is the test map: it kills `K` and nothing of the range of `f`.
    have hinj : Function.Injective (K.mkQ ∘ₗ f) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      have hmem : f x ∈ LinearMap.range f ⊓ K := ⟨⟨x, rfl⟩, hx⟩
      rw [hK, Submodule.mem_bot] at hmem
      exact hf (by simpa using hmem)
    have hmk := H K.mkQ hinj
    rwa [← LinearMap.ker_eq_bot, Submodule.ker_mkQ] at hmk

end Ring

end TauCeti
