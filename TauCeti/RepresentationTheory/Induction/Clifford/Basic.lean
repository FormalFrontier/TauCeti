/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Restriction to a normal subgroup preserves semisimplicity

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G`.  Cutting
the group down to `N` does not preserve irreducibility, but it does preserve semisimplicity: the
restriction of `ρ` to `N` is a sum of irreducibles, as soon as there is a minimal nonzero
`N`-stable subspace to start from — which for a finite-dimensional `ρ` there always is.

The mechanism is a single observation.  If `U ⊆ V` is stable under `N`, then so is `ρ g '' U` for
every `g : G`, because `ρ n (ρ g u) = ρ g (ρ (g⁻¹ n g) u)` and `g⁻¹ n g` lies in `N` by normality.
Translation by `ρ g` therefore acts on the lattice of `N`-subrepresentations
(`TauCeti.Representation.conjSubrep`), by order isomorphisms
(`TauCeti.Representation.conjSubrepOrderIso`), so it preserves atoms; and it identifies `U` with its
translate not as representations of `N` on the nose but after twisting the action of `N` by
conjugation (`TauCeti.Representation.conjSubrepEquiv`).  That twist is exactly the conjugation
action `TauCeti.conjNormalRep` on representations of `N` built in
`TauCeti/RepresentationTheory/Induction/Conjugate.lean`, whose stabilisers are the inertia groups of
`TauCeti/RepresentationTheory/Induction/Inertia.lean`.

Two theorems come out of it.  First, the translates of a single nonzero `N`-subrepresentation span:
their sum is stable under all of `G`, so irreducibility of `ρ` forces it to be everything
(`TauCeti.Representation.iSup_conjSubrep_eq_top`).  Second, if the subrepresentation being
translated is *minimal*, the span exhibits `V` as a sum of simple `N`-submodules, so the restriction
to `N` is semisimple (`TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`) --
and this needs no invertibility of `Nat.card N`, so it is not Maschke's theorem in disguise.

Throughout, an irreducible constituent is presented as an **atom** of the lattice of
`N`-subrepresentations rather than as an abstract irreducible representation of `N` mapping in.
That is what keeps the argument free of finiteness hypotheses: no dimension count and no counting of
conjugates enters.  Finite-dimensionality is used only to *produce* an atom, in
`TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`.

## Main definitions

* `TauCeti.Representation.conjSubrep`: the translate `ρ g '' U` of an `N`-subrepresentation `U`.
* `TauCeti.Representation.conjSubrepOrderIso`: translation as an order isomorphism of the lattice
  of `N`-subrepresentations.
* `TauCeti.Representation.conjSubrepEquiv`: translation by `ρ g` as an equivalence from `U`, with
  its action of `N` twisted by conjugation, onto the translate.

## Main statements

* `TauCeti.Representation.iSup_conjSubrep_eq_top`: the translates of a nonzero
  `N`-subrepresentation of an irreducible representation span.
* `TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top`: the same statement read in the
  lattice of `k[N]`-submodules of the restriction.
* `TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`: if some
  `N`-subrepresentation of an irreducible representation `IsAtom`, then the restriction to `N` is
  semisimple.
* `TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`: the same conclusion for a
  **finite-dimensional** irreducible representation, where such an atom is automatic
  (`TauCeti.Representation.exists_isAtom`).

## Implementation notes

The three constructions above are opaque: their bodies are not exported, and everything downstream
goes through their characteristic lemmas `toSubmodule_conjSubrep`, `conjSubrepOrderIso_apply`,
`conjSubrepOrderIso_symm_apply`, `coe_conjSubrepEquiv_apply` and `coe_conjSubrepEquiv_symm_apply`
instead.  The first four are proved by `(rfl)` rather than by `rfl`: a bare `rfl` body asks in
addition that the equation stay true by `rfl` *outside* this file, which for an unexposed definition
it is not.  The parenthesized form checks the proof here, where the bodies are visible, and exports
only the statement.

## References

This file supplies item (iii) of the **prerequisite** of Layer 5 (Clifford theory over a normal
subgroup) of `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` — "restriction
along a subgroup preserves semisimplicity" — in the normal-subgroup case Clifford theory uses,
as `TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`.  It stops there: nothing below
mentions a decomposition, an isotypic component, a multiplicity or a `G`-orbit of constituents.
What the file does leave in place is the translation machinery the **Clifford's theorem** milestone
runs on, since it is the same machinery the semisimplicity statement is proved from; the
single-orbit half of that milestone is
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit.lean`.

The mathematics is the classical argument of C. W. Curtis and I. Reiner, *Representation Theory of
Finite Groups and Associative Algebras*, §49.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

section Translate

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- Acting by `g` and then by `n ∈ N` is the same as acting by the conjugate `g⁻¹ n g` and then by
`g`.  This conjugation identity is what everything below rests on: it is why translating an
`N`-stable subspace by `ρ g` produces another `N`-stable subspace, and why the two carry the same
representation of `N` up to a conjugation twist.

The conjugate is written as Mathlib's `MulAut.conjNormal g⁻¹`, the automorphism of `N` that
`TauCeti.conjNormalRep` twists by. -/
theorem apply_conjNormal_inv (g : G) (n : N) (v : V) :
    ρ g (ρ (MulAut.conjNormal g⁻¹ n : G) v) = ρ (n : G) (ρ g v) := by
  -- `MulAut.conjNormal g⁻¹` sends `n` to `g⁻¹ * n * g⁻¹⁻¹`, and it is only after that double
  -- inverse is cleared that the two group elements below are visibly equal.
  have hg : g * (MulAut.conjNormal g⁻¹ n : G) = (n : G) * g := by
    rw [MulAut.conjNormal_apply]
    group
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]

/-- The **translate** of an `N`-subrepresentation `σ` by `g : G`: the image of `σ` under `ρ g`,
again stable under `N` because `N` is normal.

For `g ∈ N` this is `σ` itself; in general it is a possibly different subspace, carrying the
representation of `N` obtained from `σ` by conjugating with `g` (`conjSubrepEquiv`).

The carrier is `σ.toSubmodule.map (ρ g)` (`toSubmodule_conjSubrep`), which is how everything below
reasons about a translate: through the submodule lattice rather than through this definition. -/
def conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Subrepresentation (ρ.comp N.subtype) where
  toSubmodule := σ.toSubmodule.map (ρ g)
  apply_mem_toSubmodule := by
    rintro n _ ⟨v, hv, rfl⟩
    exact ⟨_, σ.apply_mem_toSubmodule (MulAut.conjNormal g⁻¹ n) hv,
      apply_conjNormal_inv ρ g n v⟩

variable {ρ}

@[simp]
theorem toSubmodule_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    (conjSubrep ρ g σ).toSubmodule = σ.toSubmodule.map (ρ g) :=
  (rfl)

@[simp]
theorem mem_conjSubrep_iff {g : G} {σ : Subrepresentation (ρ.comp N.subtype)} {v : V} :
    v ∈ conjSubrep ρ g σ ↔ ρ g⁻¹ v ∈ σ := by
  refine ⟨?_, fun h => ⟨_, h, _root_.Representation.self_inv_apply ρ g v⟩⟩
  rintro ⟨u, hu, rfl⟩
  rwa [_root_.Representation.inv_self_apply]

/-- Translating by an element of `N` itself does nothing: an `N`-subrepresentation is already
stable under `N`, and under `N`-inverses. -/
@[simp]
theorem conjSubrep_eq_self_of_mem {g : G} (hg : g ∈ N)
    (σ : Subrepresentation (ρ.comp N.subtype)) : conjSubrep ρ g σ = σ := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · rw [toSubmodule_conjSubrep]
    rintro _ ⟨v, hv, rfl⟩
    simpa using σ.apply_mem_toSubmodule ⟨g, hg⟩ hv
  · intro v hv
    rw [toSubmodule_conjSubrep]
    exact ⟨ρ g⁻¹ v, by simpa using σ.apply_mem_toSubmodule ⟨g⁻¹, inv_mem hg⟩ hv,
      _root_.Representation.self_inv_apply ρ g v⟩

/-- Translation is an action: translating by `1` does nothing.  Not a `simp` lemma, since
`conjSubrep_eq_self_of_mem` already rewrites this way once it discharges `(1 : G) ∈ N`. -/
theorem conjSubrep_one (σ : Subrepresentation (ρ.comp N.subtype)) : conjSubrep ρ 1 σ = σ :=
  conjSubrep_eq_self_of_mem (one_mem N) σ

@[simp]
theorem conjSubrep_conjSubrep (g h : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubrep ρ g (conjSubrep ρ h σ) = conjSubrep ρ (g * h) σ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [toSubmodule_conjSubrep, toSubmodule_conjSubrep, toSubmodule_conjSubrep,
      ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]

@[simp]
theorem conjSubrep_bot (g : G) : conjSubrep ρ g (⊥ : Subrepresentation (ρ.comp N.subtype)) = ⊥ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [toSubmodule_conjSubrep, Subrepresentation.toSubmodule_bot, Submodule.map_bot]

@[simp]
theorem conjSubrep_top (g : G) : conjSubrep ρ g (⊤ : Subrepresentation (ρ.comp N.subtype)) = ⊤ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [toSubmodule_conjSubrep, Subrepresentation.toSubmodule_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact (_root_.Representation.apply_bijective ρ g).surjective

variable (ρ) in
/-- Translation by `ρ g` is an order isomorphism of the lattice of `N`-subrepresentations, with
inverse translation by `ρ g⁻¹`.  In particular it takes atoms to atoms
(`isAtom_conjSubrep_iff`). -/
def conjSubrepOrderIso (g : G) :
    Subrepresentation (ρ.comp N.subtype) ≃o Subrepresentation (ρ.comp N.subtype) where
  toFun := conjSubrep ρ g
  invFun := conjSubrep ρ g⁻¹
  left_inv σ := by rw [conjSubrep_conjSubrep, inv_mul_cancel, conjSubrep_one]
  right_inv σ := by rw [conjSubrep_conjSubrep, mul_inv_cancel, conjSubrep_one]
  map_rel_iff' {σ τ} := by
    simp only [Equiv.coe_fn_mk, ← Subrepresentation.toSubmodule_le_toSubmodule,
      toSubmodule_conjSubrep]
    exact Submodule.map_le_map_iff_of_injective
      (_root_.Representation.apply_bijective ρ g).injective _ _

@[simp]
theorem conjSubrepOrderIso_apply (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubrepOrderIso ρ g σ = conjSubrep ρ g σ :=
  (rfl)

@[simp]
theorem conjSubrepOrderIso_symm_apply (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    (conjSubrepOrderIso ρ g).symm σ = conjSubrep ρ g⁻¹ σ :=
  (rfl)

@[simp]
theorem isAtom_conjSubrep_iff {g : G} {σ : Subrepresentation (ρ.comp N.subtype)} :
    IsAtom (conjSubrep ρ g σ) ↔ IsAtom σ := by
  rw [← conjSubrepOrderIso_apply g σ]
  exact (conjSubrepOrderIso ρ g).isAtom_iff σ

variable (ρ) in
/-- Translation by `ρ g` identifies `σ`, with its action of `N` twisted by conjugation by `g`,
with the translate `conjSubrep ρ g σ`.

The twist is unavoidable: the two subspaces are exchanged by `ρ g`, which does not commute with `N`
but conjugates it.  The twisted source is the conjugate representation `TauCeti.conjNormalRep g` of
`TauCeti/RepresentationTheory/Induction/Conjugate.lean`, unbundled: it is
`(conjNormalRep g (Rep.of σ.toRepresentation)).ρ` by `TauCeti.conjNormalRep_ρ`.  It is written here
as the plain composition rather than through `Rep.of`, which would need `V` to be an `AddCommGroup`
where this section asks only for an `AddCommMonoid`.  Read on isomorphism classes, this says that
`conjSubrep ρ g σ` represents the image of the class of `σ` under the conjugation action of `g` on
representations of `N`.

The underlying map is `ρ g` (`coe_conjSubrepEquiv_apply`), and its inverse is `ρ g⁻¹`
(`coe_conjSubrepEquiv_symm_apply`). -/
noncomputable def conjSubrepEquiv (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    _root_.Representation.Equiv
      (σ.toRepresentation.comp ((MulAut.conjNormal g⁻¹ : MulAut N) : N →* N))
      (conjSubrep ρ g σ).toRepresentation :=
  _root_.Representation.Equiv.mk
    (σ.toSubmodule.equivMapOfInjective (ρ g) (_root_.Representation.apply_bijective ρ g).injective)
    (fun n => by
      ext u
      exact apply_conjNormal_inv ρ g n u)

@[simp]
theorem coe_conjSubrepEquiv_apply (g : G) (σ : Subrepresentation (ρ.comp N.subtype))
    (u : σ.toSubmodule) : (conjSubrepEquiv ρ g σ u : V) = ρ g (u : V) :=
  (rfl)

/-- The inverse of `conjSubrepEquiv` is translation back by `ρ g⁻¹`. -/
@[simp]
theorem coe_conjSubrepEquiv_symm_apply (g : G) (σ : Subrepresentation (ρ.comp N.subtype))
    (v : (conjSubrep ρ g σ).toSubmodule) :
    ((conjSubrepEquiv ρ g σ).symm v : V) = ρ g⁻¹ (v : V) := by
  refine (_root_.Representation.apply_bijective ρ g).injective ?_
  rw [_root_.Representation.self_inv_apply, ← coe_conjSubrepEquiv_apply g σ]
  exact congrArg Subtype.val ((conjSubrepEquiv ρ g σ).apply_symm_apply v)

end Translate

section Clifford

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **The translates of a nonzero `N`-subrepresentation of an irreducible representation span.**
Their sum is a subspace stable under every `ρ h`, hence a subrepresentation of `ρ` itself, and it is
nonzero, so irreducibility leaves it no choice. -/
theorem iSup_conjSubrep_eq_top [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    ⨆ g : G, (conjSubrep ρ g σ).toSubmodule = ⊤ := by
  have hmap : ∀ h : G, (⨆ g : G, (conjSubrep ρ g σ).toSubmodule).map (ρ h)
      ≤ ⨆ g : G, (conjSubrep ρ g σ).toSubmodule := by
    intro h
    rw [Submodule.map_iSup]
    refine iSup_le fun g => ?_
    rw [← toSubmodule_conjSubrep h (conjSubrep ρ g σ), conjSubrep_conjSubrep]
    exact le_iSup (fun g : G => (conjSubrep ρ g σ).toSubmodule) (h * g)
  -- the sum of the translates is stable under all of `G`, not just under `N`
  let τ : Subrepresentation ρ :=
    { toSubmodule := ⨆ g : G, (conjSubrep ρ g σ).toSubmodule
      apply_mem_toSubmodule := fun h v hv => hmap h ⟨v, hv, rfl⟩ }
  have hτσ : σ.toSubmodule ≤ τ.toSubmodule := by
    refine le_iSup_of_le 1 ?_
    rw [toSubmodule_conjSubrep, map_one, Module.End.one_eq_id, Submodule.map_id]
  rcases IsSimpleOrder.eq_bot_or_eq_top τ with h | h
  · refine absurd (Subrepresentation.toSubmodule_injective ?_) hσ
    have hbot : τ.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_bot]
    exact le_bot_iff.mp (hbot ▸ hτσ)
  · exact congrArg Subrepresentation.toSubmodule h

/-- **The translates of a nonzero `N`-subrepresentation of an irreducible representation span, as
`k[N]`-submodules.**  This is `TauCeti.Representation.iSup_conjSubrep_eq_top` read in the lattice of
`k[N]`-submodules of `Representation.asModule (ρ.comp N.subtype)` instead of the lattice of
`k`-subspaces of `V`; the two lattices are exchanged by
`Subrepresentation.subrepresentationSubmoduleOrderIso`, and this is the only place the exchange is
performed. -/
theorem iSup_asSubmodule_conjSubrep_eq_top [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    ⨆ g : G, (conjSubrep ρ g σ).asSubmodule = ⊤ := by
  -- The lattice of subrepresentations is only a `BoundedOrder`, with no suprema of its own, so the
  -- supremum is formed on the submodule side and pulled back, rather than pushed forward.
  set S : Subrepresentation (ρ.comp N.subtype) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm
      (⨆ g : G, (conjSubrep ρ g σ).asSubmodule) with hS
  have hSeq : S.asSubmodule = ⨆ g : G, (conjSubrep ρ g σ).asSubmodule := by
    rw [hS, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      OrderIso.apply_symm_apply]
  have hle : ∀ g : G, conjSubrep ρ g σ ≤ S := fun g => by
    rw [← Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply, hSeq]
    exact le_iSup (fun g : G => (conjSubrep ρ g σ).asSubmodule) g
  have htop : S = ⊤ := by
    refine Subrepresentation.toSubmodule_injective (le_antisymm le_top ?_)
    rw [Subrepresentation.toSubmodule_top, ← iSup_conjSubrep_eq_top ρ hσ]
    exact iSup_le fun g => hle g
  rw [← hSeq, htop, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    OrderIso.map_top]

/-- **Restriction to a normal subgroup is semisimple, from a minimal constituent.** If an
irreducible representation has a minimal nonzero `N`-stable subspace, then its restriction to `N`
is semisimple: the translates of that subspace are again minimal and they span, so the restriction
is a sum of simple `N`-submodules.

No hypothesis relating `Nat.card N` to the characteristic is needed; irreducibility of the ambient
representation does the work Maschke's theorem would otherwise do. -/
theorem isSemisimpleRepresentation_comp_subtype_of_isAtom [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  rw [_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine IsSemisimpleModule.of_sSup_simples_eq_top (eq_top_iff.mpr ?_)
  rw [← iSup_asSubmodule_conjSubrep_eq_top ρ hσ.1]
  refine iSup_le fun g => le_sSup ?_
  rw [Set.mem_ofPred_eq]
  exact Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)

/-- **Restriction to a normal subgroup preserves semisimplicity.** The restriction to a normal
subgroup of a finite-dimensional irreducible representation is semisimple. -/
theorem isSemisimpleRepresentation_comp_subtype [ρ.IsIrreducible] [FiniteDimensional k V] :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] _
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨σ, hσ⟩ := exists_isAtom (ρ.comp N.subtype)
  exact isSemisimpleRepresentation_comp_subtype_of_isAtom ρ hσ

end Clifford

end Representation

end TauCeti
