/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Induction.Conjugate
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Clifford's theorem

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G`.  Clifford's
theorem describes what `ρ` looks like once the group is cut down to `N`: the restriction is
semisimple — once there is a minimal nonzero `N`-stable subspace to start from, which for a
finite-dimensional `ρ` there always is — and its irreducible constituents are all carried into one
another by `G`.

The mechanism is a single observation.  If `U ⊆ V` is stable under `N`, then so is `ρ g '' U` for
every `g : G`, because `ρ n (ρ g u) = ρ g (ρ (g⁻¹ n g) u)` and `g⁻¹ n g` lies in `N` by normality.
Translation by `ρ g` therefore acts on the lattice of `N`-subrepresentations
(`TauCeti.Representation.conjSubrep`), by order isomorphisms
(`TauCeti.Representation.conjSubrepOrderIso`), so it preserves atoms; and it identifies `U` with its
translate not as representations of `N` on the nose but after twisting the action of `N` by
conjugation (`TauCeti.Representation.conjSubrepEquiv`).  That twist is exactly
`TauCeti.conjNormalRep`, the conjugation action on representations of `N` built in
`TauCeti/RepresentationTheory/Induction/Conjugate.lean`, whose stabilisers are the inertia groups of
`TauCeti/RepresentationTheory/Induction/Inertia.lean`.

Two theorems come out of it.  First, the translates of a single nonzero `N`-subrepresentation span:
their sum is stable under all of `G`, so irreducibility of `ρ` forces it to be everything
(`TauCeti.Representation.iSup_conjSubrep_eq_top`).  Second, if the subrepresentation being
translated is *minimal*, the span exhibits `V` as a sum of simple `N`-submodules, so the restriction
to `N` is semisimple (`TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`) --
and this needs no invertibility of `Nat.card N`, so it is not Maschke's theorem in disguise.
Semisimplicity then supplies an `N`-equivariant projection onto any other minimal
`N`-subrepresentation, which cannot annihilate every translate, and Schur's lemma turns the
surviving map into an isomorphism (`TauCeti.Representation.exists_nonempty_equiv_conjSubrep`).
Composed with the twist, this says that any two irreducible constituents of the restriction are
conjugate (`TauCeti.Representation.exists_nonempty_equiv_conjNormalRep`): the constituents form a
single `G`-orbit.

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
* `TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`: **Clifford's theorem,
  first half** -- if some `N`-subrepresentation of an irreducible representation `IsAtom`, then the
  restriction to `N` is semisimple.
* `TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`: the same conclusion for a
  **finite-dimensional** irreducible representation, where such an atom is automatic.
* `TauCeti.Representation.exists_nonempty_equiv_conjSubrep`: **Clifford's theorem, second half** --
  any two minimal `N`-subrepresentations of an irreducible representation are translates of one
  another, up to isomorphism.
* `TauCeti.Representation.exists_nonempty_equiv_conjNormalRep`: the same statement read through
  `TauCeti.conjNormalRep`, so that the irreducible constituents of the restriction form a single
  orbit under the conjugation action of `G` on representations of `N`.
* `TauCeti.Representation.finrank_eq_finrank_of_isAtom`: consequently all the constituents have the
  same `Module.finrank` over `k`.

## Implementation notes

The three constructions above are opaque: their bodies are not exported, and everything downstream
goes through their characteristic lemmas `toSubmodule_conjSubrep`, `conjSubrepOrderIso_apply`,
`conjSubrepOrderIso_symm_apply`, `coe_conjSubrepEquiv_apply` and `coe_conjSubrepEquiv_symm_apply`
instead.  The first four are proved by `(rfl)` rather than by `rfl`: a bare `rfl` body asks in
addition that the equation stay true by `rfl` *outside* this file, which for an unexposed definition
it is not.  The parenthesized form checks the proof here, where the bodies are visible, and exports
only the statement.

## References

This file builds the **Clifford's theorem** milestone of Layer 5 (Clifford theory over a normal
subgroup) of `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks that
for an irreducible `W`, "`Res_N W` is semisimple ... and **isotypic under the `G`-action**: its
irreducible `N`-constituents form a single `G`-orbit".  The milestone's remaining clause, that the
constituents all occur with one common multiplicity `e` so that `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ}V`, is the
one that consumes the layer's isotypic-decomposition prerequisite; it is not claimed here, and
nothing below refers to a decomposition or a multiplicity.  Item (iii) of that prerequisite, that
restriction along a subgroup preserves semisimplicity, is what
`TauCeti.Representation.isSemisimpleRepresentation_comp_subtype` supplies in the normal-subgroup
case Clifford theory uses.

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
`g`.  This is the whole content of Clifford theory: it is why translating an `N`-stable subspace by
`ρ g` produces another `N`-stable subspace, and why the two carry the same representation of `N` up
to a conjugation twist.

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
where this section asks only for an `AddCommMonoid`; `exists_nonempty_equiv_conjNormalRep`, where
that hypothesis is present anyway, is stated in the bundled form.  Read on isomorphism classes, this
says that `conjSubrep ρ g σ` represents the image of the class of `σ` under the conjugation action
of `g` on representations of `N`.

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

/-- **Clifford's theorem, first half, from a minimal constituent.** If an irreducible representation
has a minimal nonzero `N`-stable subspace, then its restriction to `N` is semisimple: the translates
of that subspace are again minimal and they span, so the restriction is a sum of simple
`N`-submodules.

No hypothesis relating `Nat.card N` to the characteristic is needed; irreducibility of the ambient
representation does the work Maschke's theorem would otherwise do. -/
theorem isSemisimpleRepresentation_comp_subtype_of_isAtom [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  rw [_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine IsSemisimpleModule.of_sSup_simples_eq_top (le_antisymm le_top ?_)
  have hmem : ∀ g : G, Subrepresentation.asSubmodule (conjSubrep ρ g σ) ∈
      { m : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) |
        IsSimpleModule k[N] m } := by
    intro g
    rw [Set.mem_ofPred_eq, isSimpleModule_iff_isAtom]
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff _).mpr
      (isAtom_conjSubrep_iff.mpr hσ)
  -- pull the supremum back to a subrepresentation, where the spanning statement lives
  set T : Subrepresentation (ρ.comp N.subtype) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm
      (sSup { m : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) |
        IsSimpleModule k[N] m }) with hT
  have hTsSup : Subrepresentation.asSubmodule T =
      sSup { m : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) |
        IsSimpleModule k[N] m } := by
    rw [hT, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      OrderIso.apply_symm_apply]
  have hle : ∀ g : G, conjSubrep ρ g σ ≤ T := fun g => by
    rw [← Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply, hTsSup]
    exact le_sSup (hmem g)
  have htop : T = ⊤ := by
    refine Subrepresentation.toSubmodule_injective (le_antisymm le_top ?_)
    rw [Subrepresentation.toSubmodule_top, ← iSup_conjSubrep_eq_top ρ hσ.1]
    exact iSup_le fun g => hle g
  rw [← hTsSup, htop, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    OrderIso.map_top]

/-- **Clifford's theorem, first half.** The restriction to a normal subgroup of a finite-dimensional
irreducible representation is semisimple. -/
theorem isSemisimpleRepresentation_comp_subtype [ρ.IsIrreducible] [FiniteDimensional k V] :
    _root_.Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  have hbot : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥ := by
    intro h
    have h' : (⊤ : Submodule k V) = ⊥ := by
      simpa using congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (by simpa using h'.symm))
  obtain ⟨σ, -, hσ⟩ := exists_isAtom_le (ρ := ρ.comp N.subtype) hbot
  exact isSemisimpleRepresentation_comp_subtype_of_isAtom ρ hσ

variable {ρ}

/-- **Clifford's theorem, second half.** Any two minimal `N`-subrepresentations of an irreducible
representation are isomorphic after translating one of them by an element of `G`.

Semisimplicity of the restriction gives an `N`-equivariant projection onto `σ'`.  It cannot kill
every translate of `σ`, since the translates span; the surviving map goes between two irreducible
representations of `N`, so Schur's lemma makes it an isomorphism. -/
theorem exists_nonempty_equiv_conjSubrep [ρ.IsIrreducible]
    {σ σ' : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hσ' : IsAtom σ') :
    ∃ g : G, Nonempty (_root_.Representation.Equiv (conjSubrep ρ g σ).toRepresentation
      σ'.toRepresentation) := by
  have := isSemisimpleRepresentation_comp_subtype_of_isAtom ρ hσ
  obtain ⟨τ, hτ⟩ := ComplementedLattice.exists_isCompl σ'
  have hc : IsCompl σ'.toSubmodule τ.toSubmodule := Subrepresentation.isCompl_toSubmodule hτ
  set P : V →ₗ[k] σ'.toSubmodule := Submodule.projectionOnto σ'.toSubmodule τ.toSubmodule hc
    with hP
  -- the projection along an invariant complement is `N`-equivariant
  have hequiv : ∀ (n : N) (v : V), P (ρ (n : G) v) = σ'.toRepresentation n (P v) :=
    (Subrepresentation.isIntertwiningMap_projectionOnto hτ).isIntertwining
  -- the projection cannot vanish on every translate, because the translates span
  have hne : ∃ g : G, ∃ v ∈ (conjSubrep ρ g σ).toSubmodule, P v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hker : (⊤ : Submodule k V) ≤ LinearMap.ker P := by
      rw [← iSup_conjSubrep_eq_top ρ hσ.1]
      exact iSup_le fun g v hv => LinearMap.mem_ker.mpr (hcon g v hv)
    have hσ'bot : σ'.toSubmodule ≠ ⊥ := fun h => hσ'.1
      (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hσ'bot
    have hzero : P w = 0 := LinearMap.mem_ker.mp (hker Submodule.mem_top)
    rw [hP, Submodule.projectionOnto_apply_of_mem_left hc hw] at hzero
    exact hw0 (congrArg Subtype.val hzero)
  obtain ⟨g, v, hv, hPv⟩ := hne
  -- restricted to that translate, the projection is a nonzero map between irreducibles
  have hirr : (conjSubrep ρ g σ).toRepresentation.IsIrreducible :=
    isIrreducible_toRepresentation_of_isAtom (isAtom_conjSubrep_iff.mpr hσ)
  have hirr' : σ'.toRepresentation.IsIrreducible := isIrreducible_toRepresentation_of_isAtom hσ'
  set f : _root_.Representation.IntertwiningMap (conjSubrep ρ g σ).toRepresentation
      σ'.toRepresentation :=
    (P ∘ₗ (conjSubrep ρ g σ).toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _
      (fun n u => hequiv n (u : V))
  have hfne : f ≠ 0 := by
    intro h
    have h0 : f ⟨v, hv⟩ = 0 := by rw [h]; rfl
    exact hPv h0
  exact ⟨g, ⟨f.ofBijective
    ((_root_.Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hfne)⟩⟩

/-- **Clifford's theorem, orbit form.** Every minimal `N`-subrepresentation of an irreducible
representation is isomorphic to a conjugate of any other, the conjugate being the one
`TauCeti.conjNormalRep` takes: the irreducible constituents of the restriction form a single orbit
under the conjugation action of `G` on representations of `N`. -/
theorem exists_nonempty_equiv_conjNormalRep [ρ.IsIrreducible]
    {σ σ' : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hσ' : IsAtom σ') :
    ∃ g : G, Nonempty (_root_.Representation.Equiv
      (conjNormalRep g (Rep.of σ.toRepresentation)).ρ σ'.toRepresentation) := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_equiv_conjSubrep hσ hσ'
  refine ⟨g, ⟨?_⟩⟩
  -- the source of `conjSubrepEquiv` is the conjugated action written as a composition; name the
  -- equality with the `conjNormalRep` form, from `conjNormalRep_ρ`, and transport along it rather
  -- than leaving the two descriptions to be identified by definitional unfolding
  have hρ : (conjNormalRep g (Rep.of σ.toRepresentation)).ρ =
      σ.toRepresentation.comp ((MulAut.conjNormal g⁻¹ : MulAut N) : N →* N) := by
    ext x v
    exact congrArg (fun f => f v) (conjNormalRep_ρ g (Rep.of σ.toRepresentation) x)
  rw [hρ]
  exact (conjSubrepEquiv ρ g σ).trans e

/-- All the irreducible constituents of the restriction of an irreducible representation to a
normal subgroup have the same `Module.finrank` over `k`. -/
theorem finrank_eq_finrank_of_isAtom [ρ.IsIrreducible]
    {σ σ' : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hσ' : IsAtom σ') :
    Module.finrank k σ.toSubmodule = Module.finrank k σ'.toSubmodule := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_equiv_conjSubrep hσ hσ'
  refine Eq.trans (LinearEquiv.finrank_eq (σ.toSubmodule.equivMapOfInjective (ρ g)
    (_root_.Representation.apply_bijective ρ g).injective)) ?_
  exact LinearEquiv.finrank_eq e.toLinearEquiv

end Clifford

end Representation

end TauCeti
