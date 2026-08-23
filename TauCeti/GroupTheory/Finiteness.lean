/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Closure properties of finitely generated groups

Mathlib has a substantial theory of finitely generated commutative groups in
`Mathlib/GroupTheory/FiniteAbelian/Basic.lean` — the structure theorem, `finite_of_fg_isMulTorsion`,
and `Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which is the finiteness of `G ⧸ Gⁿ`. Three
closure properties it does not carry are collected here.

## Main results

* `AddSubgroup.fg_of_addCommGroup` and `Subgroup.fg_of_commGroup`: a subgroup of a finitely
  generated commutative group is finitely generated. The argument is Noetherianity of `ℤ`, so the
  *additive* statement is the foundational one and the multiplicative statement is transported
  from it through `Additive`; `to_additive` cannot relate them — it would have to translate the
  `ℤ`-module argument itself — so the pair is written out by hand and registered with
  `to_additive existing`. Both are `instance`s, matching how Mathlib states its other `FG` closure
  properties (`Group.fg_range`, `QuotientGroup.fg`, `Subgroup.fg_of_index_ne_zero`).
* `Subgroup.fg_of_fg_map_of_fg_inf_ker`: a subgroup `K` whose image `K.map φ` and whose
  intersection `K ⊓ φ.ker` with the kernel are finitely generated is itself finitely generated.
  This is the `Subgroup` analogue of Mathlib's `Submodule.fg_of_fg_map_of_fg_inf_ker`, an absence
  Mathlib records explicitly — a comment in
  `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` restructures a proof "due to no
  `Subgroup` version of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing". It carries the generator
  argument, and needs no commutativity.
* `Group.fg_of_fg_ker_of_fg_range`: an extension of finitely generated groups is finitely
  generated — if the kernel and the range of `φ : G →* H` are finitely generated then so is `G`.
  It is the `K = ⊤` case of the previous result, and is derived from it. It is a plain theorem
  rather than an instance, because `φ` is an explicit argument that typeclass resolution cannot
  infer.

Both are `@[to_additive]`, and both are steps towards the `S`-unit group being finitely
generated, which `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 names as an input to the weak
Mordell–Weil theorem: the group of `S`-units sits in an extension whose kernel is the unit group
of the base and whose range is a subgroup of a free group of rank `|S|`, so establishing finite
generation needs exactly these two facts. The finiteness that the descent then applies to it is
Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, read through
`Subgroup.finiteIndex_iff_finite_quotient`; nothing here reproves it.

`AddSubgroup.fg_of_addCommGroup`, `Subgroup.fg_of_commGroup` and `Group.fg_of_fg_ker_of_fg_range`
are adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.

**`Subgroup.fg_of_fg_map_of_fg_inf_ker` is new here**, with no counterpart in that source, which
has only the `K = ⊤` case; Mathlib records the general statement's absence in the comment at
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` quoted above. The generator
argument is Stoll's, restated for a subgroup.

That source file also carries `finite_modPow`, `finite_of_fg_of_pow_eq_one` and two `ℤ`-module
translation helpers. **None of them is ported: all four are now in Mathlib** — as
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, `CommGroup.finite_of_fg_isMulTorsion`, the
instance `AddMonoid.FG.to_moduleFinite_int`, and `Module.Finite.iff_addGroup_fg` composed with
`AddGroup.fg_iff_mul_fg`. The source predates those additions, some of which its own author
upstreamed, so check Mathlib again before porting anything further from it.

**Concurrent work upstream.** The open Mathlib pull request
[mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791) ("dirichlet's s-unit
theorem", by `vvvv-ops`, open since 2026-06-19) carries two of the results here as file-local
helpers of `Mathlib/RingTheory/DedekindDomain/SUnit.lean`, under different names:
`Subgroup.fg_of_commGroup` as `Subgroup.fg_of_fg_commGroup`, and
`Group.fg_of_fg_ker_of_fg_range` as `CommGroup.fg_of_fg_ker_of_fg_range` — the latter
`CommGroup`-only, where the version here needs no commutativity. On a bump that lands #40791, drop
`Subgroup.fg_of_commGroup` in favour of upstream's; the extension lemma here is strictly more
general, and `Subgroup.fg_of_fg_map_of_fg_inf_ker` has no counterpart there at all.
-/

public section

/-- **A subgroup of a finitely generated additive commutative group is finitely generated.** The
additive form of `Subgroup.fg_of_commGroup`. -/
-- `ℤ` is Noetherian, so `G` is a finitely generated `ℤ`-module and hence Noetherian, and the
-- submodule corresponding to `H` is finitely generated. The argument is about `ℤ`-modules, which
-- is why this additive form is the one proved directly.
instance (priority := 100) AddSubgroup.fg_of_addCommGroup {G : Type*} [AddCommGroup G]
    [AddGroup.FG G] (H : AddSubgroup G) : AddGroup.FG H :=
  (AddGroup.fg_iff_addSubgroup_fg H).mpr <| H.toIntSubmodule_toAddSubgroup ▸
    (Submodule.fg_iff_addSubgroup_fg _).mp (IsNoetherian.noetherian (R := ℤ) H.toIntSubmodule)

/-- **A subgroup of a finitely generated commutative group is finitely generated.** The
multiplicative form of `AddSubgroup.fg_of_addCommGroup`. -/
-- Transported through `Additive G`. `to_additive` cannot relate the two — it would have to
-- translate the `ℤ`-module argument itself — so the pair is written out by hand and registered
-- with `to_additive existing`, which puts it in the dictionary so downstream `@[to_additive]`
-- proofs using either can translate.
@[to_additive existing]
instance (priority := 100) Subgroup.fg_of_commGroup {G : Type*} [CommGroup G] [Group.FG G]
    (H : Subgroup G) : Group.FG H :=
  -- `AddGroup.FG (Additive G)` is Mathlib's instance `AddGroup.fg_of_group_fg`, found by search
  (Group.fg_iff_subgroup_fg H).mpr <| (Subgroup.fg_iff_add_fg H).mpr <|
    (AddGroup.fg_iff_addSubgroup_fg (Subgroup.toAddSubgroup H)).mp inferInstance

/-- **A subgroup whose image and whose intersection with the kernel are finitely generated is
itself finitely generated.** The `Subgroup` analogue of Mathlib's
`Submodule.fg_of_fg_map_of_fg_inf_ker`, whose absence Mathlib records explicitly: a comment in
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` restructures a proof "due to no
`Subgroup` version of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing".

`Group.fg_of_fg_ker_of_fg_range` is its `K = ⊤` case. -/
-- `K` is generated by preimages in `K` of generators of `K.map φ`, together with generators of
-- `K ⊓ φ.ker`: an `x ∈ K` agrees under `φ` with some `n` in their closure `N`, and then `n⁻¹ * x`
-- lies in `K ⊓ φ.ker ≤ N`.
@[to_additive /-- **An additive subgroup whose image and whose intersection with the kernel are
finitely generated is itself finitely generated.** The `AddSubgroup` analogue of Mathlib's
`Submodule.fg_of_fg_map_of_fg_inf_ker`. `AddGroup.fg_of_fg_ker_of_fg_range` is its `K = ⊤`
case. -/]
theorem Subgroup.fg_of_fg_map_of_fg_inf_ker {G H : Type*} [Group G] [Group H] (φ : G →* H)
    {K : Subgroup G} (h₁ : (K.map φ).FG) (h₂ : (K ⊓ φ.ker).FG) : K.FG := by
  obtain ⟨T, hT, hTfin⟩ := (Subgroup.fg_iff _).mp h₁
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff _).mp h₂
  -- a preimage in `K` for each generator of the image
  have hTmem : ∀ t ∈ T, ∃ g, g ∈ K ∧ φ g = t := fun t ht ↦
    Subgroup.mem_map.mp (by rw [← hT]; exact Subgroup.subset_closure ht)
  choose! σ hσK hσ using hTmem
  have hSle : S ⊆ (K ⊓ φ.ker : Subgroup G) := by rw [← hS]; exact Subgroup.subset_closure
  refine (Subgroup.fg_iff _).mpr ⟨σ '' T ∪ S, ?_, (hTfin.image σ).union hSfin⟩
  set N := Subgroup.closure (σ '' T ∪ S) with hN
  -- the generators lie in `K`
  have hle : N ≤ K := by
    rw [hN, Subgroup.closure_le]
    rintro g (⟨t, ht, rfl⟩ | hg)
    exacts [hσK t ht, (hSle hg).1]
  refine le_antisymm hle fun x hx ↦ ?_
  -- `φ x` is hit by `N`, since `N.map φ` contains every generator of `K.map φ`
  have hTle : T ⊆ (N.map φ : Set H) := fun t ht ↦
    ⟨σ t, Subgroup.subset_closure (Set.mem_union_left _ ⟨t, ht, rfl⟩), hσ t ht⟩
  have hxT : φ x ∈ Subgroup.closure T := by rw [hT]; exact ⟨x, hx, rfl⟩
  obtain ⟨n, hnN, hn⟩ := (Subgroup.closure_le _).mpr hTle hxT
  -- so `n⁻¹ * x` lies in `K ⊓ φ.ker`, hence in `N`
  have hker : n⁻¹ * x ∈ K ⊓ φ.ker :=
    ⟨K.mul_mem (K.inv_mem (hle hnN)) hx, by simp [hn]⟩
  rw [← hS] at hker
  have := (Subgroup.closure_le N).mpr
    (fun s hs ↦ Subgroup.subset_closure (Set.mem_union_right _ hs)) hker
  simpa using N.mul_mem hnN this

/-- **An extension of finitely generated groups is finitely generated:** if the kernel and the
range of `φ : G →* H` are finitely generated, then so is `G`. This is the `K = ⊤` case of
`Subgroup.fg_of_fg_map_of_fg_inf_ker`. -/
@[to_additive /-- **An extension of finitely generated additive groups is finitely generated:** if
the kernel and the range of `φ : G →+ H` are finitely generated, then so is `G`. This is the
`K = ⊤` case of `AddSubgroup.fg_of_fg_map_of_fg_inf_ker`. -/]
theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    [Group.FG φ.ker] [Group.FG φ.range] : Group.FG G := by
  have h₁ : ((⊤ : Subgroup G).map φ).FG := by
    rw [← MonoidHom.range_eq_map]
    exact (Group.fg_iff_subgroup_fg _).mp ‹Group.FG φ.range›
  have h₂ : ((⊤ : Subgroup G) ⊓ φ.ker).FG := by
    rw [top_inf_eq]
    exact (Group.fg_iff_subgroup_fg _).mp ‹Group.FG φ.ker›
  -- `Group.FG G` is by definition finite generation of `(⊤ : Subgroup G)`
  exact ⟨Subgroup.fg_of_fg_map_of_fg_inf_ker φ h₁ h₂⟩

end
