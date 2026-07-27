/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.Homotopy.Product
-- Private: `Path.codRestrict`, `Path.map_codRestrict`, and
-- `Path.Homotopic.map_nullhomotopic_of_nullhomotopic` are used only in private proofs below,
-- so this import is not re-exported.
import TauCeti.Topology.Homotopy.Path

/-!
# Semilocally simply connected spaces

A topological space `X` is *semilocally simply connected* if every point `x` has a
neighbourhood `U` such that every loop in `U` based at `x` is null-homotopic *in `X`*. This is
the standing point-set hypothesis (alongside path-connectedness and local path-connectedness)
under which the universal cover of a space exists; see the universal-covers roadmap. Mathlib
master has `SimplyConnectedSpace` and the local notions `LocallyContractibleSpace` and
`StronglyLocallyContractibleSpace`, but no semilocal simple connectivity; the predicate follows
Kim Morrison's unmerged mathlib4#38292 (see the References below).

The condition is genuinely *semi*local: the null-homotopy is allowed to leave `U` and use the
whole of `X`. It is therefore weaker than asking each `U` to be simply connected on its own (the
local notion); the constructor
`SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected` records that
implication. The classical local-contractibility hypothesis `LocallyContractibleSpace` is also
enough (`SemilocallySimplyConnectedSpace.of_locallyContractibleSpace`), and through it every
strongly locally contractible space is semilocally simply connected. Discrete spaces are also
instances, witnessed by singleton neighbourhoods.

## Main declarations

* `TauCeti.SemilocallySimplyConnectedSpace`: the predicate, as a typeclass.
* `TauCeti.SemilocallySimplyConnectedSpace.exists_mem_nhds_subset_loops_nullhomotopic`: the
  witnessing neighbourhood can be taken inside any prescribed neighbourhood.
* `TauCeti.SemilocallySimplyConnectedSpace.exists_isOpen_mem_nhds_loops_nullhomotopic`: the
  witnessing neighbourhood can be taken open, the form the universal-cover construction consumes.
* `TauCeti.SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected`: a space
  in which every point has a simply connected neighbourhood is semilocally simply connected.
* `TauCeti.SemilocallySimplyConnectedSpace.of_locallyContractibleSpace`: a locally contractible
  space is semilocally simply connected.
* Instances deriving the property for simply connected spaces, strongly locally contractible
  spaces, discrete spaces, and binary products.

## References

This file supplies the semilocal-simple-connectivity hypothesis required by the Tau Ceti
universal-covers roadmap (`TauCetiRoadmap/UniversalCovers`); see the standing hypotheses there.
The predicate follows the one Kim Morrison introduces (as `SemilocallySimplyConnectedSpace`, the
classical based notion of Brazas, Definition 2.1, https://arxiv.org/abs/1102.0993) in mathlib4
PRs [#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292), which state the
universal-cover construction over `[SemilocallySimplyConnectedSpace X]`; neither has merged, so
the predicate is not yet in Mathlib. The API here is a streamlined single-field restatement
sufficient for the roadmap's Stage 0.2.
-/

public section

open Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is **semilocally simply connected** if every point `x` has a neighbourhood `U` such
that every loop in `U` based at `x` is null-homotopic in the whole space. The null-homotopy is
allowed to leave `U`, which is what makes this weaker than local simple connectivity. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point has a neighbourhood in which every based loop is null-homotopic in `X`. -/
  exists_mem_nhds_loops_nullhomotopic (x : X) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x)

namespace SemilocallySimplyConnectedSpace

variable [SemilocallySimplyConnectedSpace X]

/-- The witnessing neighbourhood of a point can be shrunk to lie inside any prescribed
neighbourhood: loops contained in a smaller set are in particular contained in the larger one. -/
theorem exists_mem_nhds_subset_loops_nullhomotopic (x : X) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U ∈ 𝓝 x, U ⊆ V ∧ ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hloop⟩ := exists_mem_nhds_loops_nullhomotopic (X := X) x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Set.inter_subset_right, fun γ hγ => ?_⟩
  exact hloop γ fun t => (hγ t).1

/-- The witnessing neighbourhood can be taken open and inside any prescribed neighbourhood. This
is the form consumed by the universal-cover construction, where the sheets must be open. -/
theorem exists_isOpen_mem_nhds_subset_loops_nullhomotopic (x : X) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hUV, hloop⟩ := exists_mem_nhds_subset_loops_nullhomotopic x hV
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  exact ⟨W, hWopen, hxW, hWU.trans hUV, fun γ hγ => hloop γ fun t => hWU (hγ t)⟩

/-- The witnessing neighbourhood can be taken open. This is the form consumed by the
universal-cover construction, where the sheets must be open. -/
theorem exists_isOpen_mem_nhds_loops_nullhomotopic (x : X) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hUopen, hxU, -, hloop⟩ :=
    exists_isOpen_mem_nhds_subset_loops_nullhomotopic x (V := Set.univ) Filter.univ_mem
  exact ⟨U, hUopen, hxU, hloop⟩

end SemilocallySimplyConnectedSpace

/-- If every point of `X` has a simply connected neighbourhood, then `X` is semilocally simply
connected: a loop inside such a neighbourhood is already null-homotopic there, hence in `X`. -/
theorem SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, IsSimplyConnected U) : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    obtain ⟨U, hU, hsc⟩ := h x
    refine ⟨U, hU, fun γ hγ => ?_⟩
    obtain ⟨F, -⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 x γ hγ
    exact ⟨F⟩

/-- A locally contractible space (each neighbourhood of a point contains a smaller neighbourhood
whose inclusion into the larger one is null-homotopic) is semilocally simply connected. A based
loop in the smaller neighbourhood becomes null-homotopic once pushed forward along the
null-homotopic inclusion into `X`. -/
theorem SemilocallySimplyConnectedSpace.of_locallyContractibleSpace
    (h : LocallyContractibleSpace X) : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    obtain ⟨V, hVU, hV, hnull⟩ := h x Set.univ Filter.univ_mem
    -- The inclusion `↥V → X` (factoring through `↥univ`) is null-homotopic.
    let j : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hnj : j.Nullhomotopic :=
      hnull.comp_right (⟨Subtype.val, continuous_subtype_val⟩ : C((Set.univ : Set X), X))
    refine ⟨V, hV, fun γ hγ => ?_⟩
    -- Restrict the loop `γ` to the subspace `V` via `codRestrict`; pushing it forward along the
    -- null-homotopic inclusion `j` recovers `γ` (`Path.map_codRestrict`), so `γ` is null-homotopic
    -- in `X`.
    let xV : V := ⟨x, mem_of_mem_nhds hV⟩
    have hmap :=
      Path.Homotopic.map_nullhomotopic_of_nullhomotopic hnj (γ.codRestrict hγ : Path xV xV)
    rwa [Path.map_codRestrict] at hmap

/-- A simply connected space is semilocally simply connected: the whole space already witnesses
the condition, since every loop is null-homotopic. -/
instance (priority := 100) [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x :=
    ⟨Set.univ, Filter.univ_mem,
      fun γ _ => (simply_connected_iff_loops_nullhomotopic.mp ‹_›).2 x γ⟩

/-- A strongly locally contractible space (each point has a basis of contractible neighbourhoods)
is semilocally simply connected, since strong local contractibility implies the classical local
contractibility hypothesis. -/
instance (priority := 100) [StronglyLocallyContractibleSpace X] :
    SemilocallySimplyConnectedSpace X :=
  .of_locallyContractibleSpace StronglyLocallyContractibleSpace.locallyContractible

/-- A discrete space is semilocally simply connected: the singleton neighbourhood of a point
contains only the constant loop. -/
instance (priority := 100) [DiscreteTopology X] : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    refine ⟨{x}, (isOpen_discrete _).mem_nhds rfl, fun γ hγ => ?_⟩
    have hγx : γ = Path.refl x := by
      ext t
      simpa using hγ t
    rw [hγx]

/-- A product of semilocally simply connected spaces is semilocally simply connected: a loop in a
product of witnessing neighbourhoods projects to loops in each factor, and their null-homotopies
combine into a null-homotopy of the original loop. -/
instance [SemilocallySimplyConnectedSpace X] [SemilocallySimplyConnectedSpace Y] :
    SemilocallySimplyConnectedSpace (X × Y) where
  exists_mem_nhds_loops_nullhomotopic := by
    rintro ⟨x, y⟩
    obtain ⟨U, hU, hUloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (X := X) x
    obtain ⟨V, hV, hVloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (X := Y) y
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, fun γ hγ => ?_⟩
    obtain ⟨F₁⟩ := hUloop (γ.map continuous_fst) fun t => (Set.mem_prod.mp (hγ t)).1
    obtain ⟨F₂⟩ := hVloop (γ.map continuous_snd) fun t => (Set.mem_prod.mp (hγ t)).2
    have key : ((γ.map continuous_fst).prod (γ.map continuous_snd)).Homotopic
        ((Path.refl x).prod (Path.refl y)) := ⟨Path.Homotopic.prodHomotopy F₁ F₂⟩
    have hleft : (γ.map continuous_fst).prod (γ.map continuous_snd) = γ := by
      ext t <;> simp
    have hright : (Path.refl x).prod (Path.refl y) = Path.refl (x, y) := by
      ext t <;> simp
    rwa [hleft, hright] at key

end TauCeti
