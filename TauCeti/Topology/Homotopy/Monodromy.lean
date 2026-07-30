/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import TauCeti.Topology.Homotopy.Covering

/-!
# The subgroup a cover recovers from a chosen lift of the basepoint

Let `p : E → X` be a covering map and let `e` be a point of the fibre over `x`. Mathlib's
`IsCoveringMap.fundamentalGroupMulAction` makes `π₁(X, x)` act on that fibre by monodromy.
This file identifies the stabiliser of `e` for that action with the image of `π₁(E, e)` under
`p`:

`MulAction.stabilizer (π₁(X, x)) e = (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range`.

That image is the subgroup the classification of covering spaces attaches to the *pointed*
cover `(E, e)`, so the identification is the bridge between the topological side (which loops
of the base lift to loops of the cover) and the group-theoretic side (which subgroup of
`π₁(X, x)` is recovered).

Three consequences follow, and are the reason the identification is worth isolating.

* Because a covering map is injective on homotopy classes of paths with fixed endpoints
  (Mathlib's `IsCoveringMap.injective_path_homotopic_map`), it is injective on fundamental
  groups, so the recovered subgroup is a copy of `π₁(E, e)` itself.
* When `E` is path connected the monodromy action is transitive, so the orbit-stabiliser
  theorem turns the fibre into the coset space of the recovered subgroup; in particular the
  number of sheets of the cover is the index of that subgroup.
* Changing the lift `e` inside the fibre conjugates the recovered subgroup, and when `E` is
  path connected every conjugate arises this way: a pointed cover recovers a subgroup, an
  unpointed connected cover only its conjugacy class. The recovered subgroup is normal exactly
  when it does not depend on the chosen lift.

Mathlib proves the analogous statement `IsQuotientCoveringMap.ker_monodromyPerm` only for a
cover presented as a quotient by a group action, where the stabiliser of a single point is
automatically the kernel of the whole monodromy representation. For a general cover the two
subgroups differ, and it is the stabiliser, not the kernel, that the classification uses.

## Main declarations

* `TauCeti.IsCoveringMap.monodromy_eq_self_iff_mem_range`: a loop class of the base fixes the
  chosen lift under monodromy exactly when it is the image of a loop class of the cover.
* `TauCeti.IsCoveringMap.stabilizer_eq_range`: the same statement for the monodromy
  `MulAction`.
* `TauCeti.IsCoveringMap.mapOfEq_injective`: the map induced by a covering map on fundamental
  groups is injective, so `MonoidHom.ofInjective` makes the recovered subgroup a copy of
  `π₁(E, e)`.
* `TauCeti.IsCoveringMap.exists_monodromy_eq` and
  `TauCeti.IsCoveringMap.monodromy_isPretransitive`: monodromy is transitive on a fibre of a
  path-connected cover.
* `TauCeti.IsCoveringMap.fiberEquivQuotientRange` and
  `TauCeti.IsCoveringMap.card_fiber_eq_index`: the fibre is the coset space of the recovered
  subgroup, so the number of sheets is its index.
* `TauCeti.IsCoveringMap.range_mapOfEq_monodromy` and
  `TauCeti.IsCoveringMap.exists_range_eq_map_conj`: changing the lift conjugates the recovered
  subgroup, and realises every conjugate.
* `TauCeti.IsCoveringMap.normal_range_iff`: the recovered subgroup is normal exactly when it is
  independent of the chosen lift.

## References

This is Stage 2 of `TauCetiRoadmap/UniversalCovers/README.md`: item 7 asks for the subgroup a
pointed cover recovers and for the way it transforms when the chosen lift changes, and item 8
splits the classification into a pointed statement about subgroups and an unpointed statement
about conjugacy classes, phrased "via transitive `π₁(X)`-sets". Everything here is built from
Junyan Xu's monodromy API in `Mathlib/Topology/Homotopy/Lifting.lean`; no Mathlib proof is
vendored.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

namespace IsCoveringMap

/-! ### The recovered subgroup -/

/-- A loop class of the base fixes a chosen lift `e` of the basepoint under monodromy exactly
when it is the image of a loop class of the total space based at `e`.

The image subgroup on the right is the subgroup of `π₁(X, x)` that the classification of covers
attaches to the pointed cover `(E, e)`. -/
theorem monodromy_eq_self_iff_mem_range (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    hp.monodromy γ e = e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  constructor
  · intro h
    refine ⟨(hp.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h.symm), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      hp.map_liftPathQuotient]
    simp
  · rintro ⟨δ, rfl⟩
    refine hp.monodromy_eq_of_map_eq δ ?_
    simp [FundamentalGroup.mapOfEq_apply]

/-- The stabiliser of a chosen lift `e` of the basepoint, for the monodromy action of
`π₁(X, x)` on the fibre over `x`, is the image of `π₁(E, e)` under the covering map. -/
@[simp]
theorem stabilizer_eq_range (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    letI := hp.fundamentalGroupMulAction x
    MulAction.stabilizer (FundamentalGroup X x) e =
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  letI := hp.fundamentalGroupMulAction x
  ext γ
  exact monodromy_eq_self_iff_mem_range hp e γ

/-! ### The recovered subgroup is a copy of `π₁` of the cover -/

/-- A covering map induces an injective map on fundamental groups. This is the fundamental-group
form of Mathlib's `IsCoveringMap.injective_path_homotopic_map`.

Combined with `MonoidHom.ofInjective`, it exhibits the recovered subgroup as a copy of
`π₁(E, e)`. -/
theorem mapOfEq_injective (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2) := by
  intro δ δ' h
  refine hp.injective_path_homotopic_map (e : E) (e : E) ?_
  have h' := congrArg (fun q : FundamentalGroup X x =>
    Path.Homotopic.Quotient.cast q e.2 e.2) h
  simpa [FundamentalGroup.mapOfEq_apply] using h'

/-! ### Transitivity on a fibre -/

/-- On a fibre of a path-connected cover, monodromy is transitive: a path joining two lifts
projects to a loop of the base whose monodromy carries the first lift to the second. -/
theorem exists_monodromy_eq [PathConnectedSpace E] (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    ∃ γ : FundamentalGroup X x, hp.monodromy γ e = e' := by
  set Γ : Path.Homotopic.Quotient (e : E) (e' : E) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (e : E) (e' : E))
  refine ⟨FundamentalGroup.fromPath
    ((Γ.map ⟨p, hp.continuous⟩).cast e.2.symm e'.2.symm), hp.monodromy_eq_of_map_eq Γ ?_⟩
  simp

/-- The monodromy action of `π₁(X, x)` on a fibre of a path-connected cover is transitive. -/
theorem monodromy_isPretransitive [PathConnectedSpace E] (hp : IsCoveringMap p) (x : X) :
    letI := hp.fundamentalGroupMulAction x
    MulAction.IsPretransitive (FundamentalGroup X x) (p ⁻¹' {x}) := by
  letI := hp.fundamentalGroupMulAction x
  exact ⟨fun e e' => exists_monodromy_eq hp e e'⟩

/-! ### The fibre as a coset space -/

/-- **Orbit-stabiliser for a covering map.** Choosing a lift `e` of the basepoint identifies the
fibre over `x` with the coset space of the subgroup of `π₁(X, x)` recovered from `(E, e)`,
provided the cover is path connected. -/
noncomputable def fiberEquivQuotientRange [PathConnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {x}) :
    p ⁻¹' {x} ≃
      FundamentalGroup X x ⧸ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range :=
  letI := hp.fundamentalGroupMulAction x
  haveI := monodromy_isPretransitive hp x
  (Equiv.subtypeUnivEquiv (p := fun e' : p ⁻¹' {x} =>
        e' ∈ MulAction.orbit (FundamentalGroup X x) e)
      fun e' =>
        (MulAction.orbit_eq_univ (FundamentalGroup X x) e).symm ▸ Set.mem_univ e').symm.trans
    ((MulAction.orbitEquivQuotientStabilizer (FundamentalGroup X x) e).trans
      (Subgroup.quotientEquivOfEq (stabilizer_eq_range hp e)))

/-- The inverse of the orbit-stabiliser identification sends the coset of a loop class to the
monodromy translate of the chosen lift. -/
@[simp]
theorem fiberEquivQuotientRange_symm_apply_mk [PathConnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (fiberEquivQuotientRange hp e).symm (QuotientGroup.mk γ) = hp.monodromy γ e :=
  letI := hp.fundamentalGroupMulAction x
  MulAction.orbitEquivQuotientStabilizer_symm_apply (FundamentalGroup X x) e γ

/-- **The number of sheets of a path-connected cover is the index of the recovered subgroup.** -/
theorem card_fiber_eq_index [PathConnectedSpace E] (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    Nat.card (p ⁻¹' {x}) =
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range.index :=
  Nat.card_congr (fiberEquivQuotientRange hp e)

/-! ### Dependence on the chosen lift -/

/-- Moving the chosen lift by monodromy conjugates the recovered subgroup. -/
theorem range_mapOfEq_monodromy (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ (hp.monodromy γ e).2).range =
      ((FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range).map
        (MulAut.conj γ).toMonoidHom := by
  letI := hp.fundamentalGroupMulAction x
  rw [← stabilizer_eq_range hp e, ← stabilizer_eq_range hp (hp.monodromy γ e)]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj γ e

/-- On a path-connected cover, any two lifts of the basepoint recover conjugate subgroups: an
unpointed connected cover determines only the conjugacy class of the subgroup. -/
theorem exists_range_eq_map_conj [PathConnectedSpace E] (hp : IsCoveringMap p)
    (e e' : p ⁻¹' {x}) :
    ∃ γ : FundamentalGroup X x,
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e'.2).range =
        ((FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range).map
          (MulAut.conj γ).toMonoidHom := by
  obtain ⟨γ, hγ⟩ := exists_monodromy_eq hp e e'
  exact ⟨γ, by rw [← hγ, range_mapOfEq_monodromy hp e γ]⟩

/-- On a path-connected cover, the subgroup recovered from a lift of the basepoint is normal
exactly when it does not depend on which lift is chosen. This is the subgroup-side criterion for
the cover to be regular. -/
theorem normal_range_iff [PathConnectedSpace E] (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range.Normal ↔
      ∀ e' : p ⁻¹' {x},
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e'.2).range =
          (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  constructor
  · intro hnormal e'
    obtain ⟨γ, hγ⟩ := exists_range_eq_map_conj hp e e'
    rw [hγ, MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.normal_iff_map_conj_eq.mp hnormal γ
  · intro hconst
    refine Subgroup.normal_iff_map_conj_eq.mpr fun γ => ?_
    rw [← MulEquiv.toMonoidHom_eq_coe, ← range_mapOfEq_monodromy hp e γ]
    exact hconst _

end IsCoveringMap

end TauCeti
