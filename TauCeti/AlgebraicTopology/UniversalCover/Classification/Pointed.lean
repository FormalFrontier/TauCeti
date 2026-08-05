/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation
public import TauCeti.Topology.Homotopy.Covering

/-!
# Pointed connected covers are determined by the subgroup they recover

A *pointed cover* of `(X, x)` is a covering map `p : E → X` together with a lift `e₀` of `x`.
It recovers the subgroup `p_* π₁(E, e₀) ≤ π₁(X, x)`, and
`TauCeti.IsCoveringMap.stabilizer_eq_range` identifies that subgroup with the stabiliser of `e₀`
for the monodromy action. This file proves that, for path-connected and locally path-connected
total spaces, the recovered subgroup determines the pointed cover:

* there is a map of pointed covers `(E, e₀) → (F, f₀)` over `X` exactly when
  `p_* π₁(E, e₀) ≤ q_* π₁(F, f₀)`, and it is then unique;
* if the two recovered subgroups are *equal*, that map is a homeomorphism over `X`.

This is the faithful-and-full half of the correspondence between pointed connected covers of
`(X, x)` and subgroups of `π₁(X, x)`; the remaining half is the construction, from a subgroup
`H`, of a cover recovering `H`, which is a separate milestone. Nothing here needs `X` itself to
be path-connected, locally path-connected or semilocally simply connected: those hypotheses are
what make the correspondence *onto*, not what makes it injective.

The existence direction is Mathlib's lifting criterion
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, applied with the total space `E`
as the source; the only work is the basepoint bookkeeping needed to state it symmetrically in
the two covers, since a pointed cover recovers a subgroup of `π₁(X, x)` rather than of
`π₁(X, p e₀)`. The containment direction is elementary functoriality. Turning the two resulting
maps into a homeomorphism uses Mathlib's uniqueness of lifts on a preconnected space,
`IsCoveringMap.eq_of_comp_eq`, and no further covering-space input.

Specialising to simply connected total spaces gives the uniqueness of the universal cover: any
two simply connected covers of `X` are isomorphic over `X`, by a homeomorphism matching chosen
lifts of a basepoint. (Their universal *property* is already Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`, which lifts any map from a simply connected,
locally path-connected space.)

## Main declarations

* `TauCeti.IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le`: a unique map of pointed
  covers over `X` exists as soon as the recovered subgroups are nested.
* `TauCeti.IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le`: such a map exists *exactly*
  when the recovered subgroups are nested.
* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq` and
  `TauCeti.IsCoveringMap.totalSpaceHomeomorphOfRangeEq`: pointed covers recovering the same
  subgroup are isomorphic over `X` by a homeomorphism matching the chosen lifts.
* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq`: the recovered subgroup is a
  complete invariant of a pointed cover.
* `TauCeti.IsCoveringMap.eq_totalSpaceHomeomorphOfRangeEq`: that homeomorphism is the only map of
  pointed covers over `X`.
* `TauCeti.IsCoveringMap.deckMulEquivOfRangeEq`: consequently their deck transformation groups
  are isomorphic.
* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace`: uniqueness of the
  universal cover.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8, first bullet: the
correspondence between *pointed* connected covers of `(X, x₀)` and subgroups of `π₁(X, x₀)`. It
consumes the lifting criterion recorded in Stage 2, item 6
(`TauCeti.Topology.Homotopy.Covering`), and the recovered-subgroup API of
`TauCeti.Topology.Homotopy.Monodromy`. No Mathlib infrastructure is vendored: the lifting
criterion `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` is Junyan Xu's, in
`Mathlib.Topology.Homotopy.Lifting`, while the uniqueness of lifts
`IsCoveringMap.eq_of_comp_eq` is Thomas Browning's, in `Mathlib.Topology.Covering.Basic`, where
it is recorded as Proposition 1.34 of [hatcher02].
-/

public section

namespace TauCeti

open _root_.FundamentalGroup

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {x : X} {e₀ : E} {f₀ : F}

/-- The lifting criterion for pointed covers: if the subgroup recovered by `(p, e₀)` is contained
in the subgroup recovered by the covering `(q, f₀)`, then there is a unique continuous map
`E → F` over `X` carrying `e₀` to `f₀`.

Only continuity is required of `p`; the covering hypothesis is needed for the target `q`. -/
theorem IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : Continuous p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x)
    (hle : (mapOfEq ⟨p, hp⟩ hpe).range ≤ (mapOfEq ⟨q, hq.continuous⟩ hqf).range) :
    ∃! g : C(E, F), g e₀ = f₀ ∧ q ∘ g = p := by
  subst hpe
  rw [TauCeti.FundamentalGroup.mapOfEq_rfl] at hle
  exact hq.existsUnique_continuousMap_lifts_of_range_le (f := ⟨p, hp⟩) hqf hle

/-- A map of pointed covers over `X` exists exactly when the subgroup recovered by the source is
contained in the subgroup recovered by the target.

The forward implication is functoriality of `π₁` and needs no hypothesis on `p` or `q` beyond
continuity; the reverse implication is the lifting criterion. -/
theorem IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (hp : Continuous p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x) :
    (∃ g : C(E, F), g e₀ = f₀ ∧ q ∘ g = p) ↔
      (mapOfEq ⟨p, hp⟩ hpe).range ≤ (mapOfEq ⟨q, hq.continuous⟩ hqf).range := by
  constructor
  · rintro ⟨g, hg, hcomp⟩
    have hfg : (⟨q, hq.continuous⟩ : C(F, X)).comp g = ⟨p, hp⟩ := by
      ext e
      exact congrFun hcomp e
    rintro _ ⟨γ, rfl⟩
    refine ⟨mapOfEq g hg γ, ?_⟩
    rw [TauCeti.FundamentalGroup.mapOfEq_comp ⟨q, hq.continuous⟩ g hg hqf]
    exact TauCeti.FundamentalGroup.mapOfEq_congr hfg _ _ γ
  · intro hle
    exact (IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le hp hq hpe hqf hle).exists

/-- Two pointed covers of `(X, x)` with path-connected, locally path-connected total spaces which
recover the *same* subgroup of `π₁(X, x)` are isomorphic over `X`, by a homeomorphism matching the
chosen lifts. -/
theorem IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x)
    (hrange : (mapOfEq ⟨p, hp.continuous⟩ hpe).range = (mapOfEq ⟨q, hq.continuous⟩ hqf).range) :
    ∃ h : E ≃ₜ F, h e₀ = f₀ ∧ q ∘ h = p := by
  obtain ⟨g, ⟨hg₀, hgc⟩, -⟩ :=
    IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le hp.continuous hq hpe hqf hrange.le
  obtain ⟨k, ⟨hk₀, hkc⟩, -⟩ :=
    IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le hq.continuous hp hqf hpe hrange.ge
  have hkg : ∀ e, k (g e) = e := by
    have hcomp : (p ∘ fun e => k (g e)) = p ∘ id := by
      funext e
      exact (congrFun hkc (g e)).trans (congrFun hgc e)
    have hbase : (fun e => k (g e)) e₀ = id e₀ := by
      simp only [id_eq, hg₀, hk₀]
    exact congrFun
      (hp.eq_of_comp_eq (k.continuous.comp g.continuous) continuous_id hcomp e₀ hbase)
  have hgk : ∀ f, g (k f) = f := by
    have hcomp : (q ∘ fun f => g (k f)) = q ∘ id := by
      funext f
      exact (congrFun hgc (k f)).trans (congrFun hkc f)
    have hbase : (fun f => g (k f)) f₀ = id f₀ := by
      simp only [id_eq, hk₀, hg₀]
    exact congrFun
      (hq.eq_of_comp_eq (g.continuous.comp k.continuous) continuous_id hcomp f₀ hbase)
  exact ⟨⟨⟨⇑g, ⇑k, hkg, hgk⟩, g.continuous, k.continuous⟩, hg₀, hgc⟩

/-- **Pointed connected covers are classified by the subgroup they recover.** Two pointed covers
with path-connected, locally path-connected total spaces are isomorphic over `X`, by a
homeomorphism matching the chosen lifts, exactly when they recover the same subgroup of
`π₁(X, x)`. -/
theorem IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x) :
    (∃ h : E ≃ₜ F, h e₀ = f₀ ∧ q ∘ h = p) ↔
      (mapOfEq ⟨p, hp.continuous⟩ hpe).range = (mapOfEq ⟨q, hq.continuous⟩ hqf).range := by
  refine ⟨fun ⟨h, hh₀, hhc⟩ => le_antisymm ?_ ?_, fun hrange =>
    IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe hqf hrange⟩
  · exact (IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le hp.continuous hq hpe hqf).mp
      ⟨(h : C(E, F)), hh₀, hhc⟩
  · refine (IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le hq.continuous hp hqf hpe).mp
      ⟨(h.symm : C(F, E)), h.symm_apply_eq.mpr hh₀.symm, ?_⟩
    funext f
    simpa only [Function.comp_apply, ContinuousMap.coe_coe, Homeomorph.apply_symm_apply]
      using (congrFun hhc (h.symm f)).symm

/-- The homeomorphism over `X` between two pointed covers recovering the same subgroup of
`π₁(X, x)`, matching the chosen lifts of `x`. -/
noncomputable def IsCoveringMap.totalSpaceHomeomorphOfRangeEq
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x)
    (hrange : (mapOfEq ⟨p, hp.continuous⟩ hpe).range = (mapOfEq ⟨q, hq.continuous⟩ hqf).range) :
    E ≃ₜ F :=
  (IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe hqf hrange).choose

section

variable [PathConnectedSpace E] [LocallyPathConnectedSpace E]
  [PathConnectedSpace F] [LocallyPathConnectedSpace F]
  (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x)
  (hrange : (mapOfEq ⟨p, hp.continuous⟩ hpe).range = (mapOfEq ⟨q, hq.continuous⟩ hqf).range)

/-- The comparison homeomorphism carries the chosen lift of `x` in `E` to the chosen lift in
`F`. -/
@[simp]
theorem IsCoveringMap.totalSpaceHomeomorphOfRangeEq_apply_basepoint :
    IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange e₀ = f₀ :=
  (IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe hqf hrange).choose_spec.1

/-- The comparison homeomorphism lies over the base. -/
@[simp]
theorem IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq :
    q ∘ IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange = p :=
  (IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe hqf hrange).choose_spec.2

/-- The comparison homeomorphism lies over the base, pointwise.

Not a `simp` lemma: its left-hand side `q (h e)` has the variable `q` as head symbol, so Lean
rejects it as a global `simp` lemma. -/
theorem IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_apply (e : E) :
    q (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange e) = p e :=
  congrFun (IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange) e

/-- The comparison homeomorphism is characterised by the two properties defining it: it is the
*only* continuous map `E → F` over `X` carrying the chosen lift of `x` in `E` to the chosen lift
in `F`. -/
theorem IsCoveringMap.eq_totalSpaceHomeomorphOfRangeEq {g : C(E, F)} (hg₀ : g e₀ = f₀)
    (hgc : q ∘ g = p) :
    g = (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange : C(E, F)) := by
  obtain ⟨g₁, -, huniq⟩ := IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le
    hp.continuous hq hpe hqf hrange.le
  refine (huniq g ⟨hg₀, hgc⟩).trans (huniq _ ⟨?_, ?_⟩).symm
  · exact IsCoveringMap.totalSpaceHomeomorphOfRangeEq_apply_basepoint hp hq hpe hqf hrange
  · exact IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange

/-- The inverse of the comparison homeomorphism carries the chosen lift of `x` in `F` back to the
chosen lift in `E`. -/
@[simp]
theorem IsCoveringMap.totalSpaceHomeomorphOfRangeEq_symm_apply_basepoint :
    (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange).symm f₀ = e₀ := by
  rw [Homeomorph.symm_apply_eq]
  exact (IsCoveringMap.totalSpaceHomeomorphOfRangeEq_apply_basepoint hp hq hpe hqf hrange).symm

/-- The inverse of the comparison homeomorphism also lies over the base. Not a `simp` lemma, for
the same variable-head reason as `comp_totalSpaceHomeomorphOfRangeEq_apply`. -/
theorem IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_symm_apply (f : F) :
    p ((IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange).symm f) = q f := by
  rw [← IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_apply hp hq hpe hqf hrange,
    Homeomorph.apply_symm_apply]

/-- Pointed covers recovering the same subgroup of `π₁(X, x)` have isomorphic deck transformation
groups, by conjugation along the comparison homeomorphism. -/
noncomputable def IsCoveringMap.deckMulEquivOfRangeEq : Deck p ≃* Deck q :=
  Deck.conjMulEquiv (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange)
    (IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_apply hp hq hpe hqf hrange)

/-- The deck-group isomorphism attached to two pointed covers with the same recovered subgroup is
conjugation by the comparison homeomorphism. -/
@[simp]
theorem IsCoveringMap.deckMulEquivOfRangeEq_apply_coe (φ : Deck p) (f : F) :
    ((IsCoveringMap.deckMulEquivOfRangeEq hp hq hpe hqf hrange φ).1 f) =
      IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange
        (φ.1 ((IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange).symm f)) :=
  Deck.conjMulEquiv_apply_coe _ _ φ f

/-- The inverse of that deck-group isomorphism is conjugation by the inverse comparison
homeomorphism. -/
@[simp]
theorem IsCoveringMap.deckMulEquivOfRangeEq_symm_apply_coe (ψ : Deck q) (e : E) :
    (((IsCoveringMap.deckMulEquivOfRangeEq hp hq hpe hqf hrange).symm ψ).1 e) =
      (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange).symm
        (ψ.1 (IsCoveringMap.totalSpaceHomeomorphOfRangeEq hp hq hpe hqf hrange e)) :=
  Deck.conjMulEquiv_symm_apply_coe _ _ ψ e

end

/-- **Uniqueness of the universal cover.** Any two simply connected, locally path-connected covers
of `X` are isomorphic over `X`, by a homeomorphism matching chosen lifts of a basepoint.

Both recovered subgroups are trivial, so the classification of pointed covers applies. -/
theorem IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x) :
    ∃ h : E ≃ₜ F, h e₀ = f₀ ∧ q ∘ h = p :=
  IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe hqf <| by
    rw [TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton,
      TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton]

end TauCeti
