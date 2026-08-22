/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant functions on a compact group are uniformly locally constant

A locally constant function `f : G → A` on a topological group is constant near each point, but
the neighbourhood on which it is constant depends on the point. On a *compact* group the
dependence disappears: there is a single open subgroup `V` with `f (x * v) = f x` for **every**
`x : G` and every `v : V`. This file records that subgroup,
`TauCeti.rightTranslationStabilizer f`, and its openness,
`TauCeti.isOpen_rightTranslationStabilizer`.

The proof is the tube lemma. The set of pairs `(x, g)` with `f (x * g) = f x` is open, because it
is the locus where two locally constant functions of `(x, g)` agree, and it contains `G × {1}`;
compactness of `G` produces a single open `V ∋ 1` that works for every `x` at once. Being a
subgroup that is a neighbourhood of `1`, the stabilizer is then open.

Compactness is the hypothesis the tube lemma consumes, and it is what turns "for each `x` there
is a neighbourhood of `1`" into "there is a neighbourhood of `1` that works for every `x`". Nothing
weaker is claimed here: for a non-compact `G` the argument produces a neighbourhood depending on
`x` and no uniform one, and no statement below asserts anything in that case.

This is the "uniform local constancy" milestone of Layer 7 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`: it is what makes the coinduced module of locally
constant equivariant maps a *discrete* `G`-module, its right-translation stabilizers being open.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {A : Type*}

/-- The **right-translation stabilizer** of `f : G → A`: the subgroup of those `g` with
`f (x * g) = f x` for every `x : G`. For a locally constant `f` on a compact group it is open
(`TauCeti.isOpen_rightTranslationStabilizer`), which is the sense in which `f` is *uniformly*
locally constant. -/
def rightTranslationStabilizer (f : G → A) : Subgroup G where
  carrier := {g | ∀ x : G, f (x * g) = f x}
  one_mem' x := by rw [mul_one]
  mul_mem' {g g'} hg hg' x := by rw [← mul_assoc, hg' (x * g), hg x]
  inv_mem' {g} hg x := by rw [← hg (x * g⁻¹), inv_mul_cancel_right]

@[simp]
theorem mem_rightTranslationStabilizer {f : G → A} {g : G} :
    g ∈ rightTranslationStabilizer f ↔ ∀ x : G, f (x * g) = f x := Iff.rfl

/-- A locally constant function on a compact topological group is *uniformly* locally constant:
its right-translation stabilizer is an open subgroup, so a single open neighbourhood of `1` makes
`f (x * g) = f x` hold for every `x` simultaneously. -/
theorem isOpen_rightTranslationStabilizer [TopologicalSpace G] [ContinuousMul G]
    [CompactSpace G] {f : G → A} (hf : IsLocallyConstant f) :
    IsOpen (rightTranslationStabilizer f : Set G) := by
  -- the locus where the two locally constant functions `(x, g) ↦ f (x * g)` and `(x, g) ↦ f x`
  -- agree is open, and it contains the tube `G × {1}`
  have hmul : IsLocallyConstant fun p : G × G => f (p.1 * p.2) :=
    hf.comp_continuous continuous_mul
  have hfst : IsLocallyConstant fun p : G × G => f p.1 := hf.comp_continuous continuous_fst
  have hopen : IsOpen {p : G × G | f (p.1 * p.2) = f p.1} :=
    (hmul.prodMk hfst) {q : A × A | q.1 = q.2}
  obtain ⟨u, v, -, hvopen, hsu, hv1, huv⟩ :=
    generalized_tube_lemma (isCompact_univ (X := G)) (isCompact_singleton (x := (1 : G))) hopen
      fun p hp => by
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff.mp hp.2, mul_one]
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    (hvopen.mem_nhds (hv1 rfl)) fun g hg x => ?_)
  exact huv (Set.mk_mem_prod (hsu (Set.mem_univ x)) hg)

end TauCeti
