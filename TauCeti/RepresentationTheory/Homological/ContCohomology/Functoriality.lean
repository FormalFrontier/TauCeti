/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

import Mathlib.Tactic.Group

/-!
# Restriction, inflation and coefficient maps for continuous cohomology

Mathlib's `ContinuousCohomology.map` sends a *compatible pair* — a continuous homomorphism
`φ : H →ₜ* G` together with a morphism `f : TopRep.res φ X ⟶ Y` of topological
`H`-representations — to a map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)`. Three instances of that pair carry all the
change-of-group maps of the continuous cohomology of a topological group, and this file names them:

* `TauCeti.ContinuousCohomology.res`, for `φ` the inclusion of a subgroup with the subspace
  topology and `f` the identity;
* `TauCeti.ContinuousCohomology.infl`, for `φ` the quotient map by a normal subgroup and `f` the
  inclusion of the invariants;
* `TauCeti.ContinuousCohomology.coeffMap`, for `φ` the identity and `f` arbitrary.

Inflation needs a coefficient object that Mathlib supplies only on the discrete side: for a normal
subgroup `N ≤ G`, the `N`-invariants of a topological `G`-representation `X`, carrying the induced
action of `G ⧸ N`. That object is `TauCeti.quotientToInvariants`, the topological twin of Mathlib's
`Rep.quotientToInvariants`. It is functorial in `X` (`TauCeti.quotientToInvariantsFunctor`) and
comes with the `G`-equivariant inclusion `TauCeti.quotientToInvariantsι` into `X`, which is the
coefficient half of the inflation pair.

Each of the three maps carries its composition law: `coeffMap` is functorial in the coefficient
morphism (`coeffMap_id`, `coeffMap_comp`), and `res` and `infl` are natural in the coefficients
(`coeffMap_comp_res`, `coeffMap_comp_infl`).

This implements the "three named instances" milestone of Layer 1 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`. No new cohomology theory is introduced: every map
below is Mathlib's `ContinuousCohomology.map` at a named compatible pair, and the identity and
composition laws are derived from Mathlib's `ContinuousCohomology.map_id` and `map_comp`.

## Implementation notes

The coefficient constructions are reducible, matching Mathlib's `Rep.quotientToInvariants` and
`TopRep.invariants`: the underlying module of `quotientToInvariants N X` is a submodule of `X`, and
consumers compute with its elements.

No profiniteness, openness or closedness hypothesis appears in this file. Restriction is defined
for an arbitrary subgroup and inflation for an arbitrary normal subgroup; the topological
hypotheses of the later layers enter when these maps are compared with the explicit cochain model,
not when they are defined.
-/

@[expose] public section

open CategoryTheory ContRepresentation

namespace TauCeti

universe u w

/-! ### The invariants of a normal subgroup as a `G ⧸ N`-representation -/

section Invariants

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `N`-invariants of a topological `G`-representation, as a submodule of `X`. It is the
`ContRepresentation.invariants` of the restriction of `X` to `N`, so that Mathlib's lemmas about
invariants apply to it unchanged. This is the coefficient module of inflation, and the coefficient
system of the tower of finite quotients of a profinite group. -/
abbrev invariantsOf (N : Subgroup G) (X : TopRep R G) : Submodule R X.V :=
  (X.ρ.restrict N.subtype).invariants

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The `N`-invariants are stable under `G` when `N` is normal, because
`n • (g • v) = g • ((g⁻¹ n g) • v)` and `g⁻¹ n g` lies in `N`. -/
lemma map_mem_invariantsOf {N : Subgroup G} [N.Normal] {X : TopRep R G} (g : G) {v : X.V}
    (hv : v ∈ invariantsOf N X) : X.ρ g v ∈ invariantsOf N X := by
  simp only [invariantsOf, ContRepresentation.mem_invariants,
    ContRepresentation.restrict_apply_apply, Subgroup.coe_subtype] at hv ⊢
  intro n
  have hn : g⁻¹ * (n : G) * g ∈ N := Subgroup.Normal.conj_mem' ‹_› (n : G) n.2 g
  have key : (n : G) * g = g * (g⁻¹ * (n : G) * g) := by group
  calc X.ρ (n : G) (X.ρ g v) = X.ρ ((n : G) * g) v := by simp [map_mul]
    _ = X.ρ g (X.ρ (g⁻¹ * (n : G) * g) v) := by simp [key, map_mul]
    _ = X.ρ g v := by rw [hv ⟨_, hn⟩]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A morphism of topological `G`-representations carries `N`-invariants to `N`-invariants. -/
lemma map_mem_invariantsOf_of_hom {N : Subgroup G} {X Y : TopRep R G} (f : X ⟶ Y) {v : X.V}
    (hv : v ∈ invariantsOf N X) : f.hom v ∈ invariantsOf N Y := by
  simp only [invariantsOf, ContRepresentation.mem_invariants,
    ContRepresentation.restrict_apply_apply, Subgroup.coe_subtype] at hv ⊢
  exact fun n ↦ (f.hom.isIntertwining (n : G) v).symm.trans (congrArg (⇑f.hom) (hv n))

variable (N : Subgroup G) [N.Normal] (X : TopRep R G)

/-- The action of `G` on the `N`-invariants of `X`, for `N` normal. It is the restriction of the
action on `X`; the subgroup `N` acts trivially on it, which is what makes it descend to
`G ⧸ N`. -/
def toInvariants : ContRepresentation R G (invariantsOf N X) :=
  .ofMonoidHom
    { toFun g := (X.ρ g).restrict fun _ hv ↦ map_mem_invariantsOf g hv
      map_one' := ContinuousLinearMap.ext fun v ↦ Subtype.ext (by simp)
      map_mul' g h := ContinuousLinearMap.ext fun v ↦ Subtype.ext (by simp) }

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma coe_toInvariants_apply (g : G) (v : invariantsOf N X) :
    ((toInvariants N X g v : invariantsOf N X) : X.V) = X.ρ g v := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The subgroup `N` acts trivially on the `N`-invariants; this is what makes `toInvariants`
descend to `G ⧸ N`. -/
lemma toInvariants_toMonoidHom_eq_one {n : G} (hn : n ∈ N) :
    (toInvariants N X).toMonoidHom n = 1 :=
  ContinuousLinearMap.ext fun v ↦ Subtype.ext (v.2 ⟨n, hn⟩)

/-- The `N`-invariants of a topological `G`-representation `X`, as a topological representation of
`G ⧸ N`. This is the coefficient object of inflation, and the topological twin of Mathlib's
`Rep.quotientToInvariants`. -/
abbrev quotientToInvariants : TopRep R (G ⧸ N) :=
  .of (.ofMonoidHom (QuotientGroup.lift N (toInvariants N X).toMonoidHom
    fun _ hn ↦ toInvariants_toMonoidHom_eq_one N X hn))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma coe_quotientToInvariants_ρ_mk_apply (g : G) (v : invariantsOf N X) :
    (((quotientToInvariants N X).ρ (QuotientGroup.mk g) v : invariantsOf N X) : X.V) =
      X.ρ g v := rfl

variable {X}

/-- The map on `N`-invariants induced by a morphism of topological `G`-representations, as a
morphism of `G ⧸ N`-representations. -/
def quotientToInvariantsMap {Y : TopRep R G} (f : X ⟶ Y) :
    quotientToInvariants N X ⟶ quotientToInvariants N Y :=
  TopRep.ofHom
    { __ := f.hom.toContinuousLinearMap.restrict fun _ hv ↦ map_mem_invariantsOf_of_hom f hv
      isIntertwining' := fun q ↦ QuotientGroup.induction_on q fun g ↦ by
        ext v
        exact f.hom.isIntertwining g v.1 }

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma coe_quotientToInvariantsMap_apply {Y : TopRep R G} (f : X ⟶ Y) (v : invariantsOf N X) :
    ((quotientToInvariantsMap N f v : invariantsOf N Y) : Y.V) = f.hom v := rfl

/-- The functor sending a topological `G`-representation to the `G ⧸ N`-representation on its
`N`-invariants. -/
@[simps]
def quotientToInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj X := quotientToInvariants N X
  map f := quotientToInvariantsMap N f
  map_id X := by ext v; rfl
  map_comp f g := by ext v; rfl

variable (X)

/-- The inclusion of the `N`-invariants into `X`, as a morphism of topological
`G`-representations, where the invariants are regarded as a `G`-representation through
`G → G ⧸ N`. This is the coefficient half of the inflation compatible pair. -/
def quotientToInvariantsι :
    TopRep.res (QuotientGroup.mk'ₜ N : G →* G ⧸ N) (quotientToInvariants N X) ⟶ X :=
  TopRep.ofHom
    { __ := (invariantsOf N X).subtypeL
      isIntertwining' := fun _ ↦ rfl }

omit [IsTopologicalGroup G] in
@[simp]
lemma quotientToInvariantsι_apply (v : invariantsOf N X) :
    (quotientToInvariantsι N X).hom v = (v : X.V) := rfl

variable {X}

omit [IsTopologicalGroup G] in
/-- The inclusion of the `N`-invariants is natural: it is the counit-style comparison between
`quotientToInvariantsFunctor N` and the identity. -/
lemma quotientToInvariantsι_naturality {Y : TopRep R G} (f : X ⟶ Y) :
    (TopRep.resFunctor (QuotientGroup.mk'ₜ N : G →* G ⧸ N)).map (quotientToInvariantsMap N f) ≫
        quotientToInvariantsι N Y =
      quotientToInvariantsι N X ≫ f := by
  ext v
  rfl

end Invariants

/-! ### The three named instances -/

namespace ContinuousCohomology

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max u w} R G}

/-- **Restriction to a subgroup.** The compatible pair is the inclusion of `S`, with the subspace
topology, together with the identity of the restricted representation. No openness or closedness
hypothesis on `S` is needed. -/
noncomputable def res (S : Subgroup G) (X : TopRep.{max u w} R G) (n : ℕ) :
    continuousCohomology n X ⟶
      continuousCohomology n (TopRep.res (S.subtypeₜ : S →* G) X) :=
  _root_.ContinuousCohomology.map S.subtypeₜ (𝟙 _) n

lemma res_def (S : Subgroup G) (X : TopRep.{max u w} R G) (n : ℕ) :
    res S X n = _root_.ContinuousCohomology.map S.subtypeₜ (𝟙 _) n := rfl

/-- **Inflation from a quotient group.** The compatible pair is the projection `G → G ⧸ N`
together with the inclusion of the `N`-invariants into `X`. -/
noncomputable def infl (N : Subgroup G) [N.Normal] (X : TopRep.{max u w} R G) (n : ℕ) :
    continuousCohomology n (quotientToInvariants N X) ⟶ continuousCohomology n X :=
  _root_.ContinuousCohomology.map (QuotientGroup.mk'ₜ N) (quotientToInvariantsι N X) n

lemma infl_def (N : Subgroup G) [N.Normal] (X : TopRep.{max u w} R G) (n : ℕ) :
    infl N X n = _root_.ContinuousCohomology.map (X := quotientToInvariants N X)
      (QuotientGroup.mk'ₜ N) (quotientToInvariantsι N X) n := rfl

/-- **A coefficient map.** The compatible pair is the identity of `G` together with a morphism of
topological `G`-representations. -/
noncomputable def coeffMap (f : X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.id G) f n

lemma coeffMap_def (f : X ⟶ Y) (n : ℕ) :
    coeffMap f n = _root_.ContinuousCohomology.map (ContinuousMonoidHom.id G) f n := rfl

@[simp]
lemma coeffMap_id (X : TopRep.{max u w} R G) (n : ℕ) : coeffMap (𝟙 X) n = 𝟙 _ :=
  _root_.ContinuousCohomology.map_id X n

section Mixed

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {W W' : TopRep.{max u w} R H}

/-- The compatible pair `(φ, f ≫ g)` splits off its coefficient map on the right. -/
@[reassoc]
lemma map_comp_coeffMap (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ W) (g : W ⟶ W')
    (n : ℕ) :
    _root_.ContinuousCohomology.map φ (f ≫ g) n =
      _root_.ContinuousCohomology.map φ f n ≫ coeffMap g n :=
  _root_.ContinuousCohomology.map_comp φ (ContinuousMonoidHom.id H) f g n

/-- A coefficient map on `G` absorbs into a compatible pair on the left. -/
@[reassoc]
lemma coeffMap_comp_map (φ : H →ₜ* G) (f : X ⟶ Y) (g : TopRep.res (φ : H →* G) Y ⟶ W)
    (n : ℕ) :
    coeffMap f n ≫ _root_.ContinuousCohomology.map φ g n =
      _root_.ContinuousCohomology.map φ ((TopRep.resFunctor (φ : H →* G)).map f ≫ g) n :=
  (_root_.ContinuousCohomology.map_comp (ContinuousMonoidHom.id G) φ f g n).symm

end Mixed

@[reassoc]
lemma coeffMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    coeffMap (f ≫ g) n = coeffMap f n ≫ coeffMap g n :=
  map_comp_coeffMap (ContinuousMonoidHom.id G) f g n

/-- **Restriction is natural in the coefficients.** Both sides are `ContinuousCohomology.map` at
the compatible pair `(S.subtypeₜ, (TopRep.resFunctor S.subtypeₜ).map f)`. -/
@[reassoc]
lemma coeffMap_comp_res (S : Subgroup G) (f : X ⟶ Y) (n : ℕ) :
    coeffMap f n ≫ res S Y n =
      res S X n ≫ coeffMap ((TopRep.resFunctor (S.subtypeₜ : S →* G)).map f) n := by
  rw [res_def, res_def, coeffMap_comp_map, ← map_comp_coeffMap, Category.comp_id,
    Category.id_comp]

/-- **Inflation is natural in the coefficients.** Both sides are `ContinuousCohomology.map` at the
compatible pair `(QuotientGroup.mk'ₜ N, quotientToInvariantsι N X ≫ f)`, by
`quotientToInvariantsι_naturality`. -/
@[reassoc]
lemma coeffMap_comp_infl (N : Subgroup G) [N.Normal] (f : X ⟶ Y) (n : ℕ) :
    coeffMap (quotientToInvariantsMap N f) n ≫ infl N Y n = infl N X n ≫ coeffMap f n := by
  rw [infl_def, infl_def, coeffMap_comp_map, quotientToInvariantsι_naturality,
    map_comp_coeffMap]

end ContinuousCohomology

end TauCeti
