/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree

/-!
# Formations and their finite normal layers

Artin and Tate describe a *formation* by a group `G`, a distinguished family of finite-index
subgroups, and a `G`-module `A` each of whose elements is fixed by a sufficiently small member of
the family. In the arithmetic applications the family is the family of open subgroups of a
profinite Galois group and `A` is a discrete continuous module, so this file uses the equivalent
topological formulation: a `Formation` is a smooth discrete topological representation of `G` over
`ℤ`, and its `U`-**level** `A^U` is the submodule fixed by an open subgroup `U`.

A **finite normal layer** is a pair of open subgroups `V ≤ U` with `V` normal in `U`. In field
notation it is the layer `K/F` with `U = G_F` and `V = G_K`. Its Galois group `Γ = U ⧸ V` is
finite because `V` is open in the compact group `U`, its coefficient module is the level `A^V`,
and its ground level is `A^U`. The three constructions below are what the cohomology of the layer
is taken of and compared with:

* `rep`, the coefficient module `A^V` carrying the action of `Γ`. The `U`-action on `A^V` is well
  defined because `V` is normal in `U`, and `V` acts on `A^V` trivially, so the action descends to
  `Γ`.
* `groundLevelEquiv`, the identification `(A^V)^Γ = A^U` of the invariants of the coefficient
  module with the ground level. Both are submodules of the ambient module of the formation, and
  the identification does not move an element.
* `norm`, `normSubgroup` and `NormQuotient`: the norm `N_{U/V} : A^V → A^U`, its image, and the
  quotient `A^U / N_{U/V}(A^V)`.

The additive convention is used throughout, as in the abstract theory; a multiplicative group such
as `Kˣ` enters through an `Additive` adapter.

## Main definitions

* `TauCeti.ClassFieldTheory.Formation`: a profinite group's smooth discrete integral coefficient
  module.
* `TauCeti.ClassFieldTheory.Formation.level`: the level `A^U` of an open subgroup.
* `TauCeti.ClassFieldTheory.NormalLayer`: a finite normal layer `V ◁ U`.
* `TauCeti.ClassFieldTheory.NormalLayer.Gal`, `degree`: the Galois group `U ⧸ V` and its order.
* `TauCeti.ClassFieldTheory.NormalLayer.ofOpenNormal`: the layer `V ◁ ⊤` of an open normal
  subgroup, with `galOfOpenNormalEquiv` identifying its Galois group with `G ⧸ V`.
* `TauCeti.ClassFieldTheory.NormalLayer.rep`: the coefficient module `A^V` of the layer, as a
  representation of `U ⧸ V`.
* `TauCeti.ClassFieldTheory.NormalLayer.H`, `TateH`, `TrivialTateH`: the ordinary and Tate
  cohomology carriers of the layer, in the coefficient module `A^V` and in trivial integral
  coefficients.
* `TauCeti.ClassFieldTheory.NormalLayer.norm`, `normSubgroup`, `NormQuotient`, `normQuotientMk`:
  the norm of the layer, its image, the norm quotient and the quotient map onto it.

## Main statements

* `TauCeti.ClassFieldTheory.Formation.exists_mem_level`: every element of the coefficient module
  is fixed by an open subgroup.
* `TauCeti.ClassFieldTheory.NormalLayer.groundLevelEquiv`: `(A^V)^{U/V} ≃ A^U`.
* `TauCeti.ClassFieldTheory.NormalLayer.tateHZeroEquivNormQuotient`: degree-zero Tate cohomology
  of the layer is the norm quotient.

## Implementation notes

The coefficient module is built as `Representation.ofQuotient` of a
`Representation.subrepresentation`, so that its underlying module is *definitionally* the level
`A^V`. Mathlib's packaged `Rep.quotientToInvariants` would instead produce the invariants of the
restriction of `A` along `V ∩ U → U → G`, which is the same submodule of the ambient module but
not the same term as `A^V`, and every later comparison would have to transport along that equality.

The group `G` is profinite — a compact, totally disconnected topological group — and both
`Formation` and `NormalLayer` carry those hypotheses. They are what makes the family of open
subgroups the distinguished family of the Artin–Tate definition, with the open subgroups a
neighbourhood basis of `1`, and what makes the Galois group of every layer finite, so that the
`degree` of a layer is its genuine index and not the junk value `0` of an infinite quotient.

Both the group and the coefficient module live in `Type`. Mathlib's `tateCohomology` asks for the
finite group and the coefficient ring `ℤ` in one universe and for the coefficient module in that
same universe, and every carrier of the arithmetic instances is a `Type`, so nothing is lost.

The coefficient module is read as a plain `Rep ℤ G` through `Representation.ofDistribMulAction` at
the action `TauCeti.TopRep.distribMulAction` derives from the operators of the topological
representation. Passing instead through `ContRepresentation.toRepresentation` would carry the
`Module ℤ` instance packaged inside `TopRep`, which is not the instance `AddCommGroup.toIntModule`
that typeclass synthesis produces for an integral module, and the two are not definitionally
equal.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV.
* J. Neukirch, *Class Field Theory*, Chapter III.
* J.-P. Serre, *Local Fields*, Chapter XI.
* `Suggested.lean` of the TauCeti `ClassFieldTheory` roadmap, the blueprint whose signatures for
  the two structures below and for the level, layer representation and norm constructions this
  file follows.
-/

public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Formations and their levels -/

/-- A **formation**: a smooth discrete continuous integral representation of a profinite group.
In the arithmetic applications `G` is the Galois group of a Galois extension and the module is the
multiplicative group of the top field, read additively. The distinguished family of subgroups of
the Artin–Tate definition is the family of open subgroups of `G`, which is why the levels below
are indexed by `OpenSubgroup G`. -/
structure Formation (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] where
  /-- the coefficient module of the formation, a topological representation of `G` over `ℤ` -/
  module : TopRep.{0} ℤ G
  /-- the coefficient module is discrete with open point stabilizers, so that every element is
  fixed by an open subgroup -/
  smooth : IsSmoothDiscrete ℤ module

namespace Formation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (F : Formation G)

/-- The coefficient module of a formation as a plain integral representation of `G`, forgetting
its topology. The levels, the layer representations and all of their cohomology are taken of this
underlying representation. -/
abbrev toRep : Rep ℤ G := Rep.of (Representation.ofDistribMulAction ℤ G F.module.V)

theorem toRep_ρ_apply (g : G) (x : F.toRep.V) : F.toRep.ρ g x = F.module.ρ g x :=
  (rfl)

/-- The **level** `A^U` of an open subgroup `U`, as a submodule of the ambient module of the
formation. Keeping every level inside one ambient module is what makes the inclusion of a level in
a smaller subgroup's level, and the norm between two levels, maps of submodules of a fixed
module. -/
def level (U : OpenSubgroup G) : Submodule ℤ F.toRep.V :=
  invariants (F.toRep.ρ.comp U.toSubgroup.subtype)

@[simp]
theorem mem_level {U : OpenSubgroup G} {x : F.toRep.V} :
    x ∈ F.level U ↔ ∀ u ∈ U, F.toRep.ρ u x = x :=
  ⟨fun hx u hu ↦ hx ⟨u, hu⟩, fun hx u ↦ hx u u.2⟩

/-- **Every element of the coefficient module lies in a level.** This is the Artin–Tate condition
that each element of `A` is fixed by a sufficiently small member of the distinguished family of
subgroups, and it is exactly what smoothness of the module supplies: the stabilizer of an element
is open. -/
theorem exists_mem_level (x : F.toRep.V) : ∃ U : OpenSubgroup G, x ∈ F.level U :=
  ⟨⟨MulAction.stabilizer G x, F.smooth.stabilizer_isOpen x⟩, F.mem_level.2 fun _ hu ↦ hu⟩

/-- Levels decrease as the subgroup grows: a larger subgroup fixes fewer elements. -/
theorem level_antitone : Antitone F.level := by
  intro U U' hUU' x hx
  rw [mem_level] at hx ⊢
  exact fun u hu ↦ hx u (hUU' hu)

end Formation

/-! ### Finite normal layers -/

/-- A **finite normal layer** `V ◁ U` of open subgroups of `G`. In field notation this is the
finite Galois layer `K/F` inside the extension `G` cuts out, with `U = G_F` the ground subgroup and
`V = G_K` the top subgroup. -/
structure NormalLayer (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] where
  /-- the ground subgroup `U`, cutting out the base field of the layer -/
  ground : OpenSubgroup G
  /-- the top subgroup `V`, cutting out the top field of the layer -/
  top : OpenSubgroup G
  /-- the layer runs upwards: `V ≤ U` -/
  top_le_ground : top ≤ ground
  /-- `V` is normal in `U`, so that the layer is Galois -/
  normal : (top.toSubgroup.subgroupOf ground.toSubgroup).Normal

namespace NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G)

/-- The top subgroup `V` of a layer, viewed as a subgroup of the ground subgroup `U`. -/
abbrev relativeTop : Subgroup L.ground := L.top.toSubgroup.subgroupOf L.ground.toSubgroup

instance : L.relativeTop.Normal := L.normal

/-- The Galois group `Γ = U ⧸ V` of a finite normal layer. -/
abbrev Gal : Type := L.ground ⧸ L.relativeTop

/-- The top subgroup of a layer is normal in the ground subgroup, read on elements of `G`. -/
theorem conj_mem_top {u : G} (hu : u ∈ L.ground) {v : G} (hv : v ∈ L.top) :
    u * v * u⁻¹ ∈ L.top :=
  Subgroup.mem_subgroupOf.1
    (L.normal.conj_mem ⟨v, L.top_le_ground hv⟩ (Subgroup.mem_subgroupOf.2 hv) ⟨u, hu⟩)

/-- The **degree** `[U : V]` of a normal layer, the index of the top subgroup in the ground
subgroup. -/
def degree : ℕ := L.relativeTop.index

theorem degree_eq_natCard_gal : L.degree = Nat.card L.Gal :=
  (rfl)

/-- The layer `V ◁ ⊤` cut out by an open normal subgroup of `G`. These layers are the finite
Galois extensions of the ground field of a formation on `G`. -/
def ofOpenNormal (V : OpenSubgroup G) [V.toSubgroup.Normal] : NormalLayer G where
  ground := ⊤
  top := V
  top_le_ground := le_top
  normal := Subgroup.normal_subgroupOf

@[simp]
theorem ground_ofOpenNormal (V : OpenSubgroup G) [V.toSubgroup.Normal] :
    (ofOpenNormal V).ground = ⊤ :=
  (rfl)

@[simp]
theorem top_ofOpenNormal (V : OpenSubgroup G) [V.toSubgroup.Normal] :
    (ofOpenNormal V).top = V :=
  (rfl)

/-- The Galois group of the layer `V ◁ ⊤` is the finite quotient `G ⧸ V`. -/
def galOfOpenNormalEquiv (V : OpenSubgroup G) [V.toSubgroup.Normal] :
    (ofOpenNormal V).Gal ≃* G ⧸ V.toSubgroup :=
  QuotientGroup.congr _ _ Subgroup.topEquiv <| by
    ext x
    simp only [Subgroup.mem_map]
    exact ⟨fun ⟨_, ha, h⟩ ↦ h ▸ ha, fun hx ↦ ⟨⟨x, trivial⟩, hx, rfl⟩⟩

@[simp]
theorem galOfOpenNormalEquiv_mk (V : OpenSubgroup G) [V.toSubgroup.Normal]
    (u : (ofOpenNormal V).ground) :
    galOfOpenNormalEquiv V (QuotientGroup.mk u) = QuotientGroup.mk (u : G) :=
  (rfl)

section Finite

/-- The top subgroup is open in the compact ground subgroup, so the Galois group is finite. -/
instance instFiniteGal : Finite L.Gal :=
  Subgroup.quotient_finite_of_isOpen' L.ground.toSubgroup L.relativeTop L.ground.isOpen
    (L.ground.toSubgroup.subgroupOf_isOpen L.top.toSubgroup L.top.isOpen)

instance instFintypeGal : Fintype L.Gal := Fintype.ofFinite _

theorem degree_pos : 0 < L.degree :=
  L.degree_eq_natCard_gal ▸ Nat.card_pos

end Finite

/-! ### The coefficient module of a layer -/

section Coefficients

variable (F : Formation G)

/-- The ground subgroup carries the top level into itself: this is exactly normality of `V` in
`U`. -/
theorem level_top_le_comap (u : L.ground) :
    F.level L.top ≤ (F.level L.top).comap (F.toRep.ρ (u : G)) := by
  intro x hx
  rw [Submodule.mem_comap, Formation.mem_level]
  intro v hv
  have hconj : (u : G)⁻¹ * v * (u : G) ∈ L.top := by
    simpa using L.conj_mem_top (L.ground.toSubgroup.inv_mem u.2) hv
  have hvu : v * (u : G) = (u : G) * ((u : G)⁻¹ * v * (u : G)) := by group
  calc F.toRep.ρ v (F.toRep.ρ (u : G) x)
      = F.toRep.ρ (v * (u : G)) x := by rw [map_mul, Module.End.mul_apply]
    _ = F.toRep.ρ (u : G) (F.toRep.ρ ((u : G)⁻¹ * v * (u : G)) x) := by
        rw [hvu, map_mul, Module.End.mul_apply]
    _ = F.toRep.ρ (u : G) x := by rw [(F.mem_level.1 hx) _ hconj]

/-- The action of the ground subgroup `U` on the top level `A^V`. -/
abbrev groundRep : Representation ℤ L.ground (F.level L.top) :=
  .subrepresentation (F.toRep.ρ.comp L.ground.toSubgroup.subtype) _ (L.level_top_le_comap F)

@[simp]
theorem groundRep_apply_coe (u : L.ground) (x : F.level L.top) :
    ((L.groundRep F u x : F.level L.top) : F.toRep.V) = F.toRep.ρ (u : G) x :=
  (rfl)

/-- The top subgroup acts trivially on the top level, so the `U`-action descends to `U ⧸ V`. -/
instance : Representation.IsTrivial ((L.groundRep F).comp L.relativeTop.subtype) where
  out s := by
    ext x
    exact (F.mem_level.1 x.2) _ (Subgroup.mem_subgroupOf.1 s.2)

/-- The **coefficient module of a layer**: the top level `A^V` with the induced action of the
Galois group `U ⧸ V`. Its underlying module is the level itself, not an isomorphic copy. -/
abbrev rep : Rep ℤ L.Gal := Rep.of ((L.groundRep F).ofQuotient L.relativeTop)

theorem rep_ρ_mk_apply_coe (u : L.ground) (x : F.level L.top) :
    (((L.rep F).ρ (u : L.Gal) x : F.level L.top) : F.toRep.V) = F.toRep.ρ (u : G) x :=
  (rfl)

/-- The ground level sits inside the top level. -/
theorem level_ground_le_level_top : F.level L.ground ≤ F.level L.top :=
  F.level_antitone L.top_le_ground

/-- **The invariants of the coefficient module are the ground level:** `(A^V)^{U/V} = A^U`. Both
sides are read inside the top level `A^V`. -/
theorem invariants_rep :
    (L.rep F).ρ.invariants = (F.level L.ground).comap (F.level L.top).subtype := by
  ext x
  rw [Representation.mem_invariants, Submodule.mem_comap, Submodule.subtype_apply,
    Formation.mem_level]
  constructor
  · intro hx u hu
    exact congrArg Subtype.val (hx (QuotientGroup.mk (⟨u, hu⟩ : L.ground)))
  · intro hx γ
    induction γ using QuotientGroup.induction_on with
    | H u => exact Subtype.ext (hx u u.2)

/-- The identification `(A^V)^{U/V} ≃ A^U` of the invariants of the coefficient module with the
ground level. It moves no element of the ambient module. -/
def groundLevelEquiv : (L.rep F).ρ.invariants ≃ₗ[ℤ] F.level L.ground :=
  (LinearEquiv.ofEq _ _ (L.invariants_rep F)).trans
    (Submodule.comapSubtypeEquivOfLe (L.level_ground_le_level_top F))

@[simp]
theorem groundLevelEquiv_apply_coe (x : (L.rep F).ρ.invariants) :
    ((L.groundLevelEquiv F x : F.level L.ground) : F.toRep.V) = ((x : F.level L.top) :
      F.toRep.V) :=
  (rfl)

@[simp]
theorem groundLevelEquiv_symm_apply_coe (y : F.level L.ground) :
    ((((L.groundLevelEquiv F).symm y : (L.rep F).ρ.invariants) : F.level L.top) : F.toRep.V) =
      (y : F.toRep.V) :=
  (rfl)

end Coefficients

/-! ### The cohomology of a layer -/

section Cohomology

variable (F : Formation G)

/-- **Ordinary group cohomology of a finite normal layer**, `H^n(U/V, A^V)`, on Mathlib's carrier.
The axioms satisfied by a class formation and the fundamental class of a layer are read here. -/
abbrev H (n : ℕ) : ModuleCat ℤ := groupCohomology (L.rep F) n

/-- **Tate cohomology of a finite normal layer** in its coefficient module, the Tate group
`H^r(U/V, A^V)` in every integer degree `r`. -/
abbrev TateH (r : ℤ) : ModuleCat ℤ := tateCohomology (L.rep F) r

/-- **Tate cohomology of a finite normal layer with trivial integral coefficients**, the Tate
group `H^r(U/V, ℤ)`. Its degree `-2` is the abelianization of the Galois group of the layer, and
the Artin map of a class formation is a cup product between this carrier and `TateH`. -/
abbrev TrivialTateH (r : ℤ) : ModuleCat ℤ := tateCohomology (Rep.trivial ℤ L.Gal ℤ) r

end Cohomology

/-! ### The norm of a layer -/

section Norm

variable (F : Formation G)

/-- The **norm** `N_{U/V} : A^V → A^U` of a finite normal layer: the sum of the Galois conjugates,
landing in the ground level through `groundLevelEquiv`. -/
def norm : F.level L.top →ₗ[ℤ] F.level L.ground :=
  (L.groundLevelEquiv F).toLinearMap ∘ₗ
    (L.rep F).ρ.norm.codRestrict (L.rep F).ρ.invariants fun x ↦
      (Representation.mem_invariants _ _).2 fun g ↦ by
        rw [← LinearMap.comp_apply, Representation.self_comp_norm]

@[simp]
theorem norm_apply_coe (x : F.level L.top) :
    ((L.norm F x : F.level L.ground) : F.toRep.V) =
      ∑ γ : L.Gal, (((L.rep F).ρ γ x : F.level L.top) : F.toRep.V) := by
  -- The identification with the ground level does not move the underlying element, so the norm
  -- of the layer and Mathlib's `Representation.norm` take the same value in the ambient module.
  have h : ((L.norm F x : F.level L.ground) : F.toRep.V)
      = (((L.rep F).ρ.norm x : F.level L.top) : F.toRep.V) := rfl
  rw [h]
  simp [Representation.norm]

/-- The norm of a layer is the trace of the Galois action on the top level, so on an element of
the ground level it is multiplication by the degree. -/
theorem norm_apply_coe_of_mem_level_ground (x : F.level L.top)
    (hx : (x : F.toRep.V) ∈ F.level L.ground) :
    ((L.norm F x : F.level L.ground) : F.toRep.V) = L.degree • (x : F.toRep.V) := by
  have hconst : ∀ γ : L.Gal, (((L.rep F).ρ γ x : F.level L.top) : F.toRep.V) = x := by
    intro γ
    induction γ using QuotientGroup.induction_on with
    | H u => exact (F.mem_level.1 hx) u u.2
  rw [L.norm_apply_coe F x, Finset.sum_congr rfl fun γ _ ↦ hconst γ,
    L.degree_eq_natCard_gal]
  simp [Nat.card_eq_fintype_card]

/-- The **norm subgroup** `N_{U/V}(A^V)` of the ground level. -/
def normSubgroup : Submodule ℤ (F.level L.ground) :=
  LinearMap.range (L.norm F)

@[simp]
theorem mem_normSubgroup {y : F.level L.ground} :
    y ∈ L.normSubgroup F ↔ ∃ x, L.norm F x = y :=
  Iff.rfl

/-- The **norm quotient** `A^U / N_{U/V}(A^V)` of a finite normal layer. It is the group that the
Artin map of a *class formation* — a formation whose layers satisfy the axioms on `H¹` and `H²`,
which a bare `Formation` does not assume — identifies with the abelianization of the Galois group
of the layer. -/
abbrev NormQuotient : Type := F.level L.ground ⧸ L.normSubgroup F

/-- The canonical map from the ground level onto the norm quotient. The Artin map of a class
formation is defined on the ground level by composing with this map. -/
def normQuotientMk : F.level L.ground →ₗ[ℤ] L.NormQuotient F :=
  (L.normSubgroup F).mkQ

@[simp]
theorem normQuotientMk_apply (x : F.level L.ground) :
    L.normQuotientMk F x = Submodule.Quotient.mk x :=
  (rfl)

/-- The image under `groundLevelEquiv` of the norm image inside the invariants is the norm
subgroup. -/
theorem map_groundLevelEquiv_submoduleOf :
    Submodule.map (L.groundLevelEquiv F).toLinearMap
        ((LinearMap.range (L.rep F).ρ.norm).submoduleOf (L.rep F).ρ.invariants) =
      L.normSubgroup F := by
  ext y
  simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
    LinearMap.mem_range, normSubgroup, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, ⟨v, hv⟩, rfl⟩
    refine ⟨v, Subtype.ext ?_⟩
    -- The congruence is bound first: elaborated against the goal, `congrArg` would unify its
    -- arguments with the two sides of the goal instead of with the two sides of `hv`.
    have h := congrArg Subtype.val hv
    exact h
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- **Degree-zero Tate cohomology of a finite normal layer is its norm quotient.** This is the
low-degree identification that the Artin map of a class formation is read through. -/
def tateHZeroEquivNormQuotient :
    L.TateH F 0 ≅ ModuleCat.of ℤ (L.NormQuotient F) :=
  TateCohomology.H0IsoNormQuotient (L.rep F) ≪≫
    (Submodule.Quotient.equiv _ _ (L.groundLevelEquiv F)
      (L.map_groundLevelEquiv_submoduleOf F)).toModuleIso

/-- The identification of degree-zero Tate cohomology with the norm quotient sends the class of an
invariant to the class of the corresponding element of the ground level. -/
@[simp]
theorem tateHZeroEquivNormQuotient_hom_H0π (x : (L.rep F).ρ.invariants) :
    (L.tateHZeroEquivNormQuotient F).hom (TateCohomology.H0π (L.rep F) x) =
      L.normQuotientMk F (L.groundLevelEquiv F x) := by
  -- The elementwise form of the low-degree identification is bound as a hypothesis first, so
  -- that it is normalised to the application form the goal uses before it rewrites.
  have h := TateCohomology.H0π_comp_H0IsoNormQuotient_hom_apply (L.rep F) x
  simp [tateHZeroEquivNormQuotient, normQuotientMk, h]

end Norm

end NormalLayer

end TauCeti.ClassFieldTheory
