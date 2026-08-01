/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.Data.Setoid.Basic

/-!
# Generic orbit-relation quotient helpers

This file records small generic additions to Mathlib's `MulAction.orbitRel.Quotient` API.

## Main declarations

* `TauCeti.MulAction.orbitRelQuotientBotEquiv`: the quotient by the trivial subgroup is the
  original space.
* `TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq_iff`: equality after the bottom-to-`H`
  quotient map is membership in an `H`-orbit.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem`: in a cancellative
  action, two translates have the same `H`-orbit class exactly when the translators differ on
  the right by an element of `H`; this holds for an arbitrary subgroup.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_base_iff`: in a cancellative action, a
  translate has the same `H`-orbit class as the base point exactly when the translator is in
  `H`.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq`: for a
  normal subgroup, equality of two translates in the `H`-orbit quotient is equality of the
  corresponding inverse representatives in `N(H) / H`.
* `TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal`: in a free transitive
  action, the quotient by a normal subgroup is the normalizer quotient `N(H) / H`.
* `TauCeti.MulAction.normalizerOrbitRelQuotientPermHom`: the normalizer action on the
  quotient by `H`-orbits.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotientPermHom`: the descended action of
  `N(H) / H` on the quotient by `H`-orbits.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotientIsPretransitive`: if the normalizer
  acts transitively, then the descended `N(H) / H` action on the `H`-orbit quotient is
  transitive.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff`: if the original
  action is free, then the descended `N(H) / H` action on the `H`-orbit quotient is free.
* `TauCeti.MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk` and
  `TauCeti.MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE`: the representative convention of
  Mathlib's `equivSubgroupOrbitsQuotientGroup` and its naturality in subgroup inclusions.
-/

public section

namespace TauCeti

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

private lemma eq_of_bot_orbitRel {x y : X}
    (h : _root_.MulAction.orbitRel (⊥ : Subgroup G) X x y) : x = y := by
  rw [_root_.MulAction.orbitRel_apply] at h
  rcases h with ⟨g, hg⟩
  have hg_one : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  have hsmul : (g : G) • y = x := by
    simpa [Subgroup.smul_def] using hg
  rw [hg_one, one_smul] at hsmul
  exact hsmul.symm

/-- Quotienting a group action by the trivial subgroup gives back the original space. -/
noncomputable def orbitRelQuotientBotEquiv :
    _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X ≃ X :=
  { toFun := Quotient.lift (fun x : X => x) fun _ _ h => eq_of_bot_orbitRel h
    invFun := Quotient.mk''
    left_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      rfl
    right_inv := by
      intro x
      rfl }

/-- The bottom-subgroup quotient equivalence sends a class to its representative. -/
@[simp]
lemma orbitRelQuotientBotEquiv_mk (x : X) :
    orbitRelQuotientBotEquiv
        (G := G) (X := X) (Quotient.mk'' x :
          _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) = x :=
  (orbitRelQuotientBotEquiv (G := G) (X := X)).right_inv x

/-- The inverse bottom-subgroup quotient equivalence sends a point to its quotient class. -/
@[simp]
lemma orbitRelQuotientBotEquiv_symm_apply (x : X) :
    (orbitRelQuotientBotEquiv (G := G) (X := X)).symm x =
      (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :=
  ((orbitRelQuotientBotEquiv (G := G) (X := X)).apply_eq_iff_eq_symm_apply).mp
    (orbitRelQuotientBotEquiv_mk (G := G) (X := X) x)

/-- Equality of bottom-subgroup orbit classes is equality of representatives. -/
@[simp]
lemma orbitRelQuotientBot_mk_eq_iff (x y : X) :
    (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) =
        Quotient.mk'' y ↔
      x = y := by
  constructor
  · intro h
    exact congrArg (orbitRelQuotientBotEquiv (G := G) (X := X)) h
  · intro h
    rw [h]

/-- Orbit relations are monotone in the acting subgroup. -/
lemma orbitRel_le_of_subgroup_le {H K : Subgroup G} (hHK : H ≤ K) :
    _root_.MulAction.orbitRel H X ≤ _root_.MulAction.orbitRel K X := by
  intro x y h
  rw [_root_.MulAction.orbitRel_apply] at h ⊢
  rcases h with ⟨g, hg⟩
  exact ⟨⟨g.1, hHK g.2⟩, hg⟩

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma orbitRelQuotientMapOfLE_bot_eq (H : Subgroup G) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) =
      (fun x : X => (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X)) ∘
        orbitRelQuotientBotEquiv (G := G) (X := X) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

/-- Equality in an `H`-orbit quotient can be checked after choosing representatives through
the bottom-subgroup quotient. -/
lemma orbitRelQuotientMapOfLE_bot_eq_iff (H : Subgroup G)
    (x y : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) x =
        Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
          (bot_le : (⊥ : Subgroup G) ≤ H)) y ↔
      orbitRelQuotientBotEquiv (G := G) (X := X) x ∈
        _root_.MulAction.orbit H (orbitRelQuotientBotEquiv (G := G) (X := X) y) := by
  simp [orbitRelQuotientMapOfLE_bot_eq, Quotient.eq'', _root_.MulAction.orbitRel_apply]

/-- In a cancellative action, two translates have the same subgroup-orbit quotient class
exactly when the translators differ on the right by an element of the subgroup. This holds
for an arbitrary subgroup; the normal-subgroup criterion
`orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq` follows from it. -/
lemma orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem [IsCancelSMul G X] (H : Subgroup G)
    (x : X) (g k : G) : (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      g * k⁻¹ ∈ H := by
  constructor
  · intro h
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply] at h
    rcases h with ⟨l, hl⟩
    have hmul : ((l : G) * k) • x = g • x := by
      simpa [Subgroup.smul_def, smul_smul] using hl
    have hg : (l : G) * k = g := IsCancelSMul.right_cancel _ _ x hmul
    simp [← hg, mul_assoc]
  · intro hg
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply]
    exact ⟨⟨g * k⁻¹, hg⟩, by simp [Subgroup.smul_def, smul_smul]⟩

/-- In a cancellative action, a translate has the same subgroup-orbit quotient class as the
base point exactly when the translating group element belongs to the subgroup. -/
lemma orbitRelQuotient_smul_eq_base_iff [IsCancelSMul G X] (H : Subgroup G) (g : G) (x : X) :
    (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' x ↔
      g ∈ H := by
  simpa using orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem H x g 1

/-- In a cancellative action by `G`, equality of two translates in the quotient by a normal
subgroup `H` is equality of the corresponding inverse representatives in the normalizer
quotient `N(H) / H`. -/
lemma orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq [IsCancelSMul G X]
    (H : Subgroup G) [H.Normal] (x : X) (g k : G) :
    (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      Subgroup.normalizerQuotientMk H
          ⟨g⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨k⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  rw [orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem,
    Subgroup.normalizerQuotientMk_eq_iff_div_mem, div_eq_mul_inv, inv_inv,
    (inferInstance : H.Normal).mem_comm_iff, ← inv_mem_iff]
  simp [mul_inv_rev]

/-- Mathlib's subgroup-orbit quotient equivalence sends the coset of `g` back to the orbit
class of `g⁻¹ • x`. This records the representative convention once, so later lemmas can
rewrite through a named theorem rather than relying directly on definitional equality. -/
@[simp]
lemma equivSubgroupOrbitsQuotientGroup_symm_mk [MulAction.IsPretransitive G X] [IsCancelSMul G X]
    (H : Subgroup G) (x : X) (g : G) : (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
        (QuotientGroup.mk (s := H) g) =
      (Quotient.mk'' (g⁻¹ • x) : _root_.MulAction.orbitRel.Quotient H X) :=
  rfl

/-- The subgroup-orbit quotient equivalence sends the orbit class of `g • x` to the coset
of `g⁻¹`. -/
@[simp]
lemma equivSubgroupOrbitsQuotientGroup_apply_smul
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) (x : X) (g : G) :
    MulAction.equivSubgroupOrbitsQuotientGroup x H
        (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
      QuotientGroup.mk (s := H) g⁻¹ := by
  simpa [equivSubgroupOrbitsQuotientGroup_symm_mk, inv_inv] using
    (MulAction.equivSubgroupOrbitsQuotientGroup x H).apply_symm_apply
    (QuotientGroup.mk (s := H) g⁻¹)

private lemma orbitRelQuotientMapOfLE_mk {H K : Subgroup G} (hHK : H ≤ K) (x : X) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X) hHK)
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient K X) :=
  TauCeti.Setoid.map_of_le_mk (orbitRel_le_of_subgroup_le (G := G) (X := X) hHK) x

/-- The subgroup-orbit quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma equivSubgroupOrbitsQuotientGroup_mapOfLE
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] {H K : Subgroup G} (hHK : H ≤ K) (x₀ : X)
    (x : _root_.MulAction.orbitRel.Quotient H X) :
    Subgroup.quotientMapOfLE hHK
        (MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x) =
      MulAction.equivSubgroupOrbitsQuotientGroup x₀ K
        (Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X) hHK) x) := by
  refine Quotient.inductionOn' x ?_
  intro x'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ x'
  rw [← hg]
  rw [equivSubgroupOrbitsQuotientGroup_apply_smul]
  rw [orbitRelQuotientMapOfLE_mk hHK]
  rw [equivSubgroupOrbitsQuotientGroup_apply_smul, Subgroup.quotientMapOfLE_apply_mk]

private lemma normalizer_smul_mem_orbit (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) {x y : X} (hxy : x ∈ _root_.MulAction.orbit H y) :
    (g : G) • x ∈ _root_.MulAction.orbit H ((g : G) • y) := by
  rcases hxy with ⟨h, hh⟩
  refine ⟨⟨(g : G) * h * (g : G)⁻¹, ?_⟩, ?_⟩
  · exact ((_root_.Subgroup.mem_normalizer_iff.mp g.2) (h : G)).1 h.2
  · rw [← hh]
    simp [Subgroup.smul_def, mul_smul]

/-- A normalizer representative acts on the quotient by `H`-orbits. -/
def normalizerOrbitRelQuotientMap (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) :
    _root_.MulAction.orbitRel.Quotient H X → _root_.MulAction.orbitRel.Quotient H X :=
  Quotient.map' (fun x : X => (g : G) • x) fun x y hxy => by
    rw [_root_.MulAction.orbitRel_apply] at hxy ⊢
    exact normalizer_smul_mem_orbit H g hxy

/-- The normalizer action on an orbit quotient sends a class to the class of its translate. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientMap H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientMap]

/-- The normalizer representative `1` acts trivially on the orbit quotient. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_one (H : Subgroup G) :
    normalizerOrbitRelQuotientMap (X := X) H ⟨1, by simp⟩ = id := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [normalizerOrbitRelQuotientMap]

/-- Normalizer representatives act by composition on the orbit quotient. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_mul (H : Subgroup G)
    (g k : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerOrbitRelQuotientMap (X := X) H (g * k) =
      normalizerOrbitRelQuotientMap H g ∘ normalizerOrbitRelQuotientMap H k := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [normalizerOrbitRelQuotientMap, mul_smul]

/-- A normalizer representative acts on the orbit quotient by a permutation. -/
def normalizerOrbitRelQuotientEquiv (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) :
    Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) where
  toFun := normalizerOrbitRelQuotientMap H g
  invFun := normalizerOrbitRelQuotientMap H g⁻¹
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientMap]
  right_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientMap]

/-- A normalizer representative permutes orbit classes by translating representatives. -/
@[simp]
lemma normalizerOrbitRelQuotientEquiv_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientEquiv H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientEquiv]

/-- The inverse normalizer permutation translates representatives by the inverse element. -/
@[simp]
lemma normalizerOrbitRelQuotientEquiv_symm_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    (normalizerOrbitRelQuotientEquiv H g).symm
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G)⁻¹ • x) :=
  by simp [normalizerOrbitRelQuotientEquiv]

/-- The normalizer action on the orbit quotient as a permutation representation. -/
noncomputable def normalizerOrbitRelQuotientPermHom (H : Subgroup G) :
    _root_.Subgroup.normalizer (H : Set G) →*
      Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) where
  toFun := normalizerOrbitRelQuotientEquiv H
  map_one' := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientEquiv, normalizerOrbitRelQuotientMap]
  map_mul' := by
    intro g k
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp only [normalizerOrbitRelQuotientEquiv_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    have hgk : ((g * k : _root_.Subgroup.normalizer (H : Set G)) : G) = (g : G) * (k : G) :=
      rfl
    rw [hgk]
    rw [mul_smul]

/-- The normalizer permutation homomorphism sends representatives to their translates. -/
@[simp]
lemma normalizerOrbitRelQuotientPermHom_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientPermHom (X := X) H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientPermHom]

/-- Any normalizer representative whose underlying group element lies in `H` acts trivially
on the quotient by `H`-orbits. -/
lemma normalizerOrbitRelQuotientPermHom_eq_one_of_mem
    (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) (hg : (g : G) ∈ H) :
    normalizerOrbitRelQuotientPermHom (X := X) H g = 1 := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rw [normalizerOrbitRelQuotientPermHom_apply]
  exact Quotient.sound' ⟨⟨(g : G), hg⟩, rfl⟩

/-- The action of the normalizer on an orbit quotient descends to `N(H) / H`. -/
noncomputable def normalizerQuotientOrbitRelQuotientPermHom (H : Subgroup G) :
    Subgroup.normalizerQuotient H →*
      Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) :=
  Subgroup.normalizerQuotientLift H (normalizerOrbitRelQuotientPermHom (X := X) H)
    (normalizerOrbitRelQuotientPermHom_eq_one_of_mem (X := X) H)

/-- The descended normalizer-quotient action sends a normalizer representative to the
corresponding translate on orbit classes. -/
lemma normalizerQuotientOrbitRelQuotientPermHom_mk_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerQuotientOrbitRelQuotientPermHom (X := X) H
        (Subgroup.normalizerQuotientMk H g)
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerQuotientOrbitRelQuotientPermHom]

/-- The normalizer quotient `N(H) / H` acts on the quotient by `H`-orbits. -/
@[implicit_reducible]
noncomputable def normalizerQuotientOrbitRelQuotientMulAction (H : Subgroup G) :
    MulAction (Subgroup.normalizerQuotient H) (_root_.MulAction.orbitRel.Quotient H X) :=
  MulAction.compHom (_root_.MulAction.orbitRel.Quotient H X)
    (normalizerQuotientOrbitRelQuotientPermHom (X := X) H)

/-- A normalizer-quotient representative acts on the orbit quotient by translating
representatives. -/
lemma normalizerQuotientOrbitRelQuotient_smul_mk (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    Subgroup.normalizerQuotientMk H g •
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by
    -- The named action is the `compHom` action, whose smul applies the underlying
    -- permutation homomorphism to the point.
    change normalizerQuotientOrbitRelQuotientPermHom (X := X) H
        (Subgroup.normalizerQuotientMk H g)
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x)
    exact normalizerQuotientOrbitRelQuotientPermHom_mk_apply (X := X) H g x

/-- In a free transitive action, quotienting by a normal subgroup `H` identifies the
`H`-orbit quotient with the normalizer quotient `N(H) / H`. The representative convention is
the same as Mathlib's `equivSubgroupOrbitsQuotientGroup`: the class of `g • x` corresponds to
the class of `g⁻¹`. -/
noncomputable def orbitRelQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X) :
    _root_.MulAction.orbitRel.Quotient H X ≃ Subgroup.normalizerQuotient H :=
  (MulAction.equivSubgroupOrbitsQuotientGroup x H).trans
    (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.symm

/-- The normal-subgroup orbit quotient equivalence, followed by the normalizer quotient's
normal-case comparison, is Mathlib's equivalence to `G ⧸ H`. -/
@[simp]
lemma normalizerQuotientEquivQuotientOfNormal_orbitRelQuotientEquivNormalizerQuotientOfNormal
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x₀ : X)
    (x : _root_.MulAction.orbitRel.Quotient H X) :
    Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ x) =
      MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x :=
  (Subgroup.normalizerQuotientEquivQuotientOfNormal H).toEquiv.apply_symm_apply
    (MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x)

/-- The inverse normal-subgroup orbit-quotient equivalence sends a normalizer representative
to the orbit class of its inverse acting on the base point. -/
@[simp]
lemma orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mk
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    (orbitRelQuotientEquivNormalizerQuotientOfNormal H x).symm (g : Subgroup.normalizerQuotient H) =
      (Quotient.mk'' ((g : G)⁻¹ • x) : _root_.MulAction.orbitRel.Quotient H X) := by
  -- The new equivalence is definitionally Mathlib's orbit-quotient equivalence transposed
  -- across the normal-subgroup comparison `N(H) / H ≃ G ⧸ H`.
  change (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
      (Subgroup.normalizerQuotientEquivQuotientOfNormal H
        (Subgroup.normalizerQuotientMk H g)) =
    (Quotient.mk'' ((g : G)⁻¹ • x) : _root_.MulAction.orbitRel.Quotient H X)
  rw [Subgroup.normalizerQuotientEquivQuotientOfNormal_mk]
  exact equivSubgroupOrbitsQuotientGroup_symm_mk H x (g : G)

/-- The normal-subgroup orbit-quotient equivalence sends the class of `g • x` to the
normalizer-quotient class of `g⁻¹`. -/
@[simp]
lemma orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x : X) (g : G) :
    orbitRelQuotientEquivNormalizerQuotientOfNormal H x
        (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
      Subgroup.normalizerQuotientMk H
        ⟨g⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  rw [(orbitRelQuotientEquivNormalizerQuotientOfNormal H x).apply_eq_iff_eq_symm_apply]
  rw [Subgroup.normalizerQuotientMk_apply]
  rw [orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mk]
  simp

/-- Under the normal-subgroup orbit-quotient equivalence, the descended normalizer-quotient
action is right multiplication by the inverse. -/
@[simp]
lemma orbitRelQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv
    [MulAction.IsPretransitive G X] [IsCancelSMul G X] (H : Subgroup G) [H.Normal] (x₀ : X)
    (a : Subgroup.normalizerQuotient H) (x : _root_.MulAction.orbitRel.Quotient H X) :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ (a • x) =
      orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀ x * a⁻¹ := by
  letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  obtain ⟨g, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
  refine Quotient.inductionOn' x ?_
  intro x
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G x₀ x
  rw [← hk]
  rw [normalizerQuotientOrbitRelQuotient_smul_mk, ← mul_smul,
    orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul,
    orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul]
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  simp [mul_inv_rev]

/-- Applying the inverse normal-subgroup orbit-quotient equivalence after right
multiplication by `a⁻¹` is the same as acting by `a` on the orbit quotient. -/
lemma orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [MulAction.IsPretransitive G X] [IsCancelSMul G X]
    (H : Subgroup G) [H.Normal] (x₀ : X) (a y : Subgroup.normalizerQuotient H) :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    (orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).symm (y * a⁻¹) =
      a • (orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).symm y := by
  letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  apply (orbitRelQuotientEquivNormalizerQuotientOfNormal H x₀).injective
  rw [Equiv.apply_symm_apply,
    orbitRelQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv,
    Equiv.apply_symm_apply]

/-- If the normalizer of `H` acts transitively on `X`, then the descended `N(H) / H` action on
the quotient by `H`-orbits is transitive. -/
theorem normalizerQuotientOrbitRelQuotientIsPretransitive (H : Subgroup G)
    [MulAction.IsPretransitive (_root_.Subgroup.normalizer (H : Set G)) X] :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (_root_.MulAction.orbitRel.Quotient H X) := by
  letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  let φ : _root_.Subgroup.normalizer (H : Set G) → Subgroup.normalizerQuotient H :=
    Subgroup.normalizerQuotientMk H
  let f : X →ₑ[φ] _root_.MulAction.orbitRel.Quotient H X := {
    toFun := Quotient.mk''
    map_smul' g x := by
      exact (normalizerQuotientOrbitRelQuotient_smul_mk (X := X) H g x).symm }
  exact MulAction.IsPretransitive.of_surjective_map
    (f := f) Quotient.mk''_surjective inferInstance

/-- If `H` is normal and `G` acts transitively on `X`, then the descended `N(H) / H` action
on the quotient by `H`-orbits is transitive. -/
theorem normalizerQuotientOrbitRelQuotientIsPretransitiveOfNormal
    [MulAction.IsPretransitive G X] (H : Subgroup G) [H.Normal] :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (_root_.MulAction.orbitRel.Quotient H X) := by
  letI : MulAction.IsPretransitive (_root_.Subgroup.normalizer (H : Set G)) X :=
    MulAction.IsPretransitive.mk fun x y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
      refine ⟨⟨g, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩, ?_⟩
      simpa using hg
  exact normalizerQuotientOrbitRelQuotientIsPretransitive (X := X) H

/-- Equality after the descended `N(H) / H` action on an `H`-orbit quotient is equality of
normalizer-quotient elements, provided the original action is free. -/
@[simp]
lemma normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff [IsCancelSMul G X]
    (H : Subgroup G) (a c : Subgroup.normalizerQuotient H)
    (x : _root_.MulAction.orbitRel.Quotient H X) :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    a • x = c • x ↔ a = c := by
  letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H a
    obtain ⟨k, rfl⟩ := Subgroup.normalizerQuotientMk_surjective H c
    refine Quotient.inductionOn' x ?_ h
    intro x h
    rw [normalizerQuotientOrbitRelQuotient_smul_mk,
      normalizerQuotientOrbitRelQuotient_smul_mk] at h
    rw [Subgroup.normalizerQuotientMk_eq_iff_div_mem]
    simpa [div_eq_mul_inv] using
      (orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem H x (g : G) (k : G)).mp h
  · intro h
    rw [h]

/-- If a group acts freely on `X`, then the descended `N(H) / H` action on the quotient of `X`
by `H`-orbits is free. This packages `normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff` as the
cancellativity of the descended action. -/
theorem normalizerQuotientOrbitRelQuotientIsCancelSMul [IsCancelSMul G X] (H : Subgroup G) :
    letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
    IsCancelSMul (Subgroup.normalizerQuotient H) (_root_.MulAction.orbitRel.Quotient H X) :=
  letI := normalizerQuotientOrbitRelQuotientMulAction (X := X) H
  { right_cancel' := fun a c x h =>
      (normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff H a c x).mp h }

end MulAction

end TauCeti
