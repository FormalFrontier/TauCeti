/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugate representations

For a subgroup `H` of a group `G` and `s : G`, this file defines the conjugate of an
`H`-representation as a representation of `sHs⁻¹`.  The action is transported along the canonical
isomorphism

`sHs⁻¹ → H, x ↦ s⁻¹xs`.

This is the representation occurring in the summands of the Mackey decomposition.

The file also records the coherence making `s ↦ {}^s(-)` an action: conjugating by `1` does
nothing and `{}^{st} A = {}^s({}^t A)`.  Neither statement is literally an equation between
representations of one group, because `{}^s({}^t A)` is a representation of `s(tHt⁻¹)s⁻¹` while
`{}^{st} A` is a representation of `(st)H(st)⁻¹`; the two subgroups are equal, and the coherence
is stated after transporting along that equality with `MulEquiv.subgroupCongr` and `Rep.res`.

For a *normal* subgroup `N` the conjugated subgroup is `N` itself, so no transport is needed:
`conjNormalRep` is an honest action of `G` on `Rep k N`, and it is the action on `Irr(N)` that
Clifford theory runs on.

## Main definitions

* `TauCeti.conjSubgroupEquiv`: the canonical isomorphism from `sHs⁻¹` to `H`.
* `TauCeti.conjRepFunctor`: conjugation as a functor between representation categories.
* `TauCeti.conjRep`: the conjugate of a representation.
* `TauCeti.conjFDRep`: the finite-dimensional version.
* `TauCeti.conjNormalRep`, `TauCeti.conjNormalFDRep`: conjugation of a representation of a normal
  subgroup, again a representation of that subgroup.

## Main statements

* `TauCeti.conjRep_one`, `TauCeti.conjRep_mul` and their `FDRep` counterparts: the coherence of
  conjugation, up to the identification of the conjugated subgroups.
* `TauCeti.conjNormalRep_one`, `TauCeti.conjNormalRep_mul` and their `FDRep` counterparts: for a
  normal subgroup that coherence becomes a genuine left action of `G`.
* `TauCeti.res_conjRep`, `TauCeti.res_conjFDRep`: the normal-subgroup conjugation is the general
  conjugate representation, read through `MulAut.conj g • N = N`.

## References

The convention and implementation plan follow
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` and its accompanying
`Suggested.lean`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v w

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G]

/-- Membership in `sHs⁻¹`, expressed using the conjugation convention used by `conjRep`. -/
@[simp]
theorem mem_conj_smul (s : G) (H : Subgroup G) (x : G) :
    x ∈ (MulAut.conj s • H : Subgroup G) ↔ s⁻¹ * x * s ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

/-- The canonical multiplicative equivalence `sHs⁻¹ ≃* H`, given by `x ↦ s⁻¹xs`. -/
def conjSubgroupEquiv (s : G) (H : Subgroup G) :
    (MulAut.conj s • H : Subgroup G) ≃* H :=
  (Subgroup.equivSMul (MulAut.conj s) H).symm

@[simp]
theorem coe_conjSubgroupEquiv_apply (s : G) (H : Subgroup G)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjSubgroupEquiv s H x : G) = s⁻¹ * (x : G) * s := by
  simp [conjSubgroupEquiv]

@[simp]
theorem coe_conjSubgroupEquiv_symm_apply (s : G) (H : Subgroup G) (x : H) :
    ((conjSubgroupEquiv s H).symm x : G) = s * (x : G) * s⁻¹ := by
  simp [conjSubgroupEquiv]

/-- Conjugating representations by `s` is restriction along the isomorphism
`sHs⁻¹ ≃* H`. -/
def conjRepFunctor [Semiring k] (s : G) (H : Subgroup G) :
    Rep k H ⥤ Rep k (MulAut.conj s • H : Subgroup G) :=
  Rep.resFunctor (conjSubgroupEquiv s H).toMonoidHom

/-- The conjugate representation `{}^s A` of `sHs⁻¹`. -/
def conjRep [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H) :
    Rep k (MulAut.conj s • H : Subgroup G) :=
  (conjRepFunctor s H).obj A

/-- Conjugation preserves the underlying module of a representation. -/
@[simp]
theorem conjRep_V [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H) :
    (conjRep s A).V = A.V := by
  -- Unfold the local wrappers to expose Mathlib's restriction carrier.
  change (Rep.res (conjSubgroupEquiv s H).toMonoidHom A).V = A.V
  exact Rep.res_obj_V _ _

/-- Conjugation preserves the underlying linear map of a representation morphism. -/
theorem conjRepFunctor_map_hom_toLinearMap [Semiring k] (s : G) {H : Subgroup G}
    {A B : Rep k H} (f : A ⟶ B) :
    HEq ((conjRepFunctor s H).map f).hom.toLinearMap f.hom.toLinearMap := by
  -- Unfold the local functor wrapper to expose Mathlib's restriction map.
  change HEq (Rep.resMap (conjSubgroupEquiv s H).toMonoidHom f).hom.toLinearMap _
  exact heq_of_eq (Rep.resMap_hom_toLinearMap _ _)

/-- The conjugate action, as a heterogeneous equality: `conjRep` is opaque, so
`(conjRep s A).V` and `A.V` are equal only via `conjRep_V`, not definitionally. -/
theorem conjRep_ρ [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  -- Unfold the local wrappers to expose Mathlib's restricted action.
  change HEq ((Rep.res (conjSubgroupEquiv s H).toMonoidHom A).ρ x) _
  exact heq_of_eq (Rep.coe_res_obj_ρ' _ _ _)

/-- The conjugate action on elements, transported along `conjRep_V`. -/
theorem conjRep_ρ_apply [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) (v : A.V) :
    cast (conjRep_V s A) ((conjRep s A).ρ x (cast (conjRep_V s A).symm v)) =
      A.ρ (conjSubgroupEquiv s H x) v := by
  -- Unfold the local wrapper to expose Mathlib's restricted action; both casts are along the
  -- definitional carrier equality `Rep.res_obj_V`.
  change (Rep.res (conjSubgroupEquiv s H).toMonoidHom A).ρ x v = _
  exact LinearMap.congr_fun (Rep.coe_res_obj_ρ' _ _ x) v

/-- The action of the conjugate representation, written directly in the ambient group. -/
theorem conjRep_ρ_mk [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x)
      (A.ρ ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩) := by
  apply (conjRep_ρ s A x).trans
  congr 1

section Coherence

/-- Conjugating a subgroup by `1` leaves it unchanged. -/
theorem conj_one_smul (H : Subgroup G) : MulAut.conj (1 : G) • H = H := by
  simp

/-- Conjugating a subgroup by `s * t` is conjugating by `t` and then by `s`. -/
theorem conj_mul_smul (s t : G) (H : Subgroup G) :
    MulAut.conj (s * t) • H = MulAut.conj s • (MulAut.conj t • H) := by
  rw [map_mul, mul_smul]

/-- The transported form of `conjSubgroupEquiv 1`: conjugating by `1` is the identification of
`1 · H · 1⁻¹` with `H`. -/
theorem conjSubgroupEquiv_one (H : Subgroup G) :
    (conjSubgroupEquiv (1 : G) H).toMonoidHom =
      (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

/-- The homomorphism `(st)H(st)⁻¹ →* H` underlying `{}^{st}` is the one underlying `{}^t`
composed with the one underlying `{}^s`, after identifying `(st)H(st)⁻¹` with `s(tHt⁻¹)s⁻¹`.
This is the sole computation behind the coherence statements below: `(st)⁻¹ x (st) = t⁻¹(s⁻¹ x s)t`.
-/
theorem conjSubgroupEquiv_mul (s t : G) (H : Subgroup G) :
    (conjSubgroupEquiv (s * t) H).toMonoidHom =
      ((conjSubgroupEquiv t H).toMonoidHom.comp
          (conjSubgroupEquiv s (MulAut.conj t • H)).toMonoidHom).comp
        (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      coe_conjSubgroupEquiv_apply, MulEquiv.subgroupCongr_apply]
    group)

variable [Semiring k]

/-- Conjugating by `1` does nothing, once `1 · H · 1⁻¹` is identified with `H`. -/
theorem conjRep_one {H : Subgroup G} (A : Rep k H) :
    conjRep (1 : G) A =
      Rep.res (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom A :=
  congrArg (fun φ : (MulAut.conj (1 : G) • H : Subgroup G) →* H => Rep.res φ A)
    (conjSubgroupEquiv_one H)

/-- **Cocycle coherence for conjugation**: `{}^{st} A = {}^s({}^t A)`, once `(st)H(st)⁻¹` is
identified with `s(tHt⁻¹)s⁻¹`.

Together with `conjRep_one` this is what makes `s ↦ {}^s(-)` an action of `G`; both Mackey theory
(where a double-coset representative may be replaced by another) and Clifford theory consume it. -/
theorem conjRep_mul (s t : G) {H : Subgroup G} (A : Rep k H) :
    conjRep (s * t) A =
      Rep.res (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom
        (conjRep s (conjRep t A)) :=
  congrArg (fun φ : (MulAut.conj (s * t) • H : Subgroup G) →* H => Rep.res φ A)
    (conjSubgroupEquiv_mul s t H)

end Coherence

section FDRep

variable [CommRing k]

/-- The conjugate of a finite-dimensional representation. -/
noncomputable def conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    FDRep k (MulAut.conj s • H : Subgroup G) :=
  FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)

/-- Conjugation preserves the underlying module of a finite-dimensional representation. -/
@[simp]
theorem conjFDRep_V (s : G) {H : Subgroup G} (A : FDRep k H) :
    (conjFDRep s A).V = A.V := by
  rfl

/-- The conjugate finite-dimensional action, as a heterogeneous equality. -/
theorem conjFDRep_ρ (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjFDRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  -- Unfold the local wrapper to expose the action of Mathlib's `FDRep.of`.
  change HEq ((FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)).ρ x) _
  rw [FDRep.of_ρ']
  rfl

/-- The conjugate action, transported along `conjFDRep_V`. -/
theorem conjFDRep_ρ_cast (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    cast (congrArg (fun V : FGModuleCat k => V →ₗ[k] V) (conjFDRep_V s A))
      ((conjFDRep s A).ρ x) = A.ρ (conjSubgroupEquiv s H x) := by
  -- Unfold the local wrapper to expose the action of Mathlib's `FDRep.of`.
  change (FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)).ρ x = _
  rw [FDRep.of_ρ']
  rfl

/-- Conjugation preserves the dimension (finrank) of a finite-dimensional representation. -/
@[simp]
theorem finrank_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    Module.finrank k (conjFDRep s A) = Module.finrank k A := by
  exact congrArg (fun V : FGModuleCat k => Module.finrank k V) (conjFDRep_V s A)

/-- Conjugating a finite-dimensional representation by `1` does nothing, once `1 · H · 1⁻¹` is
identified with `H`.  The `FDRep` mirror of `conjRep_one`. -/
theorem conjFDRep_one {H : Subgroup G} (A : FDRep k H) :
    conjFDRep (1 : G) A =
      (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom).obj A :=
  congrArg (fun φ : (MulAut.conj (1 : G) • H : Subgroup G) →* H => FDRep.of (A.ρ.comp φ))
    (conjSubgroupEquiv_one H)

/-- **Cocycle coherence** for finite-dimensional representations: `{}^{st} A = {}^s({}^t A)`, once
`(st)H(st)⁻¹` is identified with `s(tHt⁻¹)s⁻¹`.  The `FDRep` mirror of `conjRep_mul`, and the form
in which the character computations of Mackey and Clifford theory use it. -/
theorem conjFDRep_mul (s t : G) {H : Subgroup G} (A : FDRep k H) :
    conjFDRep (s * t) A =
      (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom).obj
          (conjFDRep s (conjFDRep t A)) :=
  congrArg (fun φ : (MulAut.conj (s * t) • H : Subgroup G) →* H => FDRep.of (A.ρ.comp φ))
    (conjSubgroupEquiv_mul s t H)

end FDRep

section Character

variable [Field k]

/-- The character of a conjugate representation is evaluated through `conjSubgroupEquiv`. -/
@[simp]
theorem char_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x = A.character (conjSubgroupEquiv s H x) := by
  rw [FDRep.character, FDRep.character]
  congr 1

/-- The conjugate-character formula `({}^s χ)(x) = χ(s⁻¹xs)`. -/
theorem char_conjFDRep_mk (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x =
      A.character ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩ := by
  rw [char_conjFDRep]
  congr 1

end Character

/-! ## Conjugation on a normal subgroup

For `N ◁ G` the conjugated subgroup `MulAut.conj g • N` is `N` itself
(`Subgroup.Normal.conj_smul_eq_self`), so conjugation does not move the group it is a
representation of, and the coherence of the previous sections becomes a genuine left action of `G`
on `Rep k N`.  This is the action on the irreducibles of `N` that Clifford theory runs on. -/

section Normal

variable {N : Subgroup G} [hN : N.Normal]

/-- Conjugating a normal subgroup by `1` is the identity automorphism.  The `MulAut.conjNormal`
form of `conj_one_smul`. -/
theorem conjNormal_inv_one :
    (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = MonoidHom.id N :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

/-- Conjugating a normal subgroup by `s * t` is conjugating by `t` after conjugating by `s`.  The
`MulAut.conjNormal` form of `conj_mul_smul`; note the order, which is the one `Rep.res` reverses
into a left action. -/
theorem conjNormal_inv_mul (s t : G) :
    (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom =
      (MulAut.conjNormal (t⁻¹) : MulAut N).toMonoidHom.comp
        (MulAut.conjNormal (s⁻¹) : MulAut N).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by
    simp only [MulAut.conjNormal_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    group)

/-- On a normal subgroup, the homomorphism `N →* gNg⁻¹ →* N` that `conjRep` restricts along is
`MulAut.conjNormal g⁻¹`. -/
theorem conjSubgroupEquiv_comp_subgroupCongr (g : G) :
    (conjSubgroupEquiv g N).toMonoidHom.comp
        (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom =
      (MulAut.conjNormal (g⁻¹) : MulAut N).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

section NormalRep

variable [Semiring k]

/-- The conjugate `{}^g A` of a representation of a **normal** subgroup `N`, again a
representation of `N`: the element `x : N` acts by `A.ρ (g⁻¹ x g)`.

This is `conjRep` with the conjugated subgroup identified with `N`, as `res_conjRep` records; the
conjugating automorphism is Mathlib's `MulAut.conjNormal g⁻¹`. -/
@[expose]
def conjNormalRep (g : G) (A : Rep k N) : Rep k N :=
  Rep.res (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom A

/-- Conjugation on a normal subgroup preserves the underlying module.  Not a `simp` lemma: it is
`rfl`, and as a rewrite it fires inside the *type* of the left-hand side of `conjNormalRep_ρ`. -/
theorem conjNormalRep_V (g : G) (A : Rep k N) : (conjNormalRep g A).V = A.V :=
  rfl

/-- The conjugate action on a normal subgroup.  Unlike `conjRep_ρ` this is an honest equality:
the two representations are representations of the same group, on the same module. -/
@[simp]
theorem conjNormalRep_ρ (g : G) (A : Rep k N) (x : N) :
    (conjNormalRep g A).ρ x = A.ρ (MulAut.conjNormal g⁻¹ x) :=
  rfl

/-- The conjugate action on a normal subgroup, written in the ambient group. -/
theorem conjNormalRep_ρ_mk (g : G) (A : Rep k N) (x : N) :
    (conjNormalRep g A).ρ x = A.ρ ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ := by
  rw [conjNormalRep_ρ]
  congr 1
  exact Subtype.ext (by simp)

/-- On a normal subgroup, `conjNormalRep` is the general conjugate representation `conjRep`, read
through the identification `gNg⁻¹ = N`. -/
theorem res_conjRep (g : G) (A : Rep k N) :
    Rep.res (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom
        (conjRep g A) = conjNormalRep g A :=
  congrArg (fun φ : N →* N => Rep.res φ A) (conjSubgroupEquiv_comp_subgroupCongr g)

/-- Conjugating by `1` is the identity. -/
@[simp]
theorem conjNormalRep_one (A : Rep k N) : conjNormalRep (1 : G) A = A :=
  (congrArg (fun φ : N →* N => Rep.res φ A) conjNormal_inv_one).trans (Rep.res_id A)

/-- Conjugation is a left action: `{}^{st} A = {}^s({}^t A)`. -/
theorem conjNormalRep_mul (s t : G) (A : Rep k N) :
    conjNormalRep (s * t) A = conjNormalRep s (conjNormalRep t A) :=
  congrArg (fun φ : N →* N => Rep.res φ A) (conjNormal_inv_mul s t)

end NormalRep

section NormalFDRep

variable [CommRing k]

/-- The conjugate `{}^g A` of a finite-dimensional representation of a **normal** subgroup, again
a finite-dimensional representation of that subgroup.

`FDRep k N` is by definition `Action (FGModuleCat k) N`, so this is Mathlib's `Action.res` along
the conjugating automorphism, and the underlying module is `A.V` on the nose. -/
@[expose]
def conjNormalFDRep (g : G) (A : FDRep k N) : FDRep k N :=
  (Action.res (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom).obj A

/-- Conjugation on a normal subgroup preserves the underlying module.  Not a `simp` lemma, for the
same reason as `conjNormalRep_V`. -/
theorem conjNormalFDRep_V (g : G) (A : FDRep k N) : (conjNormalFDRep g A).V = A.V :=
  rfl

/-- The conjugate finite-dimensional action on a normal subgroup, as an honest equality. -/
@[simp]
theorem conjNormalFDRep_ρ (g : G) (A : FDRep k N) (x : N) :
    (conjNormalFDRep g A).ρ x = A.ρ (MulAut.conjNormal g⁻¹ x) :=
  rfl

/-- The conjugate finite-dimensional action, written in the ambient group. -/
theorem conjNormalFDRep_ρ_mk (g : G) (A : FDRep k N) (x : N) :
    (conjNormalFDRep g A).ρ x = A.ρ ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ := by
  rw [conjNormalFDRep_ρ]
  congr 1
  exact Subtype.ext (by simp)

/-- Conjugation on a normal subgroup preserves the dimension. -/
@[simp]
theorem finrank_conjNormalFDRep (g : G) (A : FDRep k N) :
    Module.finrank k (conjNormalFDRep g A) = Module.finrank k A :=
  rfl

/-- On a normal subgroup, `conjNormalFDRep` is `conjFDRep` read through `gNg⁻¹ = N`. -/
theorem res_conjFDRep (g : G) (A : FDRep k N) :
    (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom).obj
      (conjFDRep g A) = conjNormalFDRep g A :=
  congrArg (fun φ : N →* N => (Action.res (FGModuleCat k) φ).obj A)
    (conjSubgroupEquiv_comp_subgroupCongr g)

/-- Conjugating by `1` is the identity. -/
@[simp]
theorem conjNormalFDRep_one (A : FDRep k N) : conjNormalFDRep (1 : G) A = A :=
  congrArg (fun φ : N →* N => (Action.res (FGModuleCat k) φ).obj A) conjNormal_inv_one

/-- Conjugation is a left action: `{}^{st} A = {}^s({}^t A)`. -/
theorem conjNormalFDRep_mul (s t : G) (A : FDRep k N) :
    conjNormalFDRep (s * t) A = conjNormalFDRep s (conjNormalFDRep t A) :=
  congrArg (fun φ : N →* N => (Action.res (FGModuleCat k) φ).obj A) (conjNormal_inv_mul s t)

end NormalFDRep

section NormalCharacter

variable [Field k]

/-- The character of the conjugate of a representation of a normal subgroup. -/
@[simp]
theorem char_conjNormalFDRep (g : G) (A : FDRep k N) (x : N) :
    (conjNormalFDRep g A).character x = A.character (MulAut.conjNormal g⁻¹ x) :=
  rfl

/-- The conjugate-character formula on a normal subgroup: `({}^g χ)(x) = χ(g⁻¹xg)`. -/
theorem char_conjNormalFDRep_mk (g : G) (A : FDRep k N) (x : N) :
    (conjNormalFDRep g A).character x =
      A.character ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ := by
  rw [char_conjNormalFDRep]
  congr 1
  exact Subtype.ext (by simp)

end NormalCharacter

end Normal

end TauCeti
