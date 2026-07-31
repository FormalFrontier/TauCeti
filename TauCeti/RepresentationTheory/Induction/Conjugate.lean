/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.RepresentationTheory.Induction.Restriction

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
Both halves are proved as equalities of *functors*; the statements about a single representation
are their evaluations.

For a *normal* subgroup `N` the conjugated subgroup is `N` itself, so no transport is needed:
conjugation by `g` is an endofunctor of `Rep k N`, indeed an autoequivalence, and the coherence
makes `g ↦ conjNormalRep g` a `MulAction` of `G` on `Rep k N`.  This is the action of `G` on
`Rep k N` that Clifford theory runs on.  Its inertia group of a representation `A` is the
stabilizer of the *isomorphism class* of `A`, `{g | {}^g A ≅ A}`, which this action cuts out but
which is not `MulAction.stabilizer G A`: the latter asks for `{}^g A = A` on the nose.  Neither
the induced action on isomorphism classes, nor the fact that the action preserves irreducibility
(so restricts to `Irr(N)`), is proved here.

## Main definitions

* `TauCeti.conjSubgroupEquiv`: the canonical isomorphism from `sHs⁻¹` to `H`.
* `TauCeti.conjRepFunctor`, `TauCeti.conjFDRepFunctor`: conjugation as a functor between
  representation categories, with `TauCeti.conjRepEquiv` and `TauCeti.conjFDRepEquiv` the
  equivalences `Rep k H ≌ Rep k (sHs⁻¹)` and `FDRep k H ≌ FDRep k (sHs⁻¹)` they underlie.
* `TauCeti.conjRep`: the conjugate of a representation.
* `TauCeti.conjFDRep`: the finite-dimensional version.
* `TauCeti.conjNormalRepFunctor`, `TauCeti.conjNormalFDRepFunctor`: for a normal subgroup,
  conjugation as an endofunctor, with `TauCeti.conjNormalRepEquiv` and
  `TauCeti.conjNormalFDRepEquiv` the autoequivalences they underlie.
* `TauCeti.conjNormalRep`, `TauCeti.conjNormalFDRep`: conjugation of a representation of a normal
  subgroup, again a representation of that subgroup; these are the `MulAction` of `G` on
  `Rep k N` and on `FDRep k N`.

## Main statements

* `TauCeti.conjRepFunctor_one`, `TauCeti.conjRepFunctor_mul` and their `FDRep` counterparts: the
  coherence of conjugation, as equalities of functors, up to the identification of the conjugated
  subgroups; `TauCeti.conjRep_one`, `TauCeti.conjRep_mul` evaluate them at a representation.
* `TauCeti.conjNormalRep_one`, `TauCeti.conjNormalRep_mul` and their `FDRep` counterparts: for a
  normal subgroup that coherence becomes a genuine left action of `G`, recorded as `MulAction`
  instances.
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
  -- `Subgroup.equivSMul (MulAut.conj s) H` acts by `x ↦ s * x * s⁻¹`, so its inverse returns
  -- `s⁻¹ * x * s` as the underlying element by definition.
  rfl

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

/-- Conjugating a subgroup by `s⁻¹` undoes conjugating it by `s`. -/
theorem conj_inv_smul_smul (s : G) (H : Subgroup G) :
    MulAut.conj s⁻¹ • (MulAut.conj s • H) = H := by
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The transported form of `conjSubgroupEquiv 1`: conjugating by `1` is the identification of
`1 · H · 1⁻¹` with `H`. -/
private theorem conjSubgroupEquiv_one (H : Subgroup G) :
    (conjSubgroupEquiv (1 : G) H).toMonoidHom =
      (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

/-- Conjugating by `s⁻¹`, after identifying `H` with `s⁻¹(sHs⁻¹)s`, is the identification
`H →* sHs⁻¹` inverse to the one `{}^s` restricts along.  This is what makes the inverse of the
conjugation equivalence conjugation by `s⁻¹`. -/
private theorem conjSubgroupEquiv_inv_comp_subgroupCongr (s : G) (H : Subgroup G) :
    (conjSubgroupEquiv s⁻¹ (MulAut.conj s • H)).toMonoidHom.comp
        (MulEquiv.subgroupCongr (conj_inv_smul_smul s H).symm).toMonoidHom =
      (conjSubgroupEquiv s H).symm.toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

/-- The homomorphism `(st)H(st)⁻¹ →* H` underlying `{}^{st}` is the one underlying `{}^t`
composed with the one underlying `{}^s`, after identifying `(st)H(st)⁻¹` with `s(tHt⁻¹)s⁻¹`.
This is the sole computation behind the coherence statements below: `(st)⁻¹ x (st) = t⁻¹(s⁻¹ x s)t`.
-/
private theorem conjSubgroupEquiv_mul (s t : G) (H : Subgroup G) :
    (conjSubgroupEquiv (s * t) H).toMonoidHom =
      ((conjSubgroupEquiv t H).toMonoidHom.comp
          (conjSubgroupEquiv s (MulAut.conj t • H)).toMonoidHom).comp
        (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      coe_conjSubgroupEquiv_apply, MulEquiv.subgroupCongr_apply]
    group)

variable [Semiring k]

/-- Conjugating by `1` does nothing, once `1 · H · 1⁻¹` is identified with `H`: an equality of
functors, of which `conjRep_one` is the evaluation at a representation. -/
theorem conjRepFunctor_one (H : Subgroup G) :
    conjRepFunctor (k := k) (1 : G) H =
      Rep.resFunctor (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom :=
  congrArg (fun φ : (MulAut.conj (1 : G) • H : Subgroup G) →* H => Rep.resFunctor (k := k) φ)
    (conjSubgroupEquiv_one H)

/-- **Cocycle coherence for conjugation**, at the level of functors: `{}^{st}(-) = {}^s({}^t(-))`,
once `(st)H(st)⁻¹` is identified with `s(tHt⁻¹)s⁻¹`.  Being an equality of functors this also
pins down the behaviour on morphisms, which the evaluation `conjRep_mul` does not see.

Together with `conjRepFunctor_one` this is what makes `s ↦ {}^s(-)` an action of `G`; both Mackey
theory (where a double-coset representative may be replaced by another) and Clifford theory
consume it. -/
theorem conjRepFunctor_mul (s t : G) (H : Subgroup G) :
    conjRepFunctor (k := k) (s * t) H =
      conjRepFunctor t H ⋙ conjRepFunctor s (MulAut.conj t • H) ⋙
        Rep.resFunctor (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom := by
  -- `conjRepFunctor (s * t) H` is by definition restriction along
  -- `conjSubgroupEquiv (s * t) H`; unfolding the wrapper definitionally is what exposes that
  -- homomorphism, which is the thing `conjSubgroupEquiv_mul` rewrites.
  change Rep.resFunctor (conjSubgroupEquiv (s * t) H).toMonoidHom = _
  rw [conjSubgroupEquiv_mul, resFunctor_comp, resFunctor_comp]
  rfl

/-- Conjugating by `1` does nothing, once `1 · H · 1⁻¹` is identified with `H`. -/
theorem conjRep_one {H : Subgroup G} (A : Rep k H) :
    conjRep (1 : G) A =
      Rep.res (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom A :=
  Functor.congr_obj (conjRepFunctor_one H) A

/-- **Cocycle coherence for conjugation**: `{}^{st} A = {}^s({}^t A)`, once `(st)H(st)⁻¹` is
identified with `s(tHt⁻¹)s⁻¹`.  The evaluation of `conjRepFunctor_mul` at `A`. -/
theorem conjRep_mul (s t : G) {H : Subgroup G} (A : Rep k H) :
    conjRep (s * t) A =
      Rep.res (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom
        (conjRep s (conjRep t A)) :=
  Functor.congr_obj (conjRepFunctor_mul s t H) A

/-- **Conjugation is an equivalence of categories** `Rep k H ≌ Rep k (sHs⁻¹)`: it is restriction
along the isomorphism `conjSubgroupEquiv s H`, and `resFunctorEquiv` makes any such restriction an
equivalence.  Its inverse is conjugation by `s⁻¹`, read through `s⁻¹(sHs⁻¹)s = H`
(`conjRepEquiv_inverse_eq_conjRepFunctor`).

`conjNormalRepEquiv` is the normal-subgroup form, where source and target coincide, so that the
equivalence is an autoequivalence and the coherence below becomes an action. -/
def conjRepEquiv (s : G) (H : Subgroup G) :
    Rep k H ≌ Rep k (MulAut.conj s • H : Subgroup G) :=
  resFunctorEquiv (conjSubgroupEquiv s H)

@[simp]
theorem conjRepEquiv_functor (s : G) (H : Subgroup G) :
    (conjRepEquiv (k := k) s H).functor = conjRepFunctor s H := by
  -- Unfold both wrappers to expose the restriction functor they share.
  change (resFunctorEquiv (conjSubgroupEquiv s H)).functor =
    Rep.resFunctor (conjSubgroupEquiv s H).toMonoidHom
  rw [resFunctorEquiv_functor]

@[simp]
theorem conjRepEquiv_inverse (s : G) (H : Subgroup G) :
    (conjRepEquiv (k := k) s H).inverse =
      Rep.resFunctor (conjSubgroupEquiv s H).symm.toMonoidHom := by
  -- Unfold the `conjRepEquiv` wrapper to expose `resFunctorEquiv`.
  change (resFunctorEquiv (conjSubgroupEquiv s H)).inverse = _
  rw [resFunctorEquiv_inverse]

/-- The inverse of the conjugation equivalence is conjugation by `s⁻¹`, once `s⁻¹(sHs⁻¹)s` is
identified with `H`. -/
theorem conjRepEquiv_inverse_eq_conjRepFunctor (s : G) (H : Subgroup G) :
    (conjRepEquiv (k := k) s H).inverse =
      conjRepFunctor s⁻¹ (MulAut.conj s • H) ⋙
        Rep.resFunctor (MulEquiv.subgroupCongr (conj_inv_smul_smul s H).symm).toMonoidHom := by
  -- Unfold the `conjRepFunctor` wrapper on the right, so that `resFunctor_comp` can contract the
  -- composite into the single restriction that `conjSubgroupEquiv_inv_comp_subgroupCongr`
  -- identifies with restriction along `(conjSubgroupEquiv s H).symm`.
  change _ = Rep.resFunctor (conjSubgroupEquiv s⁻¹ (MulAut.conj s • H)).toMonoidHom ⋙
    Rep.resFunctor _
  rw [conjRepEquiv_inverse, ← resFunctor_comp, conjSubgroupEquiv_inv_comp_subgroupCongr]

end Coherence

section FDRep

variable [Ring k]

/-- Conjugating finite-dimensional representations by `s` is restriction along the isomorphism
`sHs⁻¹ ≃* H`.  The `FDRep` mirror of `conjRepFunctor`: `FDRep k H` is by definition
`Action (FGModuleCat k) H`, so the restriction functor is Mathlib's `Action.res`. -/
def conjFDRepFunctor (s : G) (H : Subgroup G) :
    FDRep k H ⥤ FDRep k (MulAut.conj s • H : Subgroup G) :=
  Action.res (FGModuleCat k) (conjSubgroupEquiv s H).toMonoidHom

/-- The conjugate of a finite-dimensional representation. -/
def conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    FDRep k (MulAut.conj s • H : Subgroup G) :=
  (conjFDRepFunctor s H).obj A

/-- Conjugation preserves the underlying module of a finite-dimensional representation. -/
@[simp]
theorem conjFDRep_V (s : G) {H : Subgroup G} (A : FDRep k H) :
    (conjFDRep s A).V = A.V := by
  -- Unfold the local wrappers to expose Mathlib's restriction carrier.
  change ((Action.res (FGModuleCat k) (conjSubgroupEquiv s H).toMonoidHom).obj A).V = A.V
  exact Action.res_obj_V _ _ _

/-- Conjugating by `1` does nothing, as an equality of functors.  The `FDRep` mirror of
`conjRepFunctor_one`. -/
theorem conjFDRepFunctor_one (H : Subgroup G) :
    conjFDRepFunctor (k := k) (1 : G) H =
      Action.res (FGModuleCat k) (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom :=
  congrArg
    (fun φ : (MulAut.conj (1 : G) • H : Subgroup G) →* H => Action.res (FGModuleCat k) φ)
    (conjSubgroupEquiv_one H)

/-- **Cocycle coherence** for finite-dimensional representations, at the level of functors.  The
`FDRep` mirror of `conjRepFunctor_mul`, and the form in which the character computations of Mackey
and Clifford theory use it. -/
theorem conjFDRepFunctor_mul (s t : G) (H : Subgroup G) :
    conjFDRepFunctor (k := k) (s * t) H =
      conjFDRepFunctor t H ⋙ conjFDRepFunctor s (MulAut.conj t • H) ⋙
        Action.res (FGModuleCat k) (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom := by
  -- As in `conjRepFunctor_mul`: unfold the `conjFDRepFunctor` wrapper to expose the homomorphism
  -- `conjSubgroupEquiv (s * t) H` that `conjSubgroupEquiv_mul` rewrites.
  change Action.res (FGModuleCat k) (conjSubgroupEquiv (s * t) H).toMonoidHom = _
  rw [conjSubgroupEquiv_mul, actionRes_comp, actionRes_comp]
  rfl

/-- Conjugating a finite-dimensional representation by `1` does nothing, once `1 · H · 1⁻¹` is
identified with `H`.  The `FDRep` mirror of `conjRep_one`. -/
theorem conjFDRep_one {H : Subgroup G} (A : FDRep k H) :
    conjFDRep (1 : G) A =
      (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (conj_one_smul H)).toMonoidHom).obj A :=
  Functor.congr_obj (conjFDRepFunctor_one H) A

/-- **Cocycle coherence** for finite-dimensional representations: `{}^{st} A = {}^s({}^t A)`, once
`(st)H(st)⁻¹` is identified with `s(tHt⁻¹)s⁻¹`.  The evaluation of `conjFDRepFunctor_mul` at
`A`. -/
theorem conjFDRep_mul (s t : G) {H : Subgroup G} (A : FDRep k H) :
    conjFDRep (s * t) A =
      (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (conj_mul_smul s t H)).toMonoidHom).obj
          (conjFDRep s (conjFDRep t A)) :=
  Functor.congr_obj (conjFDRepFunctor_mul s t H) A

/-- **Conjugation is an equivalence** `FDRep k H ≌ FDRep k (sHs⁻¹)`.  The `FDRep` mirror of
`conjRepEquiv`; here `FDRep k H` is `Action (FGModuleCat k) H`, so this is Mathlib's
`Action.resEquiv` for `conjSubgroupEquiv s H`. -/
def conjFDRepEquiv (s : G) (H : Subgroup G) :
    FDRep k H ≌ FDRep k (MulAut.conj s • H : Subgroup G) :=
  Action.resEquiv (FGModuleCat k) (conjSubgroupEquiv s H)

@[simp]
theorem conjFDRepEquiv_functor (s : G) (H : Subgroup G) :
    (conjFDRepEquiv (k := k) s H).functor = conjFDRepFunctor s H := by
  -- Unfold both wrappers to expose the restriction functor they share.
  change (Action.resEquiv (FGModuleCat k) (conjSubgroupEquiv s H)).functor =
    Action.res (FGModuleCat k) (conjSubgroupEquiv s H).toMonoidHom
  rw [Action.resEquiv_functor]
  rfl

@[simp]
theorem conjFDRepEquiv_inverse (s : G) (H : Subgroup G) :
    (conjFDRepEquiv (k := k) s H).inverse =
      Action.res (FGModuleCat k) (conjSubgroupEquiv s H).symm.toMonoidHom := by
  -- Unfold the `conjFDRepEquiv` wrapper to expose Mathlib's `Action.resEquiv`.
  change (Action.resEquiv (FGModuleCat k) (conjSubgroupEquiv s H)).inverse = _
  rw [Action.resEquiv_inverse]
  rfl

/-- The inverse of the conjugation equivalence is conjugation by `s⁻¹`, once `s⁻¹(sHs⁻¹)s` is
identified with `H`.  The `FDRep` mirror of `conjRepEquiv_inverse_eq_conjRepFunctor`. -/
theorem conjFDRepEquiv_inverse_eq_conjFDRepFunctor (s : G) (H : Subgroup G) :
    (conjFDRepEquiv (k := k) s H).inverse =
      conjFDRepFunctor s⁻¹ (MulAut.conj s • H) ⋙
        Action.res (FGModuleCat k)
          (MulEquiv.subgroupCongr (conj_inv_smul_smul s H).symm).toMonoidHom := by
  -- As in `conjRepEquiv_inverse_eq_conjRepFunctor`: unfold the `conjFDRepFunctor` wrapper so that
  -- `actionRes_comp` can contract the composite into a single restriction.
  change _ = Action.res (FGModuleCat k) (conjSubgroupEquiv s⁻¹ (MulAut.conj s • H)).toMonoidHom ⋙
    Action.res (FGModuleCat k) _
  rw [conjFDRepEquiv_inverse, ← actionRes_comp, conjSubgroupEquiv_inv_comp_subgroupCongr]

end FDRep

/-! ## The conjugate action on a finite-dimensional representation

Mathlib develops `FDRep.ρ` and the coercion of an `FDRep` to a type only over a commutative ring,
so the statements about the conjugate action and the dimension ask for `[CommRing k]`, while the
definitions and the coherence above need only `[Ring k]`. -/

section FDRepAction

variable [CommRing k]

/-- The conjugate finite-dimensional action, as a heterogeneous equality. -/
theorem conjFDRep_ρ (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjFDRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  -- Unfold the local wrappers to expose Mathlib's restriction, then read both sides through
  -- `FDRep.hom_hom_action_ρ`, which turns `FDRep.ρ` into `Action.ρ`, so that Mathlib's
  -- `Action.res_obj_ρ` supplies the precomposition and `MonoidHom.comp_apply` evaluates it.
  change HEq (FDRep.ρ ((Action.res (FGModuleCat k) (conjSubgroupEquiv s H).toMonoidHom).obj A) x) _
  refine heq_of_eq ?_
  rw [← FDRep.hom_hom_action_ρ, ← FDRep.hom_hom_action_ρ, Action.res_obj_ρ]
  exact congrArg (fun f : A.V ⟶ A.V => f.hom.hom)
    (MonoidHom.comp_apply (Action.ρ A) (conjSubgroupEquiv s H).toMonoidHom x)

/-- The conjugate action, transported along `conjFDRep_V`. -/
theorem conjFDRep_ρ_cast (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    cast (congrArg (fun V : FGModuleCat k => V →ₗ[k] V) (conjFDRep_V s A))
      ((conjFDRep s A).ρ x) = A.ρ (conjSubgroupEquiv s H x) :=
  -- The cast only moves along the carrier equality, so this is `conjFDRep_ρ` read as an equality.
  eq_of_heq ((cast_heq _ _).trans (conjFDRep_ρ s A x))

/-- Conjugation preserves the dimension (finrank) of a finite-dimensional representation. -/
@[simp]
theorem finrank_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    Module.finrank k (conjFDRep s A) = Module.finrank k A := by
  exact congrArg (fun V : FGModuleCat k => Module.finrank k V) (conjFDRep_V s A)

end FDRepAction

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
representation of: it is an endofunctor of `Rep k N`, in fact an autoequivalence, and the
coherence of the previous sections becomes a genuine left action of `G` on `Rep k N`, recorded as
a `MulAction` instance.  This is the action of `G` on `Rep k N` that Clifford theory runs on. -/

section Normal

variable {N : Subgroup G} [hN : N.Normal]

/-- Conjugating a normal subgroup by `1` is the identity automorphism.  The `MulAut.conjNormal`
form of `conj_one_smul`. -/
private theorem conjNormal_inv_one :
    (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = MonoidHom.id N :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

/-- Conjugating a normal subgroup by `s * t` is conjugating by `t` after conjugating by `s`.  The
`MulAut.conjNormal` form of `conj_mul_smul`; note the order, which is the one `Rep.res` reverses
into a left action. -/
private theorem conjNormal_inv_mul (s t : G) :
    (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom =
      (MulAut.conjNormal (t⁻¹) : MulAut N).toMonoidHom.comp
        (MulAut.conjNormal (s⁻¹) : MulAut N).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by
    simp only [MulAut.conjNormal_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    group)

/-- On a normal subgroup, the homomorphism `N →* gNg⁻¹ →* N` that `conjRep` restricts along is
`MulAut.conjNormal g⁻¹`. -/
private theorem conjSubgroupEquiv_comp_subgroupCongr (g : G) :
    (conjSubgroupEquiv g N).toMonoidHom.comp
        (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom =
      (MulAut.conjNormal (g⁻¹) : MulAut N).toMonoidHom :=
  MonoidHom.ext fun x => Subtype.ext (by simp)

section NormalRep

variable [Semiring k]

/-- Conjugation by `g` as an endofunctor of `Rep k N`: for a normal subgroup the conjugated
subgroup is `N` again, so `conjRepFunctor` becomes an endofunctor, namely restriction along
Mathlib's `MulAut.conjNormal g⁻¹`.  It is an autoequivalence; see `conjNormalRepEquiv`.

`@[expose]` because the whole point of the normal-subgroup case is that the carrier is `A.V` on
the nose, which is what lets `conjNormalRep_ρ` and its consequences be plain equalities rather
than the heterogeneous ones `conjRep_ρ` is forced into. -/
@[expose]
def conjNormalRepFunctor (g : G) : Rep k N ⥤ Rep k N :=
  Rep.resFunctor (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom

/-- The conjugate `{}^g A` of a representation of a **normal** subgroup `N`, again a
representation of `N`: the element `x : N` acts by `A.ρ (g⁻¹ x g)`.

This is `conjRep` with the conjugated subgroup identified with `N`, as `res_conjRep` records; the
conjugating automorphism is Mathlib's `MulAut.conjNormal g⁻¹`. -/
@[expose]
def conjNormalRep (g : G) (A : Rep k N) : Rep k N :=
  (conjNormalRepFunctor g).obj A

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

/-- On a normal subgroup, the conjugation functor `conjRepFunctor`, read through the
identification `gNg⁻¹ = N`, is `conjNormalRepFunctor`. -/
theorem res_conjRepFunctor (g : G) :
    conjRepFunctor (k := k) g N ⋙
        Rep.resFunctor
          (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom =
      conjNormalRepFunctor g := by
  -- Unfold the `conjRepFunctor` wrapper on the left: `resFunctor_comp` contracts the composite
  -- only once both halves are visibly `Rep.resFunctor`, and it is the resulting composite
  -- homomorphism that `conjSubgroupEquiv_comp_subgroupCongr` identifies.
  change Rep.resFunctor (conjSubgroupEquiv g N).toMonoidHom ⋙ Rep.resFunctor _ = _
  rw [← resFunctor_comp, conjSubgroupEquiv_comp_subgroupCongr]
  rfl

/-- On a normal subgroup, `conjNormalRep` is the general conjugate representation `conjRep`, read
through the identification `gNg⁻¹ = N`. -/
theorem res_conjRep (g : G) (A : Rep k N) :
    Rep.res (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom
        (conjRep g A) = conjNormalRep g A :=
  Functor.congr_obj (res_conjRepFunctor g) A

/-- Conjugating by `1` is the identity endofunctor. -/
theorem conjNormalRepFunctor_one :
    conjNormalRepFunctor (k := k) (N := N) (1 : G) = 𝟭 (Rep k N) := by
  -- `conjNormalRepFunctor 1` is by definition restriction along `MulAut.conjNormal (1 : G)⁻¹`;
  -- unfolding the wrapper is what exposes that automorphism to `conjNormal_inv_one`.
  change Rep.resFunctor (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_one]
  rfl

/-- Conjugation is a left action, as an equality of endofunctors: `{}^{st}(-) = {}^s({}^t(-))`. -/
theorem conjNormalRepFunctor_mul (s t : G) :
    conjNormalRepFunctor (k := k) (N := N) (s * t) =
      conjNormalRepFunctor t ⋙ conjNormalRepFunctor s := by
  -- Unfold the wrapper to expose `MulAut.conjNormal (s * t)⁻¹`, the automorphism
  -- `conjNormal_inv_mul` splits; `resFunctor_comp` then turns that split into a composite of
  -- functors.
  change Rep.resFunctor (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_mul, resFunctor_comp]
  rfl

/-- Conjugating by `1` is the identity. -/
@[simp]
theorem conjNormalRep_one (A : Rep k N) : conjNormalRep (1 : G) A = A :=
  Functor.congr_obj conjNormalRepFunctor_one A

/-- Conjugation is a left action: `{}^{st} A = {}^s({}^t A)`. -/
@[simp]
theorem conjNormalRep_mul (s t : G) (A : Rep k N) :
    conjNormalRep (s * t) A = conjNormalRep s (conjNormalRep t A) :=
  Functor.congr_obj (conjNormalRepFunctor_mul s t) A

/-- Conjugation by `g` is an autoequivalence of `Rep k N`, with inverse conjugation by `g⁻¹`: the
autoequivalence the roadmap asks for.  Conjugation on a normal subgroup is restriction along the
automorphism `MulAut.conjNormal g⁻¹`, so this is `resFunctorEquiv` for that automorphism, exactly
as `conjNormalFDRepEquiv` is Mathlib's `Action.resEquiv` for it.

The body is sealed; `conjNormalRepEquiv_functor` and `conjNormalRepEquiv_inverse` are the
interface identifying it with conjugation. -/
def conjNormalRepEquiv (g : G) : Rep k N ≌ Rep k N :=
  resFunctorEquiv (MulAut.conjNormal g⁻¹ : MulAut N)

@[simp]
theorem conjNormalRepEquiv_functor (g : G) :
    (conjNormalRepEquiv (k := k) (N := N) g).functor = conjNormalRepFunctor g := by
  -- Unfold the `conjNormalRepEquiv` wrapper to expose `resFunctorEquiv`.
  change (resFunctorEquiv (MulAut.conjNormal g⁻¹ : MulAut N)).functor = _
  rw [resFunctorEquiv_functor]
  rfl

@[simp]
theorem conjNormalRepEquiv_inverse (g : G) :
    (conjNormalRepEquiv (k := k) (N := N) g).inverse = conjNormalRepFunctor g⁻¹ := by
  -- Unfold the wrapper as above; the inverse is restriction along `(MulAut.conjNormal g⁻¹)⁻¹`,
  -- which `map_inv` identifies with `MulAut.conjNormal (g⁻¹)⁻¹`, as in the `FDRep` mirror.
  change (resFunctorEquiv (MulAut.conjNormal g⁻¹ : MulAut N)).inverse = _
  rw [resFunctorEquiv_inverse]
  exact congrArg (fun e : MulAut N => Rep.resFunctor (k := k) (MulEquiv.toMonoidHom e))
    (map_inv MulAut.conjNormal (g⁻¹ : G)).symm

/-- Conjugation is a left action of `G` on `Rep k N`: `g • A` is `conjNormalRep g A`.  Clifford
theory's inertia group of `A` is the stabilizer of the isomorphism class of `A`,
`{g | {}^g A ≅ A}`, rather than `MulAction.stabilizer G A`, which asks for `{}^g A = A` on the
nose; the induced action on isomorphism classes is not constructed here. -/
instance conjNormalRepMulAction : MulAction G (Rep k N) where
  smul := conjNormalRep
  one_smul := conjNormalRep_one
  mul_smul := conjNormalRep_mul

@[simp]
theorem smul_eq_conjNormalRep (g : G) (A : Rep k N) : g • A = conjNormalRep g A :=
  rfl

end NormalRep

section NormalFDRep

variable [Ring k]

/-- Conjugation by `g` as an endofunctor of `FDRep k N`.  The `FDRep` mirror of
`conjNormalRepFunctor`: `FDRep k N` is by definition `Action (FGModuleCat k) N`, so this is
Mathlib's `Action.res` along the conjugating automorphism, and the underlying module of an object
is unchanged on the nose. -/
@[expose]
def conjNormalFDRepFunctor (g : G) : FDRep k N ⥤ FDRep k N :=
  Action.res (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom

/-- The conjugate `{}^g A` of a finite-dimensional representation of a **normal** subgroup, again
a finite-dimensional representation of that subgroup. -/
@[expose]
def conjNormalFDRep (g : G) (A : FDRep k N) : FDRep k N :=
  (conjNormalFDRepFunctor g).obj A

/-- Conjugation on a normal subgroup preserves the underlying module.  Not a `simp` lemma, for the
same reason as `conjNormalRep_V`. -/
theorem conjNormalFDRep_V (g : G) (A : FDRep k N) : (conjNormalFDRep g A).V = A.V :=
  rfl

/-- On a normal subgroup, the conjugation functor `conjFDRepFunctor`, read through the
identification `gNg⁻¹ = N`, is `conjNormalFDRepFunctor`.  The `FDRep` mirror of
`res_conjRepFunctor`. -/
theorem res_conjFDRepFunctor (g : G) :
    conjFDRepFunctor (k := k) g N ⋙
        Action.res (FGModuleCat k)
          (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom =
      conjNormalFDRepFunctor g := by
  -- As in `res_conjRepFunctor`: unfold the `conjFDRepFunctor` wrapper so that `actionRes_comp`
  -- can contract the composite into a single restriction.
  change Action.res (FGModuleCat k) (conjSubgroupEquiv g N).toMonoidHom ⋙ Action.res _ _ = _
  rw [← actionRes_comp, conjSubgroupEquiv_comp_subgroupCongr]
  rfl

/-- On a normal subgroup, `conjNormalFDRep` is `conjFDRep` read through `gNg⁻¹ = N`. -/
theorem res_conjFDRep (g : G) (A : FDRep k N) :
    (Action.res (FGModuleCat k)
        (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g N).symm).toMonoidHom).obj
      (conjFDRep g A) = conjNormalFDRep g A :=
  Functor.congr_obj (res_conjFDRepFunctor g) A

/-- Conjugating by `1` is the identity endofunctor.  The `FDRep` mirror of
`conjNormalRepFunctor_one`. -/
theorem conjNormalFDRepFunctor_one :
    conjNormalFDRepFunctor (k := k) (N := N) (1 : G) = 𝟭 (FDRep k N) := by
  -- As in `conjNormalRepFunctor_one`: unfold the wrapper to expose `MulAut.conjNormal (1 : G)⁻¹`.
  change Action.res (FGModuleCat k) (MulAut.conjNormal ((1 : G)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_one]
  rfl

/-- Conjugation is a left action, as an equality of endofunctors.  The `FDRep` mirror of
`conjNormalRepFunctor_mul`. -/
theorem conjNormalFDRepFunctor_mul (s t : G) :
    conjNormalFDRepFunctor (k := k) (N := N) (s * t) =
      conjNormalFDRepFunctor t ⋙ conjNormalFDRepFunctor s := by
  -- As in `conjNormalRepFunctor_mul`: unfold the wrapper to expose `MulAut.conjNormal (s * t)⁻¹`
  -- for `conjNormal_inv_mul`.
  change Action.res (FGModuleCat k) (MulAut.conjNormal ((s * t)⁻¹) : MulAut N).toMonoidHom = _
  rw [conjNormal_inv_mul, actionRes_comp]
  rfl

/-- Conjugating by `1` is the identity. -/
@[simp]
theorem conjNormalFDRep_one (A : FDRep k N) : conjNormalFDRep (1 : G) A = A :=
  Functor.congr_obj conjNormalFDRepFunctor_one A

/-- Conjugation is a left action: `{}^{st} A = {}^s({}^t A)`. -/
@[simp]
theorem conjNormalFDRep_mul (s t : G) (A : FDRep k N) :
    conjNormalFDRep (s * t) A = conjNormalFDRep s (conjNormalFDRep t A) :=
  Functor.congr_obj (conjNormalFDRepFunctor_mul s t) A

/-- Conjugation by `g` is an autoequivalence of `FDRep k N`, with inverse conjugation by `g⁻¹`:
Mathlib's `Action.resEquiv` for the automorphism `MulAut.conjNormal g⁻¹` of `N`.

The body is sealed, as for `conjNormalRepEquiv`; `conjNormalFDRepEquiv_functor` and
`conjNormalFDRepEquiv_inverse` are the interface identifying it with conjugation. -/
def conjNormalFDRepEquiv (g : G) : FDRep k N ≌ FDRep k N :=
  Action.resEquiv (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N)

@[simp]
theorem conjNormalFDRepEquiv_functor (g : G) :
    (conjNormalFDRepEquiv (k := k) (N := N) g).functor = conjNormalFDRepFunctor g :=
  (rfl)

@[simp]
theorem conjNormalFDRepEquiv_inverse (g : G) :
    (conjNormalFDRepEquiv (k := k) (N := N) g).inverse = conjNormalFDRepFunctor g⁻¹ :=
  congrArg (fun e : MulAut N => Action.res (FGModuleCat k) (MulEquiv.toMonoidHom e))
    (map_inv MulAut.conjNormal (g⁻¹ : G)).symm

/-- Conjugation is a left action of `G` on `FDRep k N`.  The `FDRep` mirror of the `MulAction` on
`Rep k N`. -/
instance conjNormalFDRepMulAction : MulAction G (FDRep k N) where
  smul := conjNormalFDRep
  one_smul := conjNormalFDRep_one
  mul_smul := conjNormalFDRep_mul

@[simp]
theorem smul_eq_conjNormalFDRep (g : G) (A : FDRep k N) : g • A = conjNormalFDRep g A :=
  rfl

end NormalFDRep

/-! ### The conjugate action on a normal subgroup, in finite dimensions

As in the general case, `FDRep.ρ` and the coercion of an `FDRep` to a type are Mathlib API over a
commutative ring, so these statements ask for `[CommRing k]`. -/

section NormalFDRepAction

variable [CommRing k]

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

end NormalFDRepAction

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
