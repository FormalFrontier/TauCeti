/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.MonoidAlgebra.Conjugation
public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit

/-!
# The constituents of a restriction to a normal subgroup share one multiplicity

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G` on `V`.
Restricting `ρ` to `N` breaks it into irreducible constituents, and
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit.lean` identifies *which* constituents occur:
they are the translates `TauCeti.Representation.conjSubrep ρ g σ` of any one of them, so they form a
single `G`-orbit.  This file supplies the other half of Clifford's theorem: they occur with **one
common multiplicity**.

The multiplicity of a simple `k[N]`-module `S` in a module `M` is read here off the dimension of the
hom space, `Module.finrank k (S →ₗ[k[N]] M)`.  That dimension is the classical multiplicity itself
only when `k` splits `S`: in general it is the multiplicity times `Module.finrank k` of the division
ring `End_{k[N]}(S)`.  Accordingly `TauCeti/RingTheory/Semisimple/Multiplicity.lean` identifies it
with a count of the factors isomorphic to `S` only for an algebraically closed `k`, a
finite-dimensional `S` and a *finite* decomposition of `M`, the case in which that division ring is
`k` itself.  Everything below instead compares two such dimensions for two constituents of the
*same* restriction, and that comparison is a transport statement rather than a counting one: it
needs no decomposition of the restriction, no algebraically closed field and no finiteness, so no
such hypothesis is imposed.  Over a splitting field the comparison is literally the equality of the
classical multiplicities; in general it is the equality of their `End`-weighted forms.

What makes the transport work is the one identity Clifford theory runs on, `ρ g ∘ ρ n = ρ (g n g⁻¹)
∘ ρ g` (`TauCeti.Representation.apply_conjNormal_inv`, read in the other direction).  On the
restriction viewed as a module over `k[N]`, it says that translation by `ρ g`
(`Representation.asModuleTranslateEquiv`) is not `k[N]`-linear but **semilinear over the conjugation
automorphism** `MonoidAlgebra.conjAlgAut k N g` of `k[N]`
(`Representation.asModuleTranslateEquiv_smul`).  A single semilinear map would not act on hom spaces
at all; but conjugating a map `f` -- precomposing with translation by `ρ g` and postcomposing with
translation back by `ρ g⁻¹` -- twists it by `conjAlgAut g` and then by `conjAlgAut g⁻¹`, and those
two twists cancel.  So `Representation.translateHom` really does land in `k[N]`-linear maps, and it
is a `k`-linear isomorphism of hom spaces (`Representation.translateHomEquiv`).

Combining the transport with the single-orbit theorem gives the common multiplicity: any two minimal
`N`-stable subspaces are translates of one another up to isomorphism, so their hom spaces have equal
dimension.  The same argument on the subspaces themselves, where the twist is invisible because only
the `k`-action is retained, shows that all the constituents have the same **dimension** as well;
there it is `TauCeti.Representation.conjSubrepEquiv` from `Clifford/Basic.lean` that does the work.

## Main definitions

* `Representation.asModuleTranslateEquiv`: translation by `ρ g`, as a `k`-linear automorphism of the
  restriction to `N` viewed as a `k[N]`-module.
* `Representation.translateSubrep`: translation restricted to a pair of `N`-subrepresentations that
  it maps into one another.
* `Representation.translateHom`, `Representation.translateHomₗ` and
  `Representation.translateHomEquiv`: the induced transport of hom spaces, as a function, as a
  `k`-linear map, and as a `k`-linear isomorphism.

## Main statements

* `Representation.asModuleTranslateEquiv_smul`: translation is semilinear over
  `MonoidAlgebra.conjAlgAut`.
* `Representation.finrank_linearMap_conjSubrep` and `Representation.finrank_asSubmodule_conjSubrep`:
  a translate has a hom space of the same dimension, and is itself of the same dimension.
* `Representation.finrank_linearMap_eq_of_isAtom`: **Clifford's theorem, multiplicity form** -- the
  hom spaces of any two irreducible `N`-constituents of an irreducible representation have the same
  dimension, so over a splitting field the constituents occur with the same multiplicity.
* `Representation.finrank_asSubmodule_eq_of_isAtom`: they also all have the same dimension.
* `Representation.finrank_linearMap_pos` and `Representation.exists_forall_finrank_linearMap_eq`:
  over a finite-dimensional `V` that common dimension is a positive natural number `e`, the `e` of
  the classical statement `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V` when `k` is a splitting field.

## Implementation notes

The `k[N]`-module carrying the restriction is `Representation.asModule (ρ.comp N.subtype)`, a type
synonym for `V`, and its constituents are presented as `Subrepresentation.asSubmodule` of atoms of
the lattice of `N`-subrepresentations, exactly as in `Orbit.lean`; the two presentations are matched
by `Subrepresentation.isSimpleModule_asSubmodule_iff`.  Because the synonym is not syntactically
`V`, translation is packaged as the bundled `asModuleTranslateEquiv` and not used as the bare `ρ g`:
that is what puts the `k[N]`-scalar actions in the statements below on the type where they are
found.

The declarations here extend Mathlib's `Representation` namespace, so they are declared into it
directly rather than into `TauCeti.Representation`, which would lose dot notation and be rejected by
`scripts/lint-dot-notation.py`.  The transport itself asks only for a commutative base semiring and
an additive commutative monoid; a field enters only where `Orbit.lean`'s single-orbit theorem does.

## References

This proves the multiplicity half of the **Clifford's theorem** milestone of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`: "its irreducible
`N`-constituents form a single `G`-orbit, all with the same multiplicity `e`".  The remaining part
of that milestone, the packaged decomposition `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V` indexed by a transversal
of the inertia group, is not proved here.

The mathematics is the classical argument of C. W. Curtis and I. Reiner, *Representation Theory of
Finite Groups and Associative Algebras*, §49.
-/

public section

open scoped MonoidAlgebra

open TauCeti

namespace Representation

open TauCeti.Representation
open MonoidAlgebra (conjAlgAut conjAlgAut_single conjAlgAut_inv_self_apply)

section Translate

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **Translation by `ρ g`**, read on the restriction to `N` viewed as a module over `k[N]`.  As a
map of `k`-modules it is an isomorphism, with inverse translation by `ρ g⁻¹`; it is *not*
`k[N]`-linear, only semilinear over `MonoidAlgebra.conjAlgAut k N g`
(`Representation.asModuleTranslateEquiv_smul`). -/
noncomputable def asModuleTranslateEquiv (g : G) :
    _root_.Representation.asModule (ρ.comp N.subtype) ≃ₗ[k]
      _root_.Representation.asModule (ρ.comp N.subtype) where
  toFun v := ρ g v
  map_add' x y := map_add (ρ g) x y
  map_smul' c x := map_smul (ρ g) c x
  invFun v := ρ g⁻¹ v
  left_inv v := _root_.Representation.inv_self_apply ρ g v
  right_inv v := _root_.Representation.self_inv_apply ρ g v

omit [N.Normal] in
/-- Translation is given by `ρ g`.  Not a `simp` lemma: rewriting with it moves a term off the
type synonym `Representation.asModule`, where the `k[N]`-action lives. -/
theorem asModuleTranslateEquiv_apply (g : G)
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslateEquiv ρ (N := N) g v = ρ g v :=
  (rfl)

omit [N.Normal] in
/-- Translating back by `ρ g⁻¹` inverts translating by `ρ g`. -/
@[simp]
theorem asModuleTranslateEquiv_symm (g : G) :
    (asModuleTranslateEquiv ρ (N := N) g).symm = asModuleTranslateEquiv ρ (N := N) g⁻¹ :=
  LinearEquiv.ext fun _ => (rfl)

omit [N.Normal] in
/-- Translating by `ρ g` and back by `ρ g⁻¹` is the identity. -/
theorem asModuleTranslateEquiv_inv_self_apply (g : G)
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslateEquiv ρ (N := N) g⁻¹ (asModuleTranslateEquiv ρ (N := N) g v) = v :=
  _root_.Representation.inv_self_apply ρ g v

omit [N.Normal] in
/-- Translating by `ρ g⁻¹` and back by `ρ g` is the identity. -/
theorem asModuleTranslateEquiv_self_inv_apply (g : G)
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslateEquiv ρ (N := N) g (asModuleTranslateEquiv ρ (N := N) g⁻¹ v) = v :=
  _root_.Representation.self_inv_apply ρ g v

/-- **Translation is semilinear over conjugation.**  Moving a group-algebra scalar across
translation by `ρ g` conjugates it: this is the conjugation identity
`TauCeti.Representation.apply_conjNormal_inv`, extended from the basis to all of `k[N]` by
linearity.  It is the reason a single translation does not act on `k[N]`-linear maps, and the reason
a conjugate pair of translations does. -/
theorem asModuleTranslateEquiv_smul (g : G) (a : k[N])
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslateEquiv ρ (N := N) g (a • v)
      = conjAlgAut k N g a • asModuleTranslateEquiv ρ (N := N) g v := by
  -- `apply_conjNormal_inv` read in the other direction: acting by `n` and then by `g` is acting by
  -- `g` and then by the conjugate `g n g⁻¹`.
  have hconj : ∀ (n : N) (w : V), ρ g (ρ (n : G) w) = ρ (MulAut.conjNormal g n : G) (ρ g w) :=
    fun n w => by
      have h := apply_conjNormal_inv ρ g (MulAut.conjNormal g n) w
      rwa [map_inv, MulAut.inv_apply_self] at h
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | single n c =>
    -- After `single_smul` both sides read on `V` again, through `ρ.asModuleEquiv`, which is
    -- `LinearEquiv.refl` and so disappears definitionally; there is no lemma to rewrite it away.
    rw [conjAlgAut_single, asModuleTranslateEquiv_apply, _root_.Representation.single_smul,
      _root_.Representation.single_smul]
    exact (map_smul (ρ g) c _).trans (congrArg (fun w => c • w) (hconj n _))

end Translate

section Hom

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] {ρ : Representation k G V}
  {σ τ : Subrepresentation (ρ.comp N.subtype)}

variable (ρ) in
/-- Translation by `ρ g`, restricted to a pair of `N`-subrepresentations that it maps into one
another.  The hypothesis `h` is data rather than a side condition, because which translate is being
landed in is part of what the map is. -/
noncomputable def translateSubrep (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    τ.asSubmodule :=
  ⟨asModuleTranslateEquiv ρ g x.1, h x.1 x.2⟩

omit [N.Normal] in
/-- The underlying vector of a translated vector. -/
@[simp]
theorem coe_translateSubrep (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    (translateSubrep ρ g h x : _root_.Representation.asModule (ρ.comp N.subtype))
      = asModuleTranslateEquiv ρ g x.1 :=
  (rfl)

omit [N.Normal] in
/-- Translation on subrepresentations is additive. -/
theorem translateSubrep_add (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x y : σ.asSubmodule) :
    translateSubrep ρ g h (x + y) = translateSubrep ρ g h x + translateSubrep ρ g h y :=
  Subtype.ext (by simp)

/-- Translation on subrepresentations is semilinear over conjugation. -/
theorem translateSubrep_smul (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (a : k[N]) (x : σ.asSubmodule) :
    translateSubrep ρ g h (a • x) = conjAlgAut k N g a • translateSubrep ρ g h x :=
  Subtype.ext (by simp [asModuleTranslateEquiv_smul])

omit [N.Normal] in
/-- Translating and translating back is the identity on `σ`. -/
theorem translateSubrep_inv_translateSubrep (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) (x : σ.asSubmodule) :
    translateSubrep ρ g⁻¹ h' (translateSubrep ρ g h x) = x :=
  Subtype.ext <| by
    rw [coe_translateSubrep, coe_translateSubrep]
    exact asModuleTranslateEquiv_inv_self_apply ρ g _

omit [N.Normal] in
/-- Translating back and translating is the identity on `τ`. -/
theorem translateSubrep_translateSubrep_inv (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) (y : τ.asSubmodule) :
    translateSubrep ρ g h (translateSubrep ρ g⁻¹ h' y) = y :=
  Subtype.ext <| by
    rw [coe_translateSubrep, coe_translateSubrep]
    exact asModuleTranslateEquiv_self_inv_apply ρ g _

variable (ρ) in
/-- **Transporting a hom space along a translation.**  Precomposing with translation by `ρ g` and
postcomposing with translation back by `ρ g⁻¹` turns a `k[N]`-linear map out of `τ` into one out of
`σ`.  Each translation is only semilinear over `k[N]`, but the two twists are `conjAlgAut g` and
`conjAlgAut g⁻¹`, which cancel, so the composite is `k[N]`-linear again. -/
noncomputable def translateHom (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :
    σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype) where
  toFun x := asModuleTranslateEquiv ρ g⁻¹ (f (translateSubrep ρ g h x))
  map_add' x y := by rw [translateSubrep_add, map_add, map_add]
  map_smul' a x := by
    rw [translateSubrep_smul, map_smul, asModuleTranslateEquiv_smul, conjAlgAut_inv_self_apply,
      RingHom.id_apply]

/-- Evaluation of a transported map. -/
@[simp]
theorem translateHom_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
    (x : σ.asSubmodule) :
    translateHom ρ g h f x = asModuleTranslateEquiv ρ g⁻¹ (f (translateSubrep ρ g h x)) :=
  (rfl)

variable (ρ) in
/-- `Representation.translateHom` bundled as a `k`-linear map of hom spaces. -/
noncomputable def translateHomₗ (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) :
    (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) →ₗ[k]
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) where
  toFun := translateHom ρ g h
  map_add' f₁ f₂ := LinearMap.ext fun x => by
    simp only [translateHom_apply, LinearMap.add_apply, map_add]
  map_smul' c f := LinearMap.ext fun x => by
    simp only [translateHom_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

/-- The bundled transport is the unbundled one. -/
@[simp]
theorem translateHomₗ_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :
    translateHomₗ ρ g h f = translateHom ρ g h f :=
  (rfl)

variable (ρ) in
/-- **The hom spaces out of two translates are `k`-linearly isomorphic.**  Translation by `ρ g`
identifies the space of `k[N]`-linear maps out of `τ` with the space of `k[N]`-linear maps out of
`σ`, with inverse the transport along translation by `ρ g⁻¹`. -/
noncomputable def translateHomEquiv (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) :
    (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) ≃ₗ[k]
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  LinearEquiv.ofLinearMap (translateHomₗ ρ g h) (translateHomₗ ρ g⁻¹ h')
    (LinearMap.ext fun f => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, translateHomₗ_apply, translateHomₗ_apply, LinearMap.id_apply,
        translateHom_apply, translateHom_apply, inv_inv, translateSubrep_inv_translateSubrep]
      exact asModuleTranslateEquiv_inv_self_apply ρ g _)
    (LinearMap.ext fun f => LinearMap.ext fun y => by
      rw [LinearMap.comp_apply, translateHomₗ_apply, translateHomₗ_apply, LinearMap.id_apply,
        translateHom_apply, translateHom_apply, inv_inv, translateSubrep_translateSubrep_inv]
      exact asModuleTranslateEquiv_self_inv_apply ρ g _)

end Hom

section Conjugate

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **A translate has a hom space of the same dimension.**  The hom space out of
`conjSubrep ρ g σ` and the hom space out of `σ` have the same dimension over `k`; over a splitting
field this says that a translate occurs with the same multiplicity.  No irreducibility, finiteness
or algebraic closedness is involved: this is transport along translation. -/
@[simp]
theorem finrank_linearMap_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Module.finrank k
        ((conjSubrep ρ g σ).asSubmodule →ₗ[k[N]]
          _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  (translateHomEquiv ρ g
    (fun _ hv => mem_conjSubrep_iff.mpr (by rwa [_root_.Representation.inv_self_apply]))
    (fun _ hv => mem_conjSubrep_iff.mp hv)).finrank_eq

/-- **A translate has the same dimension.**  This is the `k`-linear content of
`TauCeti.Representation.conjSubrepEquiv`, whose underlying map is again translation by `ρ g`. -/
@[simp]
theorem finrank_asSubmodule_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Module.finrank k ↥(conjSubrep ρ g σ).asSubmodule = Module.finrank k ↥σ.asSubmodule :=
  ((conjSubrepEquiv ρ g σ).toLinearEquiv).finrank_eq.symm

end Conjugate

section Clifford

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **Clifford's theorem, multiplicity form.**  The hom spaces of any two minimal `N`-stable
subspaces of an irreducible representation have the same dimension; over a splitting field this says
that the two constituents occur in the restriction with the same multiplicity.  By the single-orbit
theorem one is isomorphic to a translate of the other, and a translate transports. -/
theorem finrank_linearMap_eq_of_isAtom [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    Module.finrank k (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ
  rw [← finrank_linearMap_conjSubrep ρ g σ,
    (LinearEquiv.congrLeft (_root_.Representation.asModule (ρ.comp N.subtype)) k e).finrank_eq]

/-- **The constituents all have the same dimension.**  The companion of the multiplicity statement:
by the single-orbit theorem the minimal `N`-stable subspaces of an irreducible representation are
translates of one another up to isomorphism, and translation is a `k`-linear isomorphism. -/
theorem finrank_asSubmodule_eq_of_isAtom [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    Module.finrank k ↥σ.asSubmodule = Module.finrank k ↥τ.asSubmodule := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ
  rw [← finrank_asSubmodule_conjSubrep ρ g σ, ← (e.restrictScalars k).finrank_eq]

omit [N.Normal] in
/-- **A nonzero `N`-subrepresentation has a positive-dimensional hom space.**  Over a splitting
field this says that a nonzero subrepresentation has positive multiplicity. -/
theorem finrank_linearMap_pos [FiniteDimensional k V] {σ : Subrepresentation (ρ.comp N.subtype)}
    (hσ : σ ≠ ⊥) :
    0 < Module.finrank k
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  -- Once the source is finite-dimensional, `LinearMap.finiteDimensional'` finishes: the hom space
  -- sits inside the space of all `k`-linear maps by forgetting the `k[N]`-action.
  have : Module.Finite k ↥σ.asSubmodule :=
    .of_injective (σ.asSubmodule.subtype.restrictScalars k) Subtype.val_injective
  -- The inclusion of a nonzero `σ` is a nonzero element of the hom space.
  have hbot : σ.asSubmodule ≠ ⊥ := fun hc =>
    hσ (Subrepresentation.subrepresentationSubmoduleOrderIso.injective
      (hc.trans Subrepresentation.subrepresentationSubmoduleOrderIso.map_bot.symm))
  obtain ⟨v, hv, hv0⟩ := σ.asSubmodule.ne_bot_iff.mp hbot
  have : Nontrivial (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
    ⟨σ.asSubmodule.subtype, 0, fun hzero =>
      hv0 (by simpa using DFunLike.congr_fun hzero ⟨v, hv⟩)⟩
  exact Module.finrank_pos

/-- **Clifford's theorem, the common multiplicity.**  For a finite-dimensional irreducible `ρ` there
is a positive natural number `e` with which every irreducible `N`-constituent of the restriction
occurs: the hom space of every constituent has dimension `e`.  Over a splitting field this `e` is
the `e` of the classical decomposition `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V`. -/
theorem exists_forall_finrank_linearMap_eq [ρ.IsIrreducible] [FiniteDimensional k V] :
    ∃ e : ℕ, 0 < e ∧ ∀ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ →
      Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e := by
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAtom_forall_nonempty_linearEquiv_conjSubrep ρ (N := N)
  exact ⟨_, finrank_linearMap_pos ρ hσ₀.1, fun σ hσ => finrank_linearMap_eq_of_isAtom ρ hσ hσ₀⟩

end Clifford

end Representation
