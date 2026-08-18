/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit
public import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# The constituents of a restriction to a normal subgroup share one multiplicity

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G` on `V`.
Restricting `ρ` to `N` breaks it into irreducible constituents, and
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit.lean` identifies *which* constituents occur:
they are the translates `TauCeti.Representation.conjSubrep ρ g σ` of any one of them, so they form a
single `G`-orbit.  This file supplies the other half of Clifford's theorem: they occur with **one
common multiplicity**.

The multiplicity of a simple `k[N]`-module `S` in a module `M` is the dimension of the hom space
`Module.finrank k (S →ₗ[k[N]] M)`, the choice-free description that
`TauCeti/RingTheory/Semisimple/Multiplicity.lean` proves counts the factors isomorphic to `S` in any
decomposition of `M`.  With that description the statement to prove is that the two hom spaces of a
subrepresentation and of its translate have the same dimension, and that is a transport statement,
not a counting one: it needs no decomposition of the restriction, no algebraically closed field, and
no finiteness.

What makes the transport work is the one identity Clifford theory runs on, `ρ g ∘ ρ n = ρ (g n g⁻¹)
∘ ρ g`.  Read on the restriction as a module over `k[N]`, it says that translation by `ρ g`
(`TauCeti.Representation.asModuleTranslate`) is not `k[N]`-linear but **semilinear over the
conjugation automorphism** `MonoidAlgebra.conjAlgAut k N g` of `k[N]`
(`TauCeti.Representation.asModuleTranslate_smul`).  A single semilinear map would not act on hom
spaces at all; but conjugating a map `f` -- precomposing with translation by `ρ g` and postcomposing
with translation back by `ρ g⁻¹` -- twists it by `conjAlgAut g` and then by `conjAlgAut g⁻¹`, and
those two twists cancel.  So `TauCeti.Representation.translateHom` really does land in `k[N]`-linear
maps, and it is a `k`-linear isomorphism of hom spaces
(`TauCeti.Representation.translateHomEquiv`).

Combining the transport with the single-orbit theorem gives the common multiplicity: any two minimal
`N`-stable subspaces are translates of one another up to isomorphism, so their hom spaces have equal
dimension.  The same argument on the subspaces themselves, where the twist is invisible because only
the `k`-action is retained, shows that all the constituents have the same **dimension** as well.

## Main definitions

* `MonoidAlgebra.conjAlgAut`: conjugation by `g : G` as an algebra automorphism of `k[N]`.
* `TauCeti.Representation.asModuleTranslate`: translation by `ρ g`, as a `k`-linear automorphism of
  the restriction to `N` viewed as a `k[N]`-module.
* `TauCeti.Representation.translateSub` and `TauCeti.Representation.translateSubEquiv`: translation
  restricted to a pair of `N`-subrepresentations that it maps into one another.
* `TauCeti.Representation.translateHom`, `TauCeti.Representation.translateHomₗ` and
  `TauCeti.Representation.translateHomEquiv`: the induced transport of hom spaces, as a function, as
  a `k`-linear map, and as a `k`-linear isomorphism.

## Main statements

* `TauCeti.Representation.asModuleTranslate_smul`: translation is semilinear over
  `MonoidAlgebra.conjAlgAut`.
* `TauCeti.Representation.finrank_hom_conjSubrep` and
  `TauCeti.Representation.finrank_asSubmodule_conjSubrep`: a translate has the same multiplicity and
  the same dimension.
* `TauCeti.Representation.finrank_hom_eq_of_isAtom`: **Clifford's theorem, multiplicity form** --
  any two irreducible `N`-constituents of an irreducible representation occur with the same
  multiplicity.
* `TauCeti.Representation.finrank_asSubmodule_eq_of_isAtom`: they also all have the same dimension.
* `TauCeti.Representation.finrank_hom_pos` and
  `TauCeti.Representation.exists_forall_finrank_hom_eq`: over a finite-dimensional `V` that common
  multiplicity is a positive natural number `e`, the `e` of the classical statement
  `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V`.

## Implementation notes

The `k[N]`-module carrying the restriction is `Representation.asModule (ρ.comp N.subtype)`, a type
synonym for `V`, and its constituents are presented as `Subrepresentation.asSubmodule` of atoms of
the lattice of `N`-subrepresentations, exactly as in `Orbit.lean`; the two presentations are matched
by `Subrepresentation.isSimpleModule_asSubmodule_iff`.  Because the synonym is not syntactically
`V`, translation is packaged as the bundled `asModuleTranslate` and not used as the bare `ρ g`: that
is what puts the `k[N]`-scalar actions in the statements below on the type where they are found.

`MonoidAlgebra.conjAlgAut` is stated for a general commutative base semiring and a general normal
subgroup, so it is declared in `MonoidAlgebra`'s own namespace next to the `domCongrAut` it is built
from, rather than under `Representation`; it lives in this file because this is the only place that
needs it, and it moves to a home of its own the moment a second consumer appears.

None of the transport results needs `[IsAlgClosed k]`, so none of them carries it: identifying
`Module.finrank k (S →ₗ[k[N]] M)` with a count of isomorphic factors does need a splitting field,
but the *equality* of two such dimensions does not, and stating it without the hypothesis keeps it
available over any field.

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

namespace MonoidAlgebra

variable (k : Type*) {G : Type*} [CommSemiring k] [Group G] (N : Subgroup G) [N.Normal]

/-- **Conjugation, read on the group algebra of a normal subgroup.**  Conjugating by `g : G`
permutes `N`, hence permutes the basis of `k[N]`, and the resulting algebra automorphism is what
translation by `ρ g` is semilinear over. -/
noncomputable def conjAlgAut : G →* (k[N] ≃ₐ[k] k[N]) :=
  (domCongrAut (R := k) (A := k) (M := N)).comp MulAut.conjNormal

variable {k N}

/-- Conjugation acts on the group-algebra basis by conjugating the group element. -/
@[simp]
theorem conjAlgAut_single (g : G) (n : N) (a : k) :
    conjAlgAut k N g (single n a) = single (MulAut.conjNormal g n) a :=
  domCongr_single _ _ _

/-- Conjugating by `g` and then by `g⁻¹` is the identity.  Not a `simp` lemma: `simp` already
proves it from `map_inv` and `AlgEquiv.symm_apply_apply`, and tagging it fails `simpNF`. -/
theorem conjAlgAut_inv_apply (g : G) (a : k[N]) :
    conjAlgAut k N g⁻¹ (conjAlgAut k N g a) = a := by
  rw [map_inv, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

end MonoidAlgebra

namespace Representation

open TauCeti.Representation
open MonoidAlgebra (conjAlgAut conjAlgAut_single conjAlgAut_inv_apply)

section Translate

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- Acting by `n ∈ N` and then by `g` is the same as acting by `g` and then by the conjugate
`g n g⁻¹`.  This is `TauCeti.Representation.apply_conjNormal_inv` read in the other direction, and
it is the single identity everything in this file rests on. -/
theorem apply_conjNormal (g : G) (n : N) (v : V) :
    ρ g (ρ (n : G) v) = ρ (MulAut.conjNormal g n : G) (ρ g v) := by
  have hg : g * (n : G) = (MulAut.conjNormal g n : G) * g := by
    rw [MulAut.conjNormal_apply]
    group
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]

/-- **Translation by `ρ g`**, read on the restriction to `N` viewed as a module over `k[N]`.  As a
map of `k`-modules it is an isomorphism, with inverse translation by `ρ g⁻¹`; it is *not*
`k[N]`-linear, only semilinear over `MonoidAlgebra.conjAlgAut k N g`
(`TauCeti.Representation.asModuleTranslate_smul`). -/
noncomputable def asModuleTranslate (g : G) :
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
theorem asModuleTranslate_apply (g : G)
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslate ρ (N := N) g v = ρ g v :=
  (rfl)

omit [N.Normal] in
/-- Translating back by `ρ g⁻¹` inverts translating by `ρ g`. -/
@[simp]
theorem asModuleTranslate_symm (g : G) :
    (asModuleTranslate ρ (N := N) g).symm = asModuleTranslate ρ (N := N) g⁻¹ :=
  LinearEquiv.ext fun _ => (rfl)

/-- **Translation is semilinear over conjugation.**  Moving a group-algebra scalar across
translation by `ρ g` conjugates it: this is `TauCeti.Representation.apply_conjNormal` extended from
the basis to all of `k[N]` by linearity.  It is the reason a single translation does not act on
`k[N]`-linear maps, and the reason a conjugate pair of translations does. -/
theorem asModuleTranslate_smul (g : G) (a : k[N])
    (v : _root_.Representation.asModule (ρ.comp N.subtype)) :
    asModuleTranslate ρ (N := N) g (a • v)
      = conjAlgAut k N g a • asModuleTranslate ρ (N := N) g v := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | single n c =>
    rw [conjAlgAut_single, _root_.Representation.single_smul,
      _root_.Representation.single_smul]
    exact (map_smul (ρ g) c _).trans (congrArg (fun w => c • w) (apply_conjNormal ρ g n v))

end Translate

section Hom

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] {ρ : Representation k G V}
  {σ τ : Subrepresentation (ρ.comp N.subtype)}

variable (ρ) in
/-- Translation by `ρ g`, restricted to a pair of `N`-subrepresentations that it maps into one
another.  The hypothesis `h` is data rather than a side condition, because which translate is being
landed in is part of what the map is. -/
noncomputable def translateSub (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    τ.asSubmodule :=
  ⟨asModuleTranslate ρ g x.1, h x.1 x.2⟩

omit [N.Normal] in
/-- The underlying vector of a translated vector. -/
@[simp]
theorem coe_translateSub (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x : σ.asSubmodule) :
    (translateSub ρ g h x : _root_.Representation.asModule (ρ.comp N.subtype))
      = asModuleTranslate ρ g x.1 :=
  (rfl)

omit [N.Normal] in
/-- Translation on subrepresentations is additive. -/
theorem translateSub_add (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (x y : σ.asSubmodule) :
    translateSub ρ g h (x + y) = translateSub ρ g h x + translateSub ρ g h y :=
  Subtype.ext (by simp)

/-- Translation on subrepresentations is semilinear over conjugation. -/
theorem translateSub_smul (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (a : k[N]) (x : σ.asSubmodule) :
    translateSub ρ g h (a • x) = conjAlgAut k N g a • translateSub ρ g h x :=
  Subtype.ext (by simp [asModuleTranslate_smul])

omit [N.Normal] in
/-- Translating and translating back is the identity on `σ`. -/
theorem translateSub_translateSub (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ)
    (x : σ.asSubmodule) : translateSub ρ g⁻¹ h' (translateSub ρ g h x) = x :=
  Subtype.ext <| by
    rw [coe_translateSub, coe_translateSub, ← asModuleTranslate_symm]
    exact (asModuleTranslate ρ (N := N) g).symm_apply_apply _

omit [N.Normal] in
/-- Translating back and translating is the identity on `τ`. -/
theorem translateSub_translateSub' (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ)
    (y : τ.asSubmodule) : translateSub ρ g h (translateSub ρ g⁻¹ h' y) = y :=
  Subtype.ext <| by
    rw [coe_translateSub, coe_translateSub, ← asModuleTranslate_symm]
    exact (asModuleTranslate ρ (N := N) g).apply_symm_apply _

variable (ρ) in
/-- **Transporting a hom space along a translation.**  Precomposing with translation by `ρ g` and
postcomposing with translation back by `ρ g⁻¹` turns a `k[N]`-linear map out of `τ` into one out of
`σ`.  Each translation is only semilinear over `k[N]`, but the two twists are `conjAlgAut g` and
`conjAlgAut g⁻¹`, which cancel, so the composite is `k[N]`-linear again. -/
noncomputable def translateHom (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :
    σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype) where
  toFun x := asModuleTranslate ρ g⁻¹ (f (translateSub ρ g h x))
  map_add' x y := by rw [translateSub_add, map_add, map_add]
  map_smul' a x := by
    rw [translateSub_smul, map_smul, asModuleTranslate_smul, conjAlgAut_inv_apply, RingHom.id_apply]

/-- Evaluation of a transported map. -/
@[simp]
theorem translateHom_apply (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ)
    (f : τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
    (x : σ.asSubmodule) :
    translateHom ρ g h f x = asModuleTranslate ρ g⁻¹ (f (translateSub ρ g h x)) :=
  (rfl)

variable (ρ) in
/-- `TauCeti.Representation.translateHom` bundled as a `k`-linear map of hom spaces. -/
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
        translateHom_apply, translateHom_apply, inv_inv, translateSub_translateSub,
        ← asModuleTranslate_symm]
      exact (asModuleTranslate ρ (N := N) g).symm_apply_apply _)
    (LinearMap.ext fun f => LinearMap.ext fun y => by
      rw [LinearMap.comp_apply, translateHomₗ_apply, translateHomₗ_apply, LinearMap.id_apply,
        translateHom_apply, translateHom_apply, inv_inv, translateSub_translateSub',
        ← asModuleTranslate_symm]
      exact (asModuleTranslate ρ (N := N) g).apply_symm_apply _)

variable (ρ) in
/-- **Translation as an isomorphism of `k`-modules.**  Only the `k`-action is retained here, and the
conjugation twist is invisible to it, so translation identifies `σ` with `τ` `k`-linearly. -/
noncomputable def translateSubEquiv (g : G) (h : ∀ v ∈ σ, ρ g v ∈ τ) (h' : ∀ v ∈ τ, ρ g⁻¹ v ∈ σ) :
    σ.asSubmodule ≃ₗ[k] τ.asSubmodule where
  toFun := translateSub ρ g h
  map_add' := translateSub_add g h
  map_smul' c x := Subtype.ext (by simp)
  invFun := translateSub ρ g⁻¹ h'
  left_inv := translateSub_translateSub g h h'
  right_inv := translateSub_translateSub' g h h'

end Hom

section Clifford

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- Translation by `ρ g` carries `σ` into its translate; the converse inclusion is
`TauCeti.Representation.mem_conjSubrep_iff`. -/
theorem apply_mem_conjSubrep (g : G) {σ : Subrepresentation (ρ.comp N.subtype)} {v : V}
    (hv : v ∈ σ) : ρ g v ∈ conjSubrep ρ g σ :=
  mem_conjSubrep_iff.mpr (by rwa [_root_.Representation.inv_self_apply])

/-- **A translate occurs with the same multiplicity.**  The hom space out of `conjSubrep ρ g σ` and
the hom space out of `σ` have the same dimension over `k`.  No irreducibility, finiteness or
algebraic closedness is involved: this is transport along translation. -/
theorem finrank_hom_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Module.finrank k
        ((conjSubrep ρ g σ).asSubmodule →ₗ[k[N]]
          _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) :=
  (translateHomEquiv ρ g (fun _ hv => apply_mem_conjSubrep ρ g hv)
    (fun _ hv => mem_conjSubrep_iff.mp hv)).finrank_eq

/-- **Clifford's theorem, multiplicity form.**  Any two minimal `N`-stable subspaces of an
irreducible representation occur in the restriction with the same multiplicity.  By the single-orbit
theorem one is isomorphic to a translate of the other, and a translate has the same multiplicity. -/
theorem finrank_hom_eq_of_isAtom [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    Module.finrank k (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype))
      = Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ
  rw [← finrank_hom_conjSubrep ρ g σ,
    (LinearEquiv.congrLeft (_root_.Representation.asModule (ρ.comp N.subtype)) k e).finrank_eq]


/-- **A translate has the same dimension.** -/
theorem finrank_asSubmodule_conjSubrep (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    Module.finrank k ↥(conjSubrep ρ g σ).asSubmodule = Module.finrank k ↥σ.asSubmodule :=
  ((translateSubEquiv ρ g (fun _ hv => apply_mem_conjSubrep ρ g hv)
    (fun _ hv => mem_conjSubrep_iff.mp hv)).symm).finrank_eq

/-- **The constituents all have the same dimension.**  The companion of the multiplicity statement:
by the single-orbit theorem the minimal `N`-stable subspaces of an irreducible representation are
translates of one another up to isomorphism, and translation is a `k`-linear isomorphism. -/
theorem finrank_asSubmodule_eq_of_isAtom [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    Module.finrank k ↥σ.asSubmodule = Module.finrank k ↥τ.asSubmodule := by
  obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ
  rw [← finrank_asSubmodule_conjSubrep ρ g σ, ← (e.restrictScalars k).finrank_eq]

omit [N.Normal] in
/-- A nonzero `N`-subrepresentation has a nonzero map into the restriction. -/
theorem nontrivial_hom_of_ne_bot {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    Nontrivial (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ σ.asSubmodule, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hσ (Subrepresentation.toSubmodule_injective
      (Submodule.eq_bot_iff _ |>.mpr fun v hv => hcon v hv))
  exact ⟨σ.asSubmodule.subtype, 0, fun hzero => hv0 (by
    simpa using congrFun (congrArg DFunLike.coe hzero) ⟨v, hv⟩)⟩

omit [N.Normal] in
/-- The hom space is finite-dimensional over `k` once `V` is: it sits inside the space of all
`k`-linear maps by forgetting the group-algebra action. -/
theorem finiteDimensional_hom [FiniteDimensional k V] (σ : Subrepresentation (ρ.comp N.subtype)) :
    FiniteDimensional k
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  have hσ : Module.Finite k ↥σ.asSubmodule :=
    .of_injective (σ.asSubmodule.subtype.restrictScalars k) Subtype.val_injective
  have hV : Module.Finite k (_root_.Representation.asModule (ρ.comp N.subtype)) :=
    inferInstance
  exact .of_injective
    (LinearMap.restrictScalarsₗ k k[N] ↥σ.asSubmodule
      (_root_.Representation.asModule (ρ.comp N.subtype)) k)
    fun f g hfg => LinearMap.ext fun x => DFunLike.congr_fun hfg x

omit [N.Normal] in
/-- **A nonzero constituent has positive multiplicity.** -/
theorem finrank_hom_pos [FiniteDimensional k V] {σ : Subrepresentation (ρ.comp N.subtype)}
    (hσ : σ ≠ ⊥) :
    0 < Module.finrank k
      (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) := by
  have := finiteDimensional_hom ρ σ
  have := nontrivial_hom_of_ne_bot ρ hσ
  exact Module.finrank_pos

/-- **Clifford's theorem, the common multiplicity.**  For a finite-dimensional irreducible `ρ` there
is a positive natural number `e` -- the `e` of the classical decomposition `Res_N W ≅ e · ⨁ᵢ {}^{gᵢ}
V` -- with which every irreducible `N`-constituent of the restriction occurs. -/
theorem exists_forall_finrank_hom_eq [ρ.IsIrreducible] [FiniteDimensional k V] :
    ∃ e : ℕ, 0 < e ∧ ∀ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ →
      Module.finrank k
        (σ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e := by
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] _
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨σ₀, hσ₀⟩ := exists_isAtom (ρ.comp N.subtype)
  exact ⟨_, finrank_hom_pos ρ hσ₀.1, fun σ hσ => finrank_hom_eq_of_isAtom ρ hσ hσ₀⟩

end Clifford

end Representation
