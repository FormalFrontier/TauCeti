/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Basic

/-!
# A projective representation is a linear representation of the central extension of its factor set

A projective representation `ρ : G → (V ≃ₗ[k] V)` with factor set `α` is multiplicative only up to
the scalars `α`, so it is not a homomorphism. Enlarging `G` by those scalars repairs this: the
central extension `1 → kˣ → E_α → G → 1` built from `α` in
`TauCeti/GroupTheory/GroupExtension/Of/FactorSet.lean` carries a genuine homomorphism

`E_α → (V ≃ₗ[k] V)`, `⟨a, g⟩ ↦ a • ρ g`,

the **linearization** of `ρ`. This file builds it, and shows that nothing is lost: the projective
representation is recovered by restricting the linearization along the canonical section
`g ↦ ⟨1, g⟩`, and the two constructions are mutually inverse. The linear representations of `E_α`
that arise this way are exactly those under which the central copy of `kˣ` acts by its own scalars,
so `TauCeti.isProjectiveRepEquivExtensionHom` is a bijection between the projective representations
of `G` with factor set `α` and the linear representations of `E_α` with that property.

Two bookkeeping bridges are needed first, because the two halves of the theory spell a factor set
differently. `TauCeti.FactorSet` is the uncurried, bundled `G × G → M` of a general `G`-module `M`,
which is what the group extension is built from, while `TauCeti.IsFactorSet` is a curried
`Prop`-valued class on `G → G → kˣ`, which is what a projective representation carries. The two
agree when `G` acts **trivially** on `kˣ`, the case in which the extension is central
(`TauCeti.FactorSet.inl_range_le_center`), and `TauCeti.FactorSet.isFactorSet_curry` and
`TauCeti.IsFactorSet.toFactorSet` translate in the two directions. Triviality of the action is
carried as an explicit hypothesis `∀ (g : G) (a : kˣ), g • a = a` rather than as a chosen instance,
matching `TauCeti.FactorSet.inl_range_le_center`: the *type* `TauCeti.FactorSet G kˣ` already
depends on an ambient `MulDistribMulAction G kˣ`, so leaving that action free lets a factor set for
any action be fed to the statements, and only the results that genuinely need centrality pay for
it. A projective representation itself carries no action, so the closing existence statement
supplies the trivial one, `TauCeti.trivialMulDistribMulAction`, and asks for nothing of its caller.

## Main definitions

* `TauCeti.trivialMulDistribMulAction`: the trivial action, the one a projective representation's
  own factor set is bundled over, since a projective representation carries no action.
* `TauCeti.IsFactorSet.toFactorSet`: a normalized curried factor set, bundled as a
  `TauCeti.FactorSet` for a trivial action, so that its central extension is available.
* `TauCeti.IsProjectiveRep.linearization`: the homomorphism `E_α → (V ≃ₗ[k] V)` attached to a
  projective representation with factor set `α`, with
  `TauCeti.IsProjectiveRep.linearizationRepresentation` its packaging as a
  `Representation k E_α V`.
* `TauCeti.FactorSet.restrictCanonicalSection`: the restriction of a `Representation k E_α V` along
  the canonical section, as linear automorphisms of `V`, the form in which it is a projective
  representation.
* `TauCeti.isProjectiveRepEquivExtensionHom`: the resulting bijection.

## Main results

* `TauCeti.FactorSet.isFactorSet_curry`: for a trivial action a `TauCeti.FactorSet` valued in `kˣ`
  is a normalized factor set in the curried sense of `TauCeti.IsFactorSet`.
* `TauCeti.IsProjectiveRep.linearization_mk_one`: restricting the linearization along the canonical
  section returns the projective representation, and
  `TauCeti.IsProjectiveRep.linearization_inl`: the central `kˣ` acts by its own scalars.
* `TauCeti.isProjectiveRep_comp_canonicalSection`: conversely, restricting along the canonical
  section any linear representation of `E_α` under which `kˣ` acts by scalars gives a projective
  representation with factor set `α`, and
  `TauCeti.isProjectiveRep_of_representation_canonicalSection`: the same for a linear representation
  presented as an ordinary `Representation k E_α V`, whose scalar condition is read off the
  linearization by `TauCeti.IsProjectiveRep.linearizationRepresentation_inl`, with
  `TauCeti.isProjectiveRep_restrictCanonicalSection` its instance at the canonical restriction.
* `TauCeti.IsProjectiveRep.forall_linearization_mem_iff`: the linearization and the projective
  representation have the same invariant submodules, which is why irreducibility transfers between
  them.
* `TauCeti.IsProjectiveRep.exists_factorSet_linearization`: **every projective representation of
  `G` is a linear representation of a central extension of `G` by `kˣ`**, for the extension built
  from the factor set the projective representation carries.

## References

This is the linearization step of Layer 7 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/InductionRestriction/README.md),
"projective representations, factor sets, and the Schur multiplier": it is the mechanism behind the
representation group, through which every projective representation of `G` lifts to an ordinary
linear representation of a central extension.

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
  [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

/-!
## Factor sets, curried and uncurried

The extension is built from a bundled, uncurried factor set while a projective representation
carries a curried one; for the trivial action, defined first, the two notions agree.
-/

/-- **The trivial action of a monoid `G` on a monoid `M`**, `g • a = a`, obtained by composing the
tautological action of `MulAut M` with the trivial homomorphism. It is the action for which the
extension built from a factor set is central, so it is the one a projective representation's factor
set is bundled over in `TauCeti.IsProjectiveRep.exists_factorSet_linearization`. It is reducible and
deliberately not an instance, since the results below are stated for an arbitrary action; it is only
used to supply one where the ambient theory has none. -/
abbrev trivialMulDistribMulAction (G M : Type*) [Monoid G] [Monoid M] :
    MulDistribMulAction G M :=
  MulDistribMulAction.compHom M (1 : G →* MulAut M)

section TrivialActionSmul

attribute [local instance] trivialMulDistribMulAction

/-- Under `TauCeti.trivialMulDistribMulAction` every element is fixed. This is the triviality
hypothesis that `TauCeti.FactorSet.isFactorSet_curry`, `TauCeti.IsFactorSet.toFactorSet` and
`TauCeti.FactorSet.inl_range_le_center` take, supplied once so that their callers can name a
constant rather than an inlined proof. -/
@[simp]
theorem trivialMulDistribMulAction_smul {G M : Type*} [Monoid G] [Monoid M] (g : G) (a : M) :
    g • a = a :=
  rfl

end TrivialActionSmul

section GeneralAction

variable [MulDistribMulAction G kˣ]

/-- **A factor set valued in `kˣ` for the trivial action is a normalized factor set in the curried
sense of `TauCeti.IsFactorSet`.** The cocycle identity of `TauCeti.FactorSet` carries an action on
one of its four terms, which the hypothesis removes; the two normalizations agree. -/
theorem FactorSet.isFactorSet_curry (α : FactorSet G kˣ)
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) : IsFactorSet (Function.curry ⇑α) where
  cocycle g h j := by simpa [Function.curry, htriv] using α.isMulCocycle₂ g h j
  one_left g := α.map_one_fst g
  one_right g := α.map_one_snd g

/-- **A normalized factor set in the curried sense of `TauCeti.IsFactorSet`, bundled as a
`TauCeti.FactorSet`** for a trivial action of `G` on `kˣ`. This is what makes the central extension
`TauCeti.FactorSet.Extension` of the factor set of a projective representation available. -/
def IsFactorSet.toFactorSet (α : G → G → kˣ) [IsFactorSet α]
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) : FactorSet G kˣ where
  toFun p := α p.1 p.2
  isMulCocycle₂' g h j := by simpa [htriv] using IsFactorSet.cocycle (α := α) g h j
  map_one_one' := IsFactorSet.one_left (α := α) 1

/-- The bundled factor set of a curried one takes the same values. -/
@[simp]
theorem IsFactorSet.toFactorSet_apply (α : G → G → kˣ) [IsFactorSet α]
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) (p : G × G) :
    IsFactorSet.toFactorSet α htriv p = α p.1 p.2 :=
  (rfl)

/-- Bundling a curried factor set and currying it back returns it unchanged, so a projective
representation with factor set `α` is one with the factor set of
`TauCeti.IsFactorSet.toFactorSet`. -/
@[simp]
theorem IsFactorSet.curry_coe_toFactorSet (α : G → G → kˣ) [IsFactorSet α]
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) :
    Function.curry ⇑(IsFactorSet.toFactorSet α htriv) = α :=
  (rfl)

/-!
## The linearization of a projective representation

Multiplying by the scalar recorded in the `kˣ`-component of the extension repairs the failure of
`ρ` to be multiplicative, because that failure is exactly the factor set the extension is twisted
by.
-/

section Linearization

variable {α : FactorSet G kˣ} {ρ : G → V ≃ₗ[k] V}

namespace IsProjectiveRep

/-- **The linearization of a projective representation with factor set `α`**: the homomorphism from
the central extension `E_α` of `G` by `kˣ` to the linear automorphisms of `V`, sending `⟨a, g⟩` to
`a • ρ g`. It is multiplicative precisely because the extension is twisted by the same factor set
that measures the failure of `ρ` to be multiplicative. -/
def linearization (hρ : IsProjectiveRep ρ (Function.curry ⇑α))
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) : α.Extension →* (V ≃ₗ[k] V) where
  toFun x := LinearEquiv.smulOfUnit x.left * ρ x.right
  map_one' := LinearEquiv.ext fun v ↦ by
    simp [LinearEquiv.smulOfUnit_apply, hρ.map_one]
  map_mul' x y := LinearEquiv.ext fun v ↦ by
    have hmul : ρ x.right (ρ y.right v)
        = (α (x.right, y.right) : k) • ρ (x.right * y.right) v :=
      hρ.mul_apply x.right y.right v
    simp only [LinearEquiv.mul_apply, LinearEquiv.smulOfUnit_apply, FactorSet.Extension.mul_left,
      FactorSet.Extension.mul_right, htriv, Units.val_mul, map_smul, hmul, smul_smul, mul_assoc,
      mul_comm]

variable (hρ : IsProjectiveRep ρ (Function.curry ⇑α)) (htriv : ∀ (g : G) (a : kˣ), g • a = a)

/-- The linearization acts by the scalar recorded in the `kˣ`-component of the extension, followed
by the projective representation at its `G`-component. -/
@[simp]
theorem linearization_apply (x : α.Extension) (v : V) :
    hρ.linearization htriv x v = (x.left : k) • ρ x.right v :=
  (rfl)

/-- **The central copy of `kˣ` acts through the linearization by its own scalars.** This is the
condition that singles out the linearizations among all linear representations of `E_α`; see
`TauCeti.isProjectiveRepEquivExtensionHom`. -/
@[simp]
theorem linearization_inl (a : kˣ) :
    hρ.linearization htriv (FactorSet.inl α a) = LinearEquiv.smulOfUnit a :=
  LinearEquiv.ext fun v ↦ by
    simp [LinearEquiv.smulOfUnit_apply, hρ.map_one]

/-- **The projective representation is recovered from its linearization**, stated at the element
`⟨1, g⟩` that `TauCeti.FactorSet.canonicalSection_apply` rewrites the canonical section to, so that
`simp` also restricts the linearization along the canonical section. Unlike
`TauCeti.IsProjectiveRep.linearization_apply` it applies to the linearization itself rather than to
its value at a vector. -/
@[simp]
theorem linearization_mk_one (g : G) : hρ.linearization htriv ⟨1, g⟩ = ρ g :=
  LinearEquiv.ext fun v ↦ by simp

/-- **The linearization has the same invariant submodules as the projective representation.** The
`kˣ`-component of the extension acts by a scalar, which no submodule can escape, so invariance
under `E_α` is invariance under the automorphisms `ρ g` alone. This is what makes irreducibility of
a projective representation and of its linearization the same condition. -/
theorem forall_linearization_mem_iff {W : Submodule k V} :
    (∀ x : α.Extension, ∀ w ∈ W, hρ.linearization htriv x w ∈ W)
      ↔ ∀ g : G, ∀ w ∈ W, ρ g w ∈ W := by
  refine ⟨fun h g w hw ↦ ?_, fun h x w hw ↦ ?_⟩
  · simpa using h (α.canonicalSection g) w hw
  · rw [linearization_apply]
    exact W.smul_mem _ (h x.right w hw)

/-- The linearization, packaged as a `Representation` of the central extension `E_α` on `V`, so
that the machinery written against `Representation` applies to it. -/
def linearizationRepresentation : Representation k α.Extension V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (hρ.linearization htriv)

/-- The packaged representation acts by the same formula as the linearization it is built from. -/
@[simp]
theorem linearizationRepresentation_apply (x : α.Extension) (v : V) :
    hρ.linearizationRepresentation htriv x v = (x.left : k) • ρ x.right v :=
  (rfl)

/-- **The central copy of `kˣ` acts through the packaged representation by its own scalars**, the
condition of `TauCeti.isProjectiveRep_of_representation_canonicalSection` read on
`TauCeti.IsProjectiveRep.linearizationRepresentation`. -/
@[simp]
theorem linearizationRepresentation_inl (a : kˣ) :
    hρ.linearizationRepresentation htriv (FactorSet.inl α a) = (a : k) • LinearMap.id :=
  LinearMap.ext fun v ↦ by simp [hρ.map_one]

end IsProjectiveRep

/-- **Restricting a linear representation of `E_α` along the canonical section gives a projective
representation with factor set `α`**, as soon as the central copy of `kˣ` acts by its own scalars.
The canonical section fails to be a homomorphism by exactly `α`, and that failure becomes the
factor set. -/
theorem isProjectiveRep_comp_canonicalSection (htriv : ∀ (g : G) (a : kˣ), g • a = a)
    (π : α.Extension →* (V ≃ₗ[k] V))
    (hπ : ∀ a : kˣ, π (FactorSet.inl α a) = LinearEquiv.smulOfUnit a) :
    IsProjectiveRep (fun g ↦ π (α.canonicalSection g)) (Function.curry ⇑α) where
  isFactorSet := α.isFactorSet_curry htriv
  map_one := by simpa only [α.canonicalSection_one] using map_one π
  mul_apply g₁ g₂ v := by
    have key : π (α.canonicalSection g₁) * π (α.canonicalSection g₂)
        = LinearEquiv.smulOfUnit (α (g₁, g₂)) * π (α.canonicalSection (g₁ * g₂)) := by
      rw [← map_mul, α.canonicalSection_mul, map_mul, hπ]
    simpa only [LinearEquiv.mul_apply, LinearEquiv.smulOfUnit_apply, Function.curry]
      using DFunLike.congr_fun key v

/-- **The same converse for an ordinary `Representation k E_α V`**, the form in which the machinery
written against `Representation` supplies a linear representation of the extension: if the central
copy of `kˣ` acts by its own scalars, then a family `ρ` of linear automorphisms restricting `π`
along the canonical section is a projective representation with factor set `α`. The automorphisms
are taken as data because a `Representation` records only linear maps;
`TauCeti.IsProjectiveRep.linearizationRepresentation` together with
`TauCeti.IsProjectiveRep.linearizationRepresentation_inl` is the case that recovers `ρ` itself, and
`TauCeti.isProjectiveRep_restrictCanonicalSection` is the case of the canonical restriction
`TauCeti.FactorSet.restrictCanonicalSection`, which needs no automorphisms supplied. -/
theorem isProjectiveRep_of_representation_canonicalSection
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) (π : Representation k α.Extension V)
    (hπ : ∀ a : kˣ, π (FactorSet.inl α a) = (a : k) • LinearMap.id)
    (hρ : ∀ g : G, (ρ g : V →ₗ[k] V) = π (α.canonicalSection g)) :
    IsProjectiveRep ρ (Function.curry ⇑α) := by
  set π' := (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp π.asGroupHom
    with hπ'def
  have hπ'apply (x : α.Extension) (v : V) : π' x v = π x v := by
    simp [hπ'def, Representation.asGroupHom_apply]
  have hρ' : ρ = fun g ↦ π' (α.canonicalSection g) :=
    funext fun g ↦ LinearEquiv.ext fun v ↦ by
      rw [hπ'apply, ← LinearEquiv.coe_coe, hρ]
  rw [hρ']
  exact isProjectiveRep_comp_canonicalSection htriv π' fun a ↦
    LinearEquiv.ext fun v ↦ by
      rw [hπ'apply, hπ a, LinearEquiv.smulOfUnit_apply]
      simp

/-- **A linear representation of the extension `E_α`, restricted along the canonical section**, as
the family of linear automorphisms of `V` that a projective representation asks for: a
`Representation` records only linear maps, and `Representation.asGroupHom` together with
`LinearMap.GeneralLinearGroup.generalLinearEquiv` promotes its values back to automorphisms. When
the central copy of `kˣ` acts by its own scalars this family is a projective representation with
factor set `α`, by `TauCeti.isProjectiveRep_restrictCanonicalSection`. -/
def FactorSet.restrictCanonicalSection (α : FactorSet G kˣ) (π : Representation k α.Extension V)
    (g : G) : V ≃ₗ[k] V :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv k V (π.asGroupHom (α.canonicalSection g))

/-- The restriction along the canonical section acts as the representation does at `⟨1, g⟩`. -/
@[simp]
theorem FactorSet.restrictCanonicalSection_apply (α : FactorSet G kˣ)
    (π : Representation k α.Extension V) (g : G) (v : V) :
    α.restrictCanonicalSection π g v = π (α.canonicalSection g) v :=
  (rfl)

/-- **Restricting an ordinary `Representation k E_α V` along the canonical section gives a
projective representation with factor set `α`**, as soon as the central copy of `kˣ` acts by its own
scalars. This is `TauCeti.isProjectiveRep_of_representation_canonicalSection` for the canonical
choice of automorphisms, so that no conversion has to be supplied by the caller. -/
theorem isProjectiveRep_restrictCanonicalSection (htriv : ∀ (g : G) (a : kˣ), g • a = a)
    (π : Representation k α.Extension V)
    (hπ : ∀ a : kˣ, π (FactorSet.inl α a) = (a : k) • LinearMap.id) :
    IsProjectiveRep (α.restrictCanonicalSection π) (Function.curry ⇑α) :=
  isProjectiveRep_of_representation_canonicalSection htriv π hπ fun _ ↦ LinearMap.ext fun _ ↦ (rfl)

variable (k V)

/-- **Projective representations of `G` with factor set `α` are exactly the linear representations
of the central extension `E_α` under which the central copy of `kˣ` acts by its own scalars.** The
bijection sends a projective representation to its linearization, and a linear representation to
its restriction along the canonical section. -/
def isProjectiveRepEquivExtensionHom (α : FactorSet G kˣ)
    (htriv : ∀ (g : G) (a : kˣ), g • a = a) :
    {ρ : G → V ≃ₗ[k] V // IsProjectiveRep ρ (Function.curry ⇑α)} ≃
      {π : α.Extension →* (V ≃ₗ[k] V) //
        ∀ a : kˣ, π (FactorSet.inl α a) = LinearEquiv.smulOfUnit a} where
  toFun ρ := ⟨ρ.2.linearization htriv, fun a ↦ ρ.2.linearization_inl htriv a⟩
  invFun π := ⟨fun g ↦ π.1 (α.canonicalSection g),
    isProjectiveRep_comp_canonicalSection htriv π.1 π.2⟩
  left_inv ρ := Subtype.ext (funext fun g ↦ by simp)
  right_inv π := Subtype.ext (MonoidHom.ext fun x ↦ LinearEquiv.ext fun v ↦ by
    have h : π.1 (FactorSet.inl α x.left * α.canonicalSection x.right) v = π.1 x v := by
      rw [FactorSet.inl_mul_canonicalSection]
    rw [map_mul, π.2 x.left] at h
    simpa only [IsProjectiveRep.linearization_apply, LinearEquiv.mul_apply,
      LinearEquiv.smulOfUnit_apply] using h)

/-- The bijection sends a projective representation to its linearization. -/
@[simp]
theorem isProjectiveRepEquivExtensionHom_apply (α : FactorSet G kˣ)
    (htriv : ∀ (g : G) (a : kˣ), g • a = a)
    (ρ : {ρ : G → V ≃ₗ[k] V // IsProjectiveRep ρ (Function.curry ⇑α)}) :
    (isProjectiveRepEquivExtensionHom k V α htriv ρ : α.Extension →* (V ≃ₗ[k] V))
      = ρ.2.linearization htriv :=
  (rfl)

/-- The inverse bijection restricts a linear representation along the canonical section. -/
@[simp]
theorem isProjectiveRepEquivExtensionHom_symm_apply (α : FactorSet G kˣ)
    (htriv : ∀ (g : G) (a : kˣ), g • a = a)
    (π : {π : α.Extension →* (V ≃ₗ[k] V) //
      ∀ a : kˣ, π (FactorSet.inl α a) = LinearEquiv.smulOfUnit a}) :
    ((isProjectiveRepEquivExtensionHom k V α htriv).symm π : G → V ≃ₗ[k] V)
      = fun g ↦ π.1 (α.canonicalSection g) :=
  (rfl)

end Linearization

end GeneralAction

/-!
## Every projective representation linearizes

A projective representation carries no action of `G` on `kˣ`, so the statement below supplies the
trivial one, the action for which the extension of its factor set is central.
-/

section TrivialAction

attribute [local instance] trivialMulDistribMulAction

variable {ρ : G → V ≃ₗ[k] V}

/-- **Every projective representation of `G` linearizes over a central extension of `G` by `kˣ`.**
The extension is the one built from the factor set the projective representation carries, over the
trivial action `TauCeti.trivialMulDistribMulAction` of `G` on `kˣ`: its copy of `kˣ` is central, it
acts by its own scalars, and restricting along the canonical section returns the projective
representation. -/
theorem IsProjectiveRep.exists_factorSet_linearization {α : G → G → kˣ}
    (hρ : IsProjectiveRep ρ α) :
    ∃ β : FactorSet G kˣ, ∃ π : β.Extension →* (V ≃ₗ[k] V),
      (FactorSet.inl β).range ≤ Subgroup.center β.Extension ∧
        (∀ a : kˣ, π (FactorSet.inl β a) = LinearEquiv.smulOfUnit a) ∧
          ∀ g : G, π (β.canonicalSection g) = ρ g := by
  have hα : IsFactorSet α := hρ.isFactorSet
  have htriv (g : G) (a : kˣ) : g • a = a := trivialMulDistribMulAction_smul g a
  have hρ' : IsProjectiveRep ρ (Function.curry ⇑(IsFactorSet.toFactorSet α htriv)) := by
    rwa [IsFactorSet.curry_coe_toFactorSet]
  exact ⟨IsFactorSet.toFactorSet α htriv, hρ'.linearization htriv,
    FactorSet.inl_range_le_center _ htriv, fun a ↦ hρ'.linearization_inl htriv a,
    fun g ↦ by simp⟩

end TrivialAction

end TauCeti
