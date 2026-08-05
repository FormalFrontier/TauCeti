/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted

/-!
# Projective representations and their factor sets

A **projective representation** of a monoid `G` on a `k`-module `V` is a normalized lift
`ρ : G → (V ≃ₗ[k] V)` of a homomorphism into the projective linear group: it sends `1` to the
identity and is multiplicative up to a scalar,

`ρ g₁ (ρ g₂ x) = α g₁ g₂ • ρ (g₁ * g₂) x`

for a family of units `α : G → G → kˣ`, the **factor set** of `ρ`. Both the invertibility of each
`ρ g` and the normalization `ρ 1 = 1` are load-bearing: the constant zero family satisfies the
displayed relation for every `α`, so without them nothing below is true.

Working with a normalized lift rather than with a homomorphism `G → PGL(V)` keeps the theory
basis-free and puts the factor set in the statement, where the rest of the theory needs it.

The factor set is not extra data to be checked: on a nonzero module it is *determined* by `ρ`, and
`TauCeti.IsProjectiveRep.isFactorSet` derives its normalization and its multiplicative `2`-cocycle
identity from associativity of composition. The main results then identify projective
representations with factor set `α` with modules over the twisted monoid algebra `k_α[G]` of
`TauCeti.twistedMonoidAlgebra`: a module structure on `V` is an algebra map
`k_α[G] →ₐ[k] Module.End k V`, and `TauCeti.isProjectiveRepEquivAlgHom` is the bijection between
those and the projective representations with factor set `α`. Under it the twisted monoid algebra
itself becomes the **twisted regular representation**, which realizes every factor set.

## Main definitions

* `TauCeti.IsProjectiveRep ρ α`: `ρ` is a projective representation with factor set `α`.
* `TauCeti.IsProjectiveRep.toAlgHom`: the algebra map `k_α[G] →ₐ[k] Module.End k V` a projective
  representation with factor set `α` determines, that is, the `k_α[G]`-module structure on `V`.
* `TauCeti.projectiveRepOfAlgHom`: the projective representation attached to an algebra map out of
  `k_α[G]`, inverse to the previous construction.
* `TauCeti.isProjectiveRepEquivAlgHom`: the resulting bijection.
* `TauCeti.twistedRegularRep`: the twisted regular representation of `G` on `G →₀ k`.

## Main results

* `TauCeti.IsProjectiveRep.factorSet_eq`: on a nonzero module the factor set is determined by the
  lift, and `TauCeti.IsProjectiveRep.isFactorSet`: it is then a normalized factor set in the sense
  of `TauCeti.IsFactorSet`.
* `TauCeti.IsProjectiveRep.rescale`: rescaling the lift by `c : G → kˣ` multiplies the factor set by
  the coboundary of `c`, so the cohomology class of the factor set is the invariant of the lift.
* `TauCeti.IsProjectiveRep.toMonoidHom` and `TauCeti.IsProjectiveRep.of_monoidHom`: the projective
  representations with trivial factor set are exactly the linear representations.
* `TauCeti.exists_isProjectiveRep`: every normalized factor set is the factor set of a projective
  representation.

## References

This builds the projective-representation half of Layer 7 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/InductionRestriction/README.md),
whose `IsProjectiveRep` is the notion defined here. That roadmap spells the factor set uncurried
and bundles the cocycle identity into the definition; both are adjusted here, the currying to match
`TauCeti.IsFactorSet` and the twisted monoid algebra that consume it, and the cocycle identity
because it is a theorem rather than a hypothesis.

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1 and 3.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section Defs

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A **projective representation** of `G` on `V` with **factor set** `α`: a normalized lift
`ρ : G → (V ≃ₗ[k] V)` that is multiplicative up to the scalars `α`. Invertibility of the `ρ g` is
carried by the type `V ≃ₗ[k] V` and normalization by `map_one`; without them the zero family would
satisfy `mul_apply` for every `α`. -/
structure IsProjectiveRep (ρ : G → V ≃ₗ[k] V) (α : G → G → kˣ) : Prop where
  /-- The lift is normalized: the identity of `G` acts as the identity. -/
  map_one : ρ 1 = 1
  /-- The lift is multiplicative up to the factor set. -/
  mul_apply (g₁ g₂ : G) (x : V) : ρ g₁ (ρ g₂ x) = (α g₁ g₂ : k) • ρ (g₁ * g₂) x

variable {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- Rescaling an automorphism by a unit, unfolded. -/
private theorem trans_smulOfUnit_apply (e : V ≃ₗ[k] V) (u : kˣ) (x : V) :
    (e.trans (LinearEquiv.smulOfUnit u)) x = (u : k) • e x :=
  rfl

namespace IsProjectiveRep

/-- The defining relation, read in the endomorphism algebra: this is the form the universal
property of the twisted monoid algebra consumes. -/
theorem toLinearMap_mul (h : IsProjectiveRep ρ α) (g₁ g₂ : G) :
    (ρ g₁ : V →ₗ[k] V) * (ρ g₂ : V →ₗ[k] V) = (α g₁ g₂ : k) • (ρ (g₁ * g₂) : V →ₗ[k] V) :=
  LinearMap.ext fun x ↦ h.mul_apply g₁ g₂ x

/-- **Rescaling a projective representation.** Multiplying the lift by units `c : G → kˣ`, again
normalized, is again a projective representation, and multiplies the factor set by the coboundary
of `c`. So only the class of the factor set modulo coboundaries is an invariant of the underlying
homomorphism to the projective linear group. -/
theorem rescale (h : IsProjectiveRep ρ α) (c : G → kˣ) (hc : c 1 = 1) :
    IsProjectiveRep (fun g ↦ (ρ g).trans (LinearEquiv.smulOfUnit (c g)))
      fun g₁ g₂ ↦ c g₁ * c g₂ * (c (g₁ * g₂))⁻¹ * α g₁ g₂ where
  map_one := by
    refine LinearEquiv.ext fun x ↦ ?_
    rw [trans_smulOfUnit_apply, h.map_one, hc]
    simp
  mul_apply g₁ g₂ x := by
    have hunit : (c g₁ * c g₂ * (c (g₁ * g₂))⁻¹ * α g₁ g₂) * c (g₁ * g₂)
        = c g₁ * c g₂ * α g₁ g₂ := by
      rw [mul_right_comm, inv_mul_cancel_right]
    rw [trans_smulOfUnit_apply, trans_smulOfUnit_apply, trans_smulOfUnit_apply, map_smul,
      h.mul_apply, smul_smul, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, hunit]

/-- A linear representation, presented as a homomorphism into the group of linear automorphisms, is
a projective representation with trivial factor set. -/
theorem of_monoidHom (π : G →* (V ≃ₗ[k] V)) : IsProjectiveRep (⇑π) (1 : G → G → kˣ) where
  map_one := π.map_one
  mul_apply g₁ g₂ x := by rw [π.map_mul]; simp

/-- A projective representation with trivial factor set is a linear representation: the lift is
itself a homomorphism into the group of linear automorphisms. -/
@[expose] def toMonoidHom (h : IsProjectiveRep ρ (1 : G → G → kˣ)) : G →* (V ≃ₗ[k] V) where
  toFun := ρ
  map_one' := h.map_one
  map_mul' g₁ g₂ := LinearEquiv.ext fun x ↦ by simpa using (h.mul_apply g₁ g₂ x).symm

/-- The homomorphism attached to a projective representation with trivial factor set is the lift
itself. -/
@[simp]
theorem coe_toMonoidHom (h : IsProjectiveRep ρ (1 : G → G → kˣ)) : ⇑h.toMonoidHom = ρ :=
  rfl

end IsProjectiveRep

end Defs

/-!
## The factor set is a normalized `2`-cocycle

On a nonzero module the scalars in the defining relation are determined by the lift, and
associativity of composition forces the cocycle identity on them. Torsion-freeness of `V` over `k`
is what lets a scalar be read off from its action; over a field it is automatic.
-/

section IsFactorSet

variable [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [NoZeroSMulDivisors k V]
  [Nontrivial V] {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- On a nonzero torsion-free module a unit is determined by the scalar multiplication it induces.
-/
private theorem units_eq_of_forall_smul_eq {a b : kˣ} (h : ∀ x : V, (a : k) • x = (b : k) • x) :
    a = b := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  refine Units.ext ?_
  have hsub : ((a : k) - b) • x = 0 := by rw [sub_smul, h x, sub_self]
  rcases eq_zero_or_eq_zero_of_smul_eq_zero hsub with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hx

namespace IsProjectiveRep

/-- **The factor set is determined by the lift**: on a nonzero module a projective representation
has at most one factor set, so `α` is not extra data but an invariant of `ρ`. -/
theorem factorSet_eq {β : G → G → kˣ} (h : IsProjectiveRep ρ α) (h' : IsProjectiveRep ρ β) :
    α = β := by
  funext g₁ g₂
  refine units_eq_of_forall_smul_eq (V := V) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (ρ (g₁ * g₂)).surjective x
  exact (h.mul_apply g₁ g₂ y).symm.trans (h'.mul_apply g₁ g₂ y)

/-- The factor set is normalized on the left, because the lift is. -/
theorem one_left (h : IsProjectiveRep ρ α) (g : G) : α 1 g = 1 := by
  refine units_eq_of_forall_smul_eq (V := V) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (ρ g).surjective x
  have hy := h.mul_apply 1 g y
  rw [h.map_one, one_mul] at hy
  simpa using hy.symm

/-- The factor set is normalized on the right, because the lift is. -/
theorem one_right (h : IsProjectiveRep ρ α) (g : G) : α g 1 = 1 := by
  refine units_eq_of_forall_smul_eq (V := V) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (ρ g).surjective x
  have hy := h.mul_apply g 1 y
  rw [h.map_one, mul_one] at hy
  simpa using hy.symm

/-- **The cocycle identity.** Composing three lifts in the two possible orders gives the
multiplicative `2`-cocycle identity for the factor set. -/
theorem cocycle (h : IsProjectiveRep ρ α) (g₁ g₂ g₃ : G) :
    α (g₁ * g₂) g₃ * α g₁ g₂ = α g₂ g₃ * α g₁ (g₂ * g₃) := by
  refine units_eq_of_forall_smul_eq (V := V) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (ρ (g₁ * g₂ * g₃)).surjective x
  have outer : ρ g₁ (ρ g₂ (ρ g₃ y))
      = ((α g₁ g₂ : k) * α (g₁ * g₂) g₃) • ρ (g₁ * g₂ * g₃) y := by
    rw [h.mul_apply g₁ g₂, h.mul_apply (g₁ * g₂) g₃, smul_smul]
  have inner : ρ g₁ (ρ g₂ (ρ g₃ y))
      = ((α g₂ g₃ : k) * α g₁ (g₂ * g₃)) • ρ (g₁ * g₂ * g₃) y := by
    rw [h.mul_apply g₂ g₃, map_smul, h.mul_apply g₁ (g₂ * g₃), smul_smul, mul_assoc]
  rw [Units.val_mul, Units.val_mul, ← inner, outer, mul_comm]

/-- The factor set of a projective representation on a nonzero module is a normalized factor set,
so it has a twisted monoid algebra. -/
theorem isFactorSet (h : IsProjectiveRep ρ α) : IsFactorSet α where
  cocycle := h.cocycle
  one_left := h.one_left
  one_right := h.one_right

end IsProjectiveRep

end IsFactorSet

/-!
## Projective representations are twisted-group-algebra modules
-/

section AlgHom

variable [CommSemiring k] [AddCommMonoid V] [Module k V]

section Monoid

variable [Monoid G] {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ} [IsFactorSet α]

open TwistedMonoidAlgebra in
/-- **A projective representation with factor set `α` is a `k_α[G]`-module.** The algebra map is
the one the universal property of `TauCeti.twistedMonoidAlgebra` produces from the lift; a module
structure on `V` over an algebra is exactly such an algebra map to `Module.End k V`. -/
noncomputable def IsProjectiveRep.toAlgHom (h : IsProjectiveRep ρ α) :
    twistedMonoidAlgebra k G α →ₐ[k] Module.End k V :=
  lift (fun g ↦ (ρ g : V →ₗ[k] V)) (by rw [h.map_one]; rfl) h.toLinearMap_mul

/-- The `k_α[G]`-module structure attached to a projective representation acts on the basis
element at `g` by the lift at `g`. -/
@[simp]
theorem IsProjectiveRep.toAlgHom_of (h : IsProjectiveRep ρ α) (g : G) :
    h.toAlgHom (TwistedMonoidAlgebra.of g) = (ρ g : V →ₗ[k] V) :=
  TwistedMonoidAlgebra.lift_of ..

end Monoid

section Group

variable [Group G] {α : G → G → kˣ} [IsFactorSet α]
  (φ : twistedMonoidAlgebra k G α →ₐ[k] Module.End k V)

/-- **A `k_α[G]`-module is a projective representation with factor set `α`.** The basis element at
`g` is a unit of `k_α[G]`, so it acts on `V` as a linear automorphism. -/
@[expose] noncomputable def projectiveRepOfAlgHom (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofBijective (φ (TwistedMonoidAlgebra.of g))
    ((Module.End.isUnit_iff _).1 ((TwistedMonoidAlgebra.isUnit_of g).map φ))

/-- The projective representation attached to a `k_α[G]`-module acts at `g` by the basis element
at `g`. -/
@[simp]
theorem projectiveRepOfAlgHom_apply (g : G) (x : V) :
    projectiveRepOfAlgHom φ g x = φ (TwistedMonoidAlgebra.of g) x :=
  rfl

/-- The action of the basis elements of `k_α[G]` on a module is a projective representation with
factor set `α`. -/
theorem isProjectiveRep_projectiveRepOfAlgHom :
    IsProjectiveRep (projectiveRepOfAlgHom φ) α where
  map_one := LinearEquiv.ext fun x ↦ by simp
  mul_apply g₁ g₂ x := by
    have : φ (TwistedMonoidAlgebra.of g₁) (φ (TwistedMonoidAlgebra.of g₂) x)
        = φ (TwistedMonoidAlgebra.of g₁ * TwistedMonoidAlgebra.of g₂) x := by
      rw [map_mul]; rfl
    rw [projectiveRepOfAlgHom_apply, projectiveRepOfAlgHom_apply, this,
      TwistedMonoidAlgebra.of_mul_of, map_smul]
    rfl

variable {φ}

/-- Reading a `k_α[G]`-module as a projective representation and back returns the module. -/
@[simp]
theorem toAlgHom_projectiveRepOfAlgHom :
    (isProjectiveRep_projectiveRepOfAlgHom φ).toAlgHom = φ :=
  TwistedMonoidAlgebra.algHom_ext fun g ↦ by
    rw [IsProjectiveRep.toAlgHom_of]
    rfl

/-- Reading a projective representation as a `k_α[G]`-module and back returns the lift. -/
@[simp]
theorem projectiveRepOfAlgHom_toAlgHom {ρ : G → V ≃ₗ[k] V} (h : IsProjectiveRep ρ α) :
    projectiveRepOfAlgHom h.toAlgHom = ρ :=
  funext fun g ↦ LinearEquiv.ext fun x ↦ by
    rw [projectiveRepOfAlgHom_apply, IsProjectiveRep.toAlgHom_of]
    rfl

variable (k V α)

/-- **Projective representations with factor set `α` are exactly the `k_α[G]`-modules.** -/
noncomputable def isProjectiveRepEquivAlgHom :
    {ρ : G → V ≃ₗ[k] V // IsProjectiveRep ρ α} ≃
      (twistedMonoidAlgebra k G α →ₐ[k] Module.End k V) where
  toFun ρ := ρ.2.toAlgHom
  invFun φ := ⟨projectiveRepOfAlgHom φ, isProjectiveRep_projectiveRepOfAlgHom φ⟩
  left_inv ρ := Subtype.ext (projectiveRepOfAlgHom_toAlgHom ρ.2)
  right_inv _ := toAlgHom_projectiveRepOfAlgHom

end Group

end AlgHom

/-!
## The twisted regular representation
-/

section Regular

variable (k G : Type*) [CommSemiring k] [Group G] (α : G → G → kˣ) [IsFactorSet α]

/-- **The twisted regular representation** of `G` on `G →₀ k`: the twisted monoid algebra `k_α[G]`
acting on itself, read through its realization as operators on `G →₀ k`. Its factor set is `α`, so
every normalized factor set is realized by a projective representation. -/
@[expose] noncomputable def twistedRegularRep (g : G) : (G →₀ k) ≃ₗ[k] (G →₀ k) :=
  projectiveRepOfAlgHom (twistedMonoidAlgebra k G α).val g

/-- The twisted regular representation acts by the twisted translations. -/
@[simp]
theorem twistedRegularRep_apply (g : G) (x : G →₀ k) :
    twistedRegularRep k G α g x = twistedTranslation k α g x :=
  rfl

/-- The twisted regular representation has factor set `α`. -/
theorem isProjectiveRep_twistedRegularRep : IsProjectiveRep (twistedRegularRep k G α) α :=
  isProjectiveRep_projectiveRepOfAlgHom _

/-- **Every normalized factor set arises from a projective representation.** Together with
`TauCeti.IsProjectiveRep.isFactorSet` this characterizes the factor sets: over a nonzero module
they are the normalized multiplicative `2`-cocycles, and no others. -/
theorem exists_isProjectiveRep :
    ∃ ρ : G → (G →₀ k) ≃ₗ[k] (G →₀ k), IsProjectiveRep ρ α :=
  ⟨_, isProjectiveRep_twistedRegularRep k G α⟩

end Regular

end TauCeti
