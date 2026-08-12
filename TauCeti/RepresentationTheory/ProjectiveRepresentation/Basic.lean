/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted

/-!
# Projective representations and their factor sets

A **projective representation** of a monoid `G` on a `k`-module `V` is a normalized lift
`ρ : G → (V ≃ₗ[k] V)` of a homomorphism into the projective linear group: it sends `1` to the
identity and is multiplicative up to a scalar,

`ρ g₁ (ρ g₂ x) = α g₁ g₂ • ρ (g₁ * g₂) x`

for a normalized factor set `α : G → G → kˣ`, the **factor set** of `ρ`. Both the invertibility of
each `ρ g` and the normalization `ρ 1 = 1` are load-bearing: the constant zero family satisfies the
displayed relation for every `α`, so without them nothing below is true.

Working with a normalized lift rather than with a homomorphism `G → PGL(V)` keeps the theory
basis-free and puts the factor set in the statement, where the rest of the theory needs it.

That `α` is a factor set is rarely something to check by hand: as soon as `kˣ` acts faithfully on
`V` it is *determined* by `ρ`, and `TauCeti.IsProjectiveRep.of_map_one_mul_apply` derives its
normalization and its multiplicative `2`-cocycle identity from associativity of composition, so
there only the two conditions on `ρ` remain. The main results then identify projective
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

* `TauCeti.IsProjectiveRep.of_map_one_mul_apply`: when `kˣ` acts faithfully on `V` the factor-set
  axioms are automatic, and `TauCeti.IsProjectiveRep.factorSet_eq`: there the factor set is
  determined by the lift.
* `TauCeti.IsProjectiveRep.rescale`: rescaling the lift by `c : G → kˣ` multiplies the factor set by
  the coboundary of `c`. A fixed lift determines its factor set outright; it is the cohomology
  class that is unchanged by normalized rescaling, hence an invariant of the underlying projective
  action rather than of the lift.
* `TauCeti.IsProjectiveRep.toMonoidHom` and `TauCeti.IsProjectiveRep.of_monoidHom`: the projective
  representations with trivial factor set are exactly the linear representations.
* `TauCeti.exists_isProjectiveRep`: every normalized factor set is the factor set of a projective
  representation.

## References

This builds the projective-representation half of Layer 7 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/InductionRestriction/README.md),
whose `IsProjectiveRep` is the notion defined here. That roadmap spells the factor set uncurried;
it is curried here to match `TauCeti.IsFactorSet` and the twisted monoid algebra that consume it.

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1 and 3.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section Defs

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A **projective representation** of `G` on `V` with **factor set** `α`: a normalized factor set
`α`, in the sense of `TauCeti.IsFactorSet`, together with a normalized lift `ρ : G → (V ≃ₗ[k] V)`
that is multiplicative up to the scalars `α`. Invertibility of the `ρ g` is carried by the type
`V ≃ₗ[k] V` and normalization by `map_one`; without them the zero family would satisfy `mul_apply`
for every `α`, and on the zero module it still does, which is why the factor-set axioms are
recorded here rather than left to be derived. When `kˣ` acts faithfully on `V` they *are*
derivable, and `TauCeti.IsProjectiveRep.of_map_one_mul_apply` derives them. -/
structure IsProjectiveRep (ρ : G → V ≃ₗ[k] V) (α : G → G → kˣ) : Prop where
  /-- The scalars are a normalized multiplicative `2`-cocycle. -/
  isFactorSet : IsFactorSet α
  /-- The lift is normalized: the identity of `G` acts as the identity. -/
  map_one : ρ 1 = 1
  /-- The lift is multiplicative up to the factor set. -/
  mul_apply (g₁ g₂ : G) (x : V) : ρ g₁ (ρ g₂ x) = (α g₁ g₂ : k) • ρ (g₁ * g₂) x

variable {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- The rearrangement in a commutative group that turns the cocycle identity for a factor set into
the cocycle identity for its rescaling by a coboundary: read `a, b, d` as the values of the
rescaling at `g₁, g₂, g₃`, then `p, q, r` as its values at `g₁ * g₂`, `g₂ * g₃`, `g₁ * g₂ * g₃`, and
`A, B, C, D` as the four values of the factor set entering the cocycle identity. -/
private theorem rescale_cocycle_aux {M : Type*} [CommGroup M] {a b d p q r A B C D : M}
    (h : A * B = C * D) :
    p * d * r⁻¹ * A * (a * b * p⁻¹ * B) = b * d * q⁻¹ * C * (a * q * r⁻¹ * D) := by
  have e₁ : p * d * r⁻¹ * A * (a * b * p⁻¹ * B) = p * p⁻¹ * (a * b * d * r⁻¹ * (A * B)) := by
    simp only [mul_comm, mul_left_comm, mul_assoc]
  have e₂ : b * d * q⁻¹ * C * (a * q * r⁻¹ * D) = q * q⁻¹ * (a * b * d * r⁻¹ * (C * D)) := by
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [e₁, e₂, h]
  simp

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
  isFactorSet :=
    { cocycle g₁ g₂ g₃ := by
        rw [← mul_assoc g₁ g₂ g₃]
        exact rescale_cocycle_aux (h.isFactorSet.cocycle g₁ g₂ g₃)
      one_left g := by simp [hc, h.isFactorSet.one_left]
      one_right g := by simp [hc, h.isFactorSet.one_right] }
  map_one := by
    refine LinearEquiv.ext fun x ↦ ?_
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfUnit_apply, h.map_one, hc]
    simp
  mul_apply g₁ g₂ x := by
    have hunit : (c g₁ * c g₂ * (c (g₁ * g₂))⁻¹ * α g₁ g₂) * c (g₁ * g₂)
        = c g₂ * (α g₁ g₂ * c g₁) := by
      rw [mul_right_comm, inv_mul_cancel_right]
      simp only [mul_comm, mul_left_comm]
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfUnit_apply, map_smul, h.mul_apply,
      smul_smul, ← Units.val_mul, hunit]

/-- A linear representation, presented as a homomorphism into the group of linear automorphisms, is
a projective representation with trivial factor set. -/
theorem of_monoidHom (π : G →* (V ≃ₗ[k] V)) : IsProjectiveRep (⇑π) (1 : G → G → kˣ) where
  isFactorSet := inferInstance
  map_one := π.map_one
  mul_apply g₁ g₂ x := by rw [π.map_mul]; simp

/-- A projective representation with trivial factor set is a linear representation: the lift is
itself a homomorphism into the group of linear automorphisms. -/
def toMonoidHom (h : IsProjectiveRep ρ (1 : G → G → kˣ)) : G →* (V ≃ₗ[k] V) where
  toFun := ρ
  map_one' := h.map_one
  map_mul' g₁ g₂ := LinearEquiv.ext fun x ↦ by simpa using (h.mul_apply g₁ g₂ x).symm

/-- The homomorphism attached to a projective representation with trivial factor set is the lift
itself. -/
@[simp]
theorem coe_toMonoidHom (h : IsProjectiveRep ρ (1 : G → G → kˣ)) : ⇑h.toMonoidHom = ρ :=
  (rfl)

end IsProjectiveRep

end Defs

/-!
## For a faithful action of the units the factor-set axioms are automatic

When `kˣ` acts faithfully on `V` the scalars in the defining relation are determined by the lift,
and associativity of composition forces the cocycle identity on them. So there a normalized lift
that is multiplicative up to `α` is already a projective representation, and its factor set is
unique. Faithfulness is exactly what lets a scalar be read off from its action, and only the
scalars in `kˣ` are ever compared, so `[FaithfulSMul kˣ V]` is what is asked for; `k` acting
faithfully — as it does on a nonzero torsion-free module, a nonzero vector space in particular —
supplies it.
-/

section Faithful

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [FaithfulSMul kˣ V]
  {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

namespace IsProjectiveRep

/-- **For a faithful scalar action the factor-set axioms come for free.** A normalized lift that is
multiplicative up to `α` is a projective representation: the normalization of `α` follows from that
of the lift, and its multiplicative `2`-cocycle identity from associativity of composition. So on a
nonzero vector space, say, the cocycle identity never has to be checked. -/
theorem of_map_one_mul_apply (h₁ : ρ 1 = 1)
    (h₂ : ∀ (g₁ g₂ : G) (x : V), ρ g₁ (ρ g₂ x) = (α g₁ g₂ : k) • ρ (g₁ * g₂) x) :
    IsProjectiveRep ρ α where
  isFactorSet :=
    { cocycle g₁ g₂ g₃ := by
        refine FaithfulSMul.eq_of_smul_eq_smul fun x : V ↦ ?_
        obtain ⟨y, rfl⟩ := (ρ (g₁ * g₂ * g₃)).surjective x
        have outer : ρ g₁ (ρ g₂ (ρ g₃ y))
            = ((α g₁ g₂ : k) * α (g₁ * g₂) g₃) • ρ (g₁ * g₂ * g₃) y := by
          rw [h₂ g₁ g₂, h₂ (g₁ * g₂) g₃, smul_smul]
        have inner : ρ g₁ (ρ g₂ (ρ g₃ y))
            = ((α g₂ g₃ : k) * α g₁ (g₂ * g₃)) • ρ (g₁ * g₂ * g₃) y := by
          rw [h₂ g₂ g₃, map_smul, h₂ g₁ (g₂ * g₃), smul_smul, mul_assoc]
        rw [Units.smul_def, Units.smul_def, Units.val_mul, Units.val_mul, ← inner, outer, mul_comm]
      one_left g := by
        refine FaithfulSMul.eq_of_smul_eq_smul fun x : V ↦ ?_
        obtain ⟨y, rfl⟩ := (ρ g).surjective x
        have hy := h₂ 1 g y
        rw [h₁, one_mul] at hy
        simpa [Units.smul_def] using hy.symm
      one_right g := by
        refine FaithfulSMul.eq_of_smul_eq_smul fun x : V ↦ ?_
        obtain ⟨y, rfl⟩ := (ρ g).surjective x
        have hy := h₂ g 1 y
        rw [h₁, mul_one] at hy
        simpa [Units.smul_def] using hy.symm }
  map_one := h₁
  mul_apply := h₂

/-- **The factor set is determined by the lift**: for a faithful action of the units a projective
representation has at most one factor set, so `α` is not extra data but an invariant of `ρ`. -/
theorem factorSet_eq {β : G → G → kˣ} (h : IsProjectiveRep ρ α) (h' : IsProjectiveRep ρ β) :
    α = β := by
  funext g₁ g₂
  refine FaithfulSMul.eq_of_smul_eq_smul fun x : V ↦ ?_
  obtain ⟨y, rfl⟩ := (ρ (g₁ * g₂)).surjective x
  simp only [Units.smul_def]
  exact (h.mul_apply g₁ g₂ y).symm.trans (h'.mul_apply g₁ g₂ y)

end IsProjectiveRep

end Faithful

/-!
## Projective representations are twisted-group-algebra modules
-/

section AlgHom

variable [CommSemiring k] [AddCommMonoid V] [Module k V]

section Monoid

variable [Monoid G] {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

open TwistedMonoidAlgebra in
/-- **A projective representation with factor set `α` is a `k_α[G]`-module.** The algebra map is
the one the universal property of `TauCeti.twistedMonoidAlgebra` produces from the lift; a module
structure on `V` over an algebra is exactly such an algebra map to `Module.End k V`.

Writing the domain down needs the factor-set axioms, since `TauCeti.twistedMonoidAlgebra` takes
them as an instance argument; they are supplied by `h` itself, so no separate `IsFactorSet α`
instance need be in scope. -/
noncomputable def IsProjectiveRep.toAlgHom (h : IsProjectiveRep ρ α) :
    letI := h.isFactorSet
    twistedMonoidAlgebra k G α →ₐ[k] Module.End k V :=
  letI := h.isFactorSet
  lift (fun g ↦ (ρ g : V →ₗ[k] V)) (by rw [h.map_one]; rfl) h.toLinearMap_mul

/-- The `k_α[G]`-module structure attached to a projective representation acts on the basis
element at `g` by the lift at `g`. -/
@[simp]
theorem IsProjectiveRep.toAlgHom_of (h : IsProjectiveRep ρ α) (g : G) :
    letI := h.isFactorSet
    h.toAlgHom (TwistedMonoidAlgebra.of g) = (ρ g : V →ₗ[k] V) :=
  letI := h.isFactorSet
  TwistedMonoidAlgebra.lift_of ..

end Monoid

section Group

variable [Group G] {α : G → G → kˣ} [IsFactorSet α]
  (φ : twistedMonoidAlgebra k G α →ₐ[k] Module.End k V)

/-- **A `k_α[G]`-module is a projective representation with factor set `α`.** The basis element at
`g` is a unit of `k_α[G]`, so it acts on `V` as a linear automorphism. -/
noncomputable def projectiveRepOfAlgHom (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofBijective (φ (TwistedMonoidAlgebra.of g))
    ((Module.End.isUnit_iff _).1 ((TwistedMonoidAlgebra.isUnit_of g).map φ))

/-- The projective representation attached to a `k_α[G]`-module acts at `g` by the basis element
at `g`. -/
@[simp]
theorem projectiveRepOfAlgHom_apply (g : G) (x : V) :
    projectiveRepOfAlgHom φ g x = φ (TwistedMonoidAlgebra.of g) x :=
  (rfl)

/-- The action of the basis elements of `k_α[G]` on a module is a projective representation with
factor set `α`. -/
theorem isProjectiveRep_projectiveRepOfAlgHom :
    IsProjectiveRep (projectiveRepOfAlgHom φ) α where
  isFactorSet := inferInstance
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
    exact LinearMap.ext (projectiveRepOfAlgHom_apply φ g)

omit [IsFactorSet α] in
/-- Reading a projective representation as a `k_α[G]`-module and back returns the lift. -/
@[simp]
theorem projectiveRepOfAlgHom_toAlgHom {ρ : G → V ≃ₗ[k] V} (h : IsProjectiveRep ρ α) :
    projectiveRepOfAlgHom h.toAlgHom = ρ :=
  haveI := h.isFactorSet
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

/-- The bijection sends a projective representation to the `k_α[G]`-module structure it
determines. -/
@[simp]
theorem isProjectiveRepEquivAlgHom_apply (ρ : {ρ : G → V ≃ₗ[k] V // IsProjectiveRep ρ α}) :
    isProjectiveRepEquivAlgHom k V α ρ = ρ.2.toAlgHom :=
  (rfl)

/-- The inverse bijection sends a `k_α[G]`-module structure to the action of the basis elements. -/
@[simp]
theorem isProjectiveRepEquivAlgHom_symm_apply
    (ψ : twistedMonoidAlgebra k G α →ₐ[k] Module.End k V) :
    ((isProjectiveRepEquivAlgHom k V α).symm ψ : G → V ≃ₗ[k] V) = projectiveRepOfAlgHom ψ :=
  (rfl)

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
noncomputable def twistedRegularRep (g : G) : (G →₀ k) ≃ₗ[k] (G →₀ k) :=
  projectiveRepOfAlgHom (twistedMonoidAlgebra k G α).val g

/-- The twisted regular representation acts by the twisted translations. -/
@[simp]
theorem twistedRegularRep_apply (g : G) (x : G →₀ k) :
    twistedRegularRep k G α g x = twistedTranslation k α g x := by
  rw [twistedRegularRep, projectiveRepOfAlgHom_apply, Subalgebra.coe_val,
    TwistedMonoidAlgebra.coe_of]

/-- The twisted regular representation has factor set `α`. -/
theorem isProjectiveRep_twistedRegularRep : IsProjectiveRep (twistedRegularRep k G α) α :=
  isProjectiveRep_projectiveRepOfAlgHom _

/-- **Every normalized factor set arises from a projective representation.** Together with
`TauCeti.IsProjectiveRep.isFactorSet` this characterizes the factor sets of projective
representations of a group: they are exactly the normalized multiplicative `2`-cocycles. -/
theorem exists_isProjectiveRep :
    ∃ ρ : G → (G →₀ k) ≃ₗ[k] (G →₀ k), IsProjectiveRep ρ α :=
  ⟨_, isProjectiveRep_twistedRegularRep k G α⟩

end Regular

end TauCeti
