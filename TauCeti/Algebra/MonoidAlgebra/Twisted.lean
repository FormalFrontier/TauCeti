/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# The twisted group algebra of a factor set

A **factor set** on a monoid `G` with values in the units of a commutative semiring `k` is a
normalized multiplicative `2`-cocycle `α : G → G → kˣ`. The **twisted group algebra** `k_α[G]` is
the `k`-algebra with a basis `e g` indexed by `G` and multiplication
`e g * e h = α g h • e (g * h)`; for the trivial factor set it is the ordinary group algebra
`MonoidAlgebra k G`. It is the module-theoretic home of projective representation theory: a
projective representation of `G` with factor set `α` is exactly a `k_α[G]`-module.

This file constructs the algebra as the image of the **twisted regular representation**. The
operator `TauCeti.twistedTranslation k α g` on `G →₀ k` sends the basis vector at `h` to `α g h`
times the basis vector at `g * h`, and the cocycle identity says exactly that
`twistedTranslation k α g * twistedTranslation k α h = α g h • twistedTranslation k α (g * h)`.
So the `k`-span of these operators is a subalgebra of `Module.End k (G →₀ k)`, and that subalgebra
is `TauCeti.twistedGroupAlgebra k G α`. Associativity and unitality of the twisted product are
inherited from composition of linear maps rather than re-proved by hand, and the operators are
linearly independent -- each is recovered from its value at the basis vector of `1` -- so they form
a basis and the multiplication table above holds on the nose.

## Main definitions and results

* `TauCeti.IsFactorSet`: a normalized factor set, that is, a normalized multiplicative `2`-cocycle
  `α : G → G → kˣ`;
* `TauCeti.twistedGroupAlgebra k G α`: the twisted group algebra `k_α[G]`;
* `TauCeti.TwistedGroupAlgebra.of`: its basis elements, with the multiplication table
  `TauCeti.TwistedGroupAlgebra.of_mul_of`, the basis `TauCeti.TwistedGroupAlgebra.basis`, and the
  dimension count `TauCeti.TwistedGroupAlgebra.finrank_eq_natCard`;
* `TauCeti.TwistedGroupAlgebra.lift`: the universal property. A family `u : G → A` in a
  `k`-algebra `A` with `u 1 = 1` and `u g * u h = α g h • u (g * h)` -- that is, a projective
  representation with factor set `α` -- extends uniquely to an algebra map `k_α[G] →ₐ[k] A`;
* `TauCeti.TwistedGroupAlgebra.monoidAlgebraEquiv`: for the trivial factor set, `k_α[G]` is the
  group algebra `MonoidAlgebra k G`;
* `TauCeti.TwistedGroupAlgebra.equivOfCoboundary`: cohomologous factor sets have isomorphic twisted
  group algebras, so `k_α[G]` depends up to isomorphism only on the class of `α` in `H²(G, kˣ)`.

## Implementation notes

`IsFactorSet` is a `Prop`-valued class on the raw function `α`, spelled out as the multiplicative
`2`-cocycle identity `α (g * h) j * α g h = α h j * α g (h * j)` together with the normalization
`α 1 g = α g 1 = 1`, rather than as `groupCohomology.IsMulCocycle₂` for the trivial action of `G`
on `kˣ`: the twisted algebra wants `α` curried, and wants the normalization, which the cocycle
identity alone gives only up to the constant `α 1 1`. Carrying the hypotheses in a class keeps the
type `twistedGroupAlgebra k G α` free of proof arguments.

Nothing in the construction uses inverses in `G`, so `IsFactorSet`, the twisted algebra, its basis,
the universal property and the two comparison isomorphisms are all stated for a monoid `G`. A group
is assumed only where an inverse appears, in `TauCeti.IsFactorSet.apply_inv_eq_inv_apply` and
`TauCeti.TwistedGroupAlgebra.isUnit_of`.

`twistedGroupAlgebra k G α` is a `Subalgebra k (Module.End k (G →₀ k))` rather than a fresh type
carrying a hand-built ring structure on `G →₀ k`. The two are the same algebra:
`TauCeti.TwistedGroupAlgebra.basis` exhibits `G` as a basis and
`TauCeti.TwistedGroupAlgebra.of_mul_of` is the intended multiplication table, while
`TauCeti.TwistedGroupAlgebra.lift` and `TauCeti.TwistedGroupAlgebra.algHom_ext` say it has the
expected universal property.

## References

This implements the twisted group algebra of Layer 7 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/InductionRestriction/README.md),
whose `twistedMul` is the multiplication realized here.

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti

open Module

/-- A **normalized factor set** on a monoid `G` with values in the units of a commutative semiring
`k`: a function `α : G → G → kˣ` satisfying the multiplicative `2`-cocycle identity and normalized
at `1`. For a group `G` these are exactly the factor sets arising from projective representations
of `G` over `k`. -/
class IsFactorSet {k G : Type*} [CommSemiring k] [Monoid G] (α : G → G → kˣ) : Prop where
  /-- The multiplicative `2`-cocycle identity, the associativity constraint of the twisted
  product. -/
  cocycle (g h j : G) : α (g * h) j * α g h = α h j * α g (h * j)
  /-- Normalization on the left, half of the unitality of the twisted product. -/
  one_left (g : G) : α 1 g = 1
  /-- Normalization on the right, half of the unitality of the twisted product. -/
  one_right (g : G) : α g 1 = 1

namespace IsFactorSet

section Monoid

variable {k G : Type*} [CommSemiring k] [Monoid G]

/-- The trivial factor set, whose twisted group algebra is the ordinary group algebra. -/
instance : IsFactorSet (1 : G → G → kˣ) where
  cocycle _ _ _ := by simp
  one_left _ := rfl
  one_right _ := rfl

end Monoid

section Group

variable {k G : Type*} [CommSemiring k] [Group G] (α : G → G → kˣ) [IsFactorSet α]

/-- A factor set is symmetric on an inverse pair: it takes the same value at `(g, g⁻¹)` as at
`(g⁻¹, g)`. This is the cocycle identity at `(g, g⁻¹, g)`, and it is the coherence making the
twisted basis elements two-sided units. -/
theorem apply_inv_eq_inv_apply (g : G) : α g g⁻¹ = α g⁻¹ g := by
  simpa [one_left (α := α), one_right (α := α)] using cocycle (α := α) g g⁻¹ g

end Group

end IsFactorSet

section Translation

variable (k : Type*) {G : Type*} [CommSemiring k] [Monoid G] (α : G → G → kˣ)

/-- The `α`-twisted translation by `g` on `G →₀ k`: it sends the basis vector at `h` to `α g h`
times the basis vector at `g * h`. For the trivial factor set this is the regular representation
of `G` on its group algebra. -/
noncomputable def twistedTranslation (g : G) : (G →₀ k) →ₗ[k] (G →₀ k) :=
  Finsupp.lsum k fun h ↦ (α g h : k) • Finsupp.lsingle (g * h)

@[simp]
theorem twistedTranslation_single (g h : G) (b : k) :
    twistedTranslation k α g (Finsupp.single h b) = Finsupp.single (g * h) ((α g h : k) * b) := by
  simp [twistedTranslation, Finsupp.lsum_single, Finsupp.smul_single]

variable [IsFactorSet α]

@[simp]
theorem twistedTranslation_one : twistedTranslation k α 1 = 1 := by
  refine Finsupp.lhom_ext fun a b ↦ ?_
  simp [IsFactorSet.one_left]

/-- **The twisted composition law.** The composite of two twisted translations is the twisted
translation of the product, scaled by the factor set; this is the cocycle identity, restated. -/
theorem twistedTranslation_mul (g h : G) :
    twistedTranslation k α g * twistedTranslation k α h
      = (α g h : k) • twistedTranslation k α (g * h) := by
  refine Finsupp.lhom_ext fun a b ↦ ?_
  have hcoef : α g (h * a) * α h a = α g h * α (g * h) a := by
    rw [mul_comm (α g (h * a)), ← IsFactorSet.cocycle (α := α) g h a, mul_comm]
  simp only [Module.End.mul_apply, twistedTranslation_single, LinearMap.smul_apply,
    Finsupp.smul_single, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, hcoef]

/-- The twisted translations are linearly independent: the translation by `g` is recovered from its
value at the basis vector of `1`, which is the basis vector of `g`. -/
theorem linearIndependent_twistedTranslation :
    LinearIndependent k (twistedTranslation k α) := by
  refine LinearIndependent.of_comp (LinearMap.applyₗ (Finsupp.single (1 : G) (1 : k))) ?_
  have h : (LinearMap.applyₗ (R := k) (Finsupp.single (1 : G) (1 : k))) ∘
      twistedTranslation k α = fun g : G ↦ Finsupp.single g (1 : k) := by
    funext g
    simp [IsFactorSet.one_right]
  rw [h]
  simpa using (Finsupp.basisSingleOne (ι := G) (R := k)).linearIndependent

end Translation

section Algebra

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- **The twisted group algebra** `k_α[G]` of a factor set `α`, realized as the `k`-span of the
twisted translations inside `Module.End k (G →₀ k)`. It is a subalgebra because the cocycle
identity makes the span closed under composition (`TauCeti.twistedTranslation_mul`) and the
normalization puts the identity operator into it (`TauCeti.twistedTranslation_one`). -/
noncomputable def twistedGroupAlgebra : Subalgebra k (Module.End k (G →₀ k)) :=
  Submodule.toSubalgebra (Submodule.span k (Set.range (twistedTranslation k α)))
    (by
      rw [← twistedTranslation_one k α]
      exact Submodule.subset_span ⟨1, rfl⟩)
    (by
      have hle : Submodule.span k (Set.range (twistedTranslation k α)) *
          Submodule.span k (Set.range (twistedTranslation k α)) ≤
          Submodule.span k (Set.range (twistedTranslation k α)) := by
        rw [Submodule.span_mul_span]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
        refine SetLike.mem_coe.2 ?_
        simp only [twistedTranslation_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g * h, rfl⟩)
      exact fun x y hx hy ↦ hle (Submodule.mul_mem_mul hx hy))

@[simp]
theorem toSubmodule_twistedGroupAlgebra :
    Subalgebra.toSubmodule (twistedGroupAlgebra k G α) =
      Submodule.span k (Set.range (twistedTranslation k α)) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- The twisted translations lie in the twisted group algebra: they are its basis elements. -/
theorem twistedTranslation_mem_twistedGroupAlgebra (g : G) :
    twistedTranslation k α g ∈ twistedGroupAlgebra k G α := by
  rw [← Subalgebra.mem_toSubmodule, toSubmodule_twistedGroupAlgebra]
  exact Submodule.subset_span ⟨g, rfl⟩

namespace TwistedGroupAlgebra

variable {k G α}

/-- The basis element of `k_α[G]` at `g : G`, namely the `α`-twisted translation by `g`. -/
@[expose] noncomputable def of (g : G) : twistedGroupAlgebra k G α :=
  ⟨twistedTranslation k α g, twistedTranslation_mem_twistedGroupAlgebra k G α g⟩

@[simp]
theorem coe_of (g : G) :
    ((of g : twistedGroupAlgebra k G α) : Module.End k (G →₀ k)) = twistedTranslation k α g :=
  rfl

@[simp]
theorem of_one : (of 1 : twistedGroupAlgebra k G α) = 1 :=
  Subtype.ext <| by simp

/-- **The multiplication table of the twisted group algebra**: `e g * e h = α g h • e (g * h)`. -/
@[simp]
theorem of_mul_of (g h : G) :
    (of g : twistedGroupAlgebra k G α) * of h = (α g h : k) • of (g * h) :=
  Subtype.ext <| by simpa using twistedTranslation_mul k α g h

section Group

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- The basis elements are units, with `(α g g⁻¹)⁻¹ • e g⁻¹` as a two-sided inverse. -/
theorem isUnit_of (g : G) : IsUnit (of g : twistedGroupAlgebra k G α) := by
  refine ⟨⟨of g, (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹, ?_, ?_⟩, rfl⟩
  · simp [smul_smul, ← Units.val_mul]
  · simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]

end Group

variable (k G α)

/-- The twisted translations form a basis of `k_α[G]` indexed by `G`: the twisted group algebra is
free with basis the elements `TauCeti.TwistedGroupAlgebra.of`. -/
noncomputable def basis : Basis G k (twistedGroupAlgebra k G α) :=
  Basis.span (linearIndependent_twistedTranslation k α)

@[simp]
theorem basis_apply (g : G) : basis k G α g = of g :=
  Subtype.ext <| Basis.coe_span_apply _ _

instance : Module.Free k (twistedGroupAlgebra k G α) :=
  Module.Free.of_basis (basis k G α)

/-- The twisted group algebra has dimension `#G`, as the ordinary group algebra does. For an
infinite `G` both sides are `0`. -/
theorem finrank_eq_natCard [StrongRankCondition k] :
    finrank k (twistedGroupAlgebra k G α) = Nat.card G :=
  finrank_eq_nat_card_basis (basis k G α)

variable {k G α}

/-- An algebra map out of `k_α[G]` is determined by its values on the basis elements. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra k A]
    {f g : twistedGroupAlgebra k G α →ₐ[k] A} (h : ∀ x : G, f (of x) = g (of x)) : f = g :=
  AlgHom.toLinearMap_injective <| (basis k G α).ext fun x ↦ by simpa using h x

section Lift

variable {A : Type*}

/-- The linear extension of a family `u : G → A` along the basis takes the value `u g` at the
basis element `TauCeti.TwistedGroupAlgebra.of g`. -/
theorem constr_of [AddCommMonoid A] [Module k A] (u : G → A) (g : G) :
    (basis k G α).constr k u (of g) = u g := by
  rw [← basis_apply k G α g]
  exact Basis.constr_basis (b := basis k G α) (S := k) u g

variable [Semiring A] [Algebra k A]

/-- **The universal property of the twisted group algebra.** A projective representation of `G`
with factor set `α` in a `k`-algebra `A` -- a family `u : G → A` with `u 1 = 1` and
`u g * u h = α g h • u (g * h)` -- extends to an algebra map `k_α[G] →ₐ[k] A`. Uniqueness is
`TauCeti.TwistedGroupAlgebra.algHom_ext`. -/
noncomputable def lift (u : G → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h : G, u g * u h = (α g h : k) • u (g * h)) :
    twistedGroupAlgebra k G α →ₐ[k] A :=
  AlgHom.ofLinearMap ((basis k G α).constr k u)
    (by rw [← of_one (α := α), constr_of, hu₁])
    (by
      have hleft : ∀ (g : G) (y : twistedGroupAlgebra k G α),
          ((basis k G α).constr k u) (of g * y)
            = ((basis k G α).constr k u) (of g) * ((basis k G α).constr k u) y := by
        intro g
        have key : ((basis k G α).constr k u) ∘ₗ LinearMap.mulLeft k (of g)
            = LinearMap.mulLeft k (((basis k G α).constr k u) (of g)) ∘ₗ
              ((basis k G α).constr k u) := by
          refine (basis k G α).ext fun h ↦ ?_
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, basis_apply, of_mul_of,
            map_smul, constr_of, hu g h]
        exact fun y ↦ congrFun (congrArg DFunLike.coe key) y
      intro x y
      have key : ((basis k G α).constr k u) ∘ₗ LinearMap.mulRight k y
          = LinearMap.mulRight k (((basis k G α).constr k u) y) ∘ₗ ((basis k G α).constr k u) := by
        refine (basis k G α).ext fun g ↦ ?_
        simpa using hleft g y
      exact congrFun (congrArg DFunLike.coe key) x)

@[simp]
theorem lift_of (u : G → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h : G, u g * u h = (α g h : k) • u (g * h)) (g : G) :
    lift u hu₁ hu (of g) = u g :=
  constr_of u g

end Lift

section Trivial

variable (k G)

/-- For the trivial factor set the basis elements multiply exactly as the group elements do, so
they assemble into an algebra map to the group algebra. -/
noncomputable def toMonoidAlgebra :
    twistedGroupAlgebra k G (1 : G → G → kˣ) →ₐ[k] MonoidAlgebra k G :=
  lift (fun g ↦ MonoidAlgebra.single g (1 : k)) (by simp [MonoidAlgebra.one_def]) (by simp)

@[simp]
theorem toMonoidAlgebra_of (g : G) :
    toMonoidAlgebra k G (of g) = MonoidAlgebra.single g (1 : k) :=
  lift_of ..

/-- For the trivial factor set the basis elements form a copy of `G` inside `k_1[G]`, giving an
algebra map from the group algebra by its universal property. -/
noncomputable def fromMonoidAlgebra :
    MonoidAlgebra k G →ₐ[k] twistedGroupAlgebra k G (1 : G → G → kˣ) :=
  MonoidAlgebra.lift k _ G ⟨⟨of, of_one⟩, fun g h ↦ by simp [of_mul_of]⟩

@[simp]
theorem fromMonoidAlgebra_single (g : G) :
    fromMonoidAlgebra k G (MonoidAlgebra.single g (1 : k)) = of g := by
  simp [fromMonoidAlgebra]

/-- **The twisted group algebra of the trivial factor set is the group algebra.** -/
noncomputable def monoidAlgebraEquiv :
    twistedGroupAlgebra k G (1 : G → G → kˣ) ≃ₐ[k] MonoidAlgebra k G :=
  AlgEquiv.ofAlgHom (toMonoidAlgebra k G) (fromMonoidAlgebra k G) (by ext g; simp) (by ext g; simp)

@[simp]
theorem monoidAlgebraEquiv_of (g : G) :
    monoidAlgebraEquiv k G (of g) = MonoidAlgebra.single g (1 : k) :=
  toMonoidAlgebra_of k G g

variable {k G}

end Trivial

section Coboundary

variable (α) (β : G → G → kˣ) [IsFactorSet β]

/-- A function witnessing that two factor sets are cohomologous is automatically normalized at
`1`. -/
theorem eq_one_of_coboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) : c 1 = 1 := by
  simpa [IsFactorSet.one_left (α := α), IsFactorSet.one_left (α := β)] using hc 1 1

/-- Rescaling the basis elements by `c` carries the multiplication table of `β` to that of `α`,
giving an algebra map `k_β[G] →ₐ[k] k_α[G]`. -/
noncomputable def homOfCoboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) :
    twistedGroupAlgebra k G β →ₐ[k] twistedGroupAlgebra k G α :=
  lift (α := β) (fun g ↦ (c g : k) • (of g : twistedGroupAlgebra k G α))
    (by simp [eq_one_of_coboundary α β c hc])
    (fun g h ↦ by simp [smul_smul, ← Units.val_mul, hc g h, mul_comm, mul_left_comm])

@[simp]
theorem homOfCoboundary_of (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) (g : G) :
    homOfCoboundary α β c hc (of g) = (c g : k) • of g :=
  lift_of ..

omit [IsFactorSet α] [IsFactorSet β] in
/-- The inverse rescaling witnesses the same cohomology relation with the two factor sets
exchanged; this is what makes `TauCeti.TwistedGroupAlgebra.homOfCoboundary` invertible. -/
theorem coboundary_inv (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) (g h : G) :
    α g h * (c (g * h))⁻¹ = β g h * ((c g)⁻¹ * (c h)⁻¹) := by
  have hβ : β g h = α g h * (c g * c h) * (c (g * h))⁻¹ := eq_mul_inv_of_mul_eq (hc g h)
  rw [hβ, ← mul_inv, mul_right_comm, mul_inv_cancel_right]

/-- **Cohomologous factor sets have isomorphic twisted group algebras**, so `k_α[G]` depends up to
isomorphism only on the class of `α` in `H²(G, kˣ)`. The isomorphism rescales the basis element at
`g` by `c g`. -/
noncomputable def equivOfCoboundary (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) :
    twistedGroupAlgebra k G β ≃ₐ[k] twistedGroupAlgebra k G α :=
  AlgEquiv.ofAlgHom (homOfCoboundary α β c hc)
    (homOfCoboundary β α (fun g ↦ (c g)⁻¹) (coboundary_inv α β c hc))
    (by ext g; simp [smul_smul, ← Units.val_mul])
    (by ext g; simp [smul_smul, ← Units.val_mul])

@[simp]
theorem equivOfCoboundary_of (c : G → kˣ)
    (hc : ∀ g h : G, β g h * c (g * h) = α g h * (c g * c h)) (g : G) :
    equivOfCoboundary α β c hc (of g) = (c g : k) • of g :=
  homOfCoboundary_of α β c hc g

end Coboundary

end TwistedGroupAlgebra

end Algebra

end TauCeti
