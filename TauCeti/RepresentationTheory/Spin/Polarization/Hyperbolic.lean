/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.RepresentationTheory.Spin.Polarization.Basic

/-!
# The split polarization of a hyperbolic quadratic space

`TauCeti.SpinPolarizationData.ofNondegenerate` produces polarization data for any
finite-dimensional nondegenerate quadratic space over a separably closed field, but it does so by
normalizing an arbitrary form, so its two isotropic summands are not given by a formula. A consumer
that has to exhibit its carrier -- as the Chevalley--Demazure construction of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md` does -- needs the split case written down instead.

This file writes it down. For a module `M` over a commutative ring `K`, Mathlib's
`QuadraticForm.dualProd K M` is the hyperbolic form `Q (f, m) = f m` on `Module.Dual K M × M`, and
its two coordinate summands `Submodule.snd` and `Submodule.fst` are isotropic and dually paired by
construction:

```text
polar Q (f, m) (g, x) = f x + g m.
```

`TauCeti.SpinPolarizationData.hyperbolic` packages them as a `TauCeti.SpinPolarizationData`, with
the copy of `M` as the exterior summand `W`, the copy of its dual as the contraction summand `W'`,
and no orthogonal remainder, so the spinor module attached to it is the full exterior algebra of
`M`. The only hypothesis is that the functionals on `M` separate its points, which is what
identifies `W'` with the dual of `W`; by `Module.forall_dual_apply_eq_zero_iff` that holds for
every projective module, in particular over a field.

Nothing here constructs a Clifford action, a Lie algebra or a group: this file supplies the
decomposition data those constructions take as input, and it asserts nothing about the quadratic
space beyond the fields of the structure and the nondegeneracy they imply.

## Main definitions

* `TauCeti.SpinPolarizationData.hyperbolicDecomposition`: the direct-sum coordinates of the
  hyperbolic quadratic space, from Mathlib's `Submodule.prodEquivOfIsCompl`.
* `TauCeti.SpinPolarizationData.hyperbolic`: the polarization data of `QuadraticForm.dualProd`.
* `TauCeti.SpinPolarizationData.hyperbolicBasis`: the basis of the exterior summand transported
  from a basis of `M`.

## Main results

* `TauCeti.polar_dualProd`: the polar form of the hyperbolic form.
* `TauCeti.isCompl_snd_fst`: the two coordinate summands of a product module are complementary.
* `TauCeti.SpinPolarizationData.hyperbolic_W`, `hyperbolic_W'` and `hyperbolic_line`: the summands
  of the constructed data.
* `TauCeti.SpinPolarizationData.nondegenerate_dualProd`: the hyperbolic form is nondegenerate, the
  vanishing remainder removing every hypothesis on `2`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the exterior model attached to
  a split decomposition.
* N. Bourbaki, *Algèbre*, Chapter 9, §4, for hyperbolic quadratic spaces.

## Roadmap

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, "The Chevalley--Demazure construction",
requires an explicitly constructed carrier rather than an existence theorem, and the type-`Bₗ` and
type-`Dₗ` carriers are built on the spinor module of a split quadratic space. This file supplies
the split decomposition those carriers are built from; the consumer of the type-`D` instance is
milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`, whose `Dₙ(q)` and `²Dₙ(q)` branches need
a traceable pinned simply connected type-`D` carrier.
-/

public section

open QuadraticMap

namespace TauCeti

universe u v w

variable {K : Type u} [CommRing K] {M : Type v} [AddCommGroup M] [Module K M]

/-! ## The polar form of the hyperbolic form -/

/-- **The polar form of the hyperbolic quadratic form** `Q (f, m) = f m` pairs each coordinate
summand with the other and neither with itself. -/
@[simp]
theorem polar_dualProd (p q : Module.Dual K M × M) :
    polar (QuadraticForm.dualProd K M) p q = p.1 q.2 + q.1 p.2 := by
  simp only [polar, QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add,
    LinearMap.add_apply, map_add]
  ring

/-- **The two coordinate summands of a product module are complementary**, in the order the
polarization below uses them: the copy of the second factor and then the copy of the first. -/
theorem isCompl_snd_fst (R : Type u) [Semiring R] (M₁ : Type v) (M₂ : Type w) [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] :
    IsCompl (Submodule.snd R M₁ M₂) (Submodule.fst R M₁ M₂) :=
  (⟨disjoint_iff.mpr (Submodule.fst_inf_snd R M₁ M₂),
    codisjoint_iff.mpr (Submodule.fst_sup_snd R M₁ M₂)⟩ : IsCompl _ _).symm

namespace SpinPolarizationData

/-- The exterior summand of the hyperbolic quadratic space is cut out by the vanishing of the
first coordinate. -/
private theorem mem_snd_iff {p : Module.Dual K M × M} :
    p ∈ Submodule.snd K (Module.Dual K M) M ↔ p.1 = 0 :=
  Submodule.mem_comap.trans (Submodule.mem_bot K)

/-- The contraction summand of the hyperbolic quadratic space is cut out by the vanishing of the
second coordinate. -/
private theorem mem_fst_iff {p : Module.Dual K M × M} :
    p ∈ Submodule.fst K (Module.Dual K M) M ↔ p.2 = 0 :=
  Submodule.mem_comap.trans (Submodule.mem_bot K)

/-! ## The polarization data -/

variable (K M)

/-- **The direct-sum coordinates of the hyperbolic quadratic space**: its two coordinate summands
`Submodule.snd` and `Submodule.fst`, which are complementary, together with a trivial orthogonal
remainder. -/
noncomputable def hyperbolicDecomposition :
    ((Submodule.snd K (Module.Dual K M) M × Submodule.fst K (Module.Dual K M) M) ×
        (⊥ : Submodule K (Module.Dual K M × M))) ≃ₗ[K] Module.Dual K M × M :=
  LinearEquiv.prodUnique ≪≫ₗ
    Submodule.prodEquivOfIsCompl _ _ (isCompl_snd_fst K (Module.Dual K M) M)

variable {K M}

@[simp]
theorem hyperbolicDecomposition_apply
    (x : (Submodule.snd K (Module.Dual K M) M × Submodule.fst K (Module.Dual K M) M) ×
      (⊥ : Submodule K (Module.Dual K M × M))) :
    hyperbolicDecomposition K M x =
      (x.1.1 : Module.Dual K M × M) + (x.1.2 : Module.Dual K M × M) :=
  -- `(rfl)`, not `rfl`: the body of `hyperbolicDecomposition` is not `@[expose]`d.
  (rfl)

/-- **The split polarization of a hyperbolic quadratic space.** For a module `M` over a commutative
ring `K` whose functionals separate points, the hyperbolic form `Q (f, m) = f m` on
`Module.Dual K M × M` is polarized by its two coordinate summands, with no orthogonal remainder.

The exterior summand `W` is the copy of `M` and the contraction summand `W'` is the copy of its
dual, so the spinor module attached to this datum is the full exterior algebra of `M`. -/
noncomputable def hyperbolic (hM : ∀ m : M, (∀ f : Module.Dual K M, f m = 0) → m = 0) :
    SpinPolarizationData (QuadraticForm.dualProd K M) where
  W := Submodule.snd K (Module.Dual K M) M
  W' := Submodule.fst K (Module.Dual K M) M
  line := ⊥
  decompositionEquiv := hyperbolicDecomposition K M
  decompositionEquiv_apply x := by
    rw [hyperbolicDecomposition_apply, (Submodule.mem_bot K).mp x.2.2, add_zero]
  isotropic_W x := by
    rw [QuadraticForm.dualProd_apply, mem_snd_iff.mp x.2, LinearMap.zero_apply]
  isotropic_W' y := by
    rw [QuadraticForm.dualProd_apply, mem_fst_iff.mp y.2, map_zero]
  pairingEquiv :=
    (Submodule.fstEquiv K (Module.Dual K M) M) ≪≫ₗ
      (Submodule.sndEquiv K (Module.Dual K M) M).dualMap
  pairingEquiv_apply y x := by
    rw [polar_dualProd, mem_snd_iff.mp x.2, LinearMap.zero_apply, zero_add,
      LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Submodule.fstEquiv_apply,
      Submodule.sndEquiv_apply]
  pairing_separatingLeft x hx := by
    refine Subtype.ext (Prod.ext (mem_snd_iff.mp x.2) (hM _ fun f => ?_))
    have := hx ⟨(f, 0), mem_fst_iff.mpr rfl⟩
    rwa [polar_dualProd, mem_snd_iff.mp x.2, LinearMap.zero_apply, zero_add] at this
  lineCoordinate := 0
  lineCoordinate_injective a b _ := by
    refine Subtype.ext ?_
    rw [(Submodule.mem_bot K).mp a.2, (Submodule.mem_bot K).mp b.2]
  lineCoordinate_sq z := by
    rw [LinearMap.zero_apply, mul_zero, (Submodule.mem_bot K).mp z.2, map_zero]
  line_orthogonal_W z x := by
    rw [(Submodule.mem_bot K).mp z.2, polar_zero_left]
  line_orthogonal_W' z y := by
    rw [(Submodule.mem_bot K).mp z.2, polar_zero_left]

variable (hM : ∀ m : M, (∀ f : Module.Dual K M, f m = 0) → m = 0)

@[simp]
theorem hyperbolic_W : (hyperbolic hM).W = Submodule.snd K (Module.Dual K M) M :=
  -- `(rfl)`, not `rfl`: the body of `hyperbolic` is not `@[expose]`d.
  (rfl)

@[simp]
theorem hyperbolic_W' : (hyperbolic hM).W' = Submodule.fst K (Module.Dual K M) M := (rfl)

@[simp]
theorem hyperbolic_line : (hyperbolic hM).line = ⊥ := (rfl)

/-- **The hyperbolic form is nondegenerate.** It has no orthogonal remainder, so this needs no
regularity hypothesis on `2`, by
`TauCeti.SpinPolarizationData.nondegenerate_of_line_eq_bot`. -/
theorem nondegenerate_dualProd (hM : ∀ m : M, (∀ f : Module.Dual K M, f m = 0) → m = 0) :
    (QuadraticForm.dualProd K M).Nondegenerate :=
  (hyperbolic hM).nondegenerate_of_line_eq_bot rfl

/-! ## The basis of the exterior summand -/

/-- A basis of `M` is a basis of the exterior summand of the hyperbolic polarization, which by
`TauCeti.SpinPolarizationData.hyperbolic_W` is the copy of `M` in `Module.Dual K M × M`. This is
the basis the exterior model of the spin representation is coordinatized by. -/
noncomputable def hyperbolicBasis {ι : Type w} (b : Module.Basis ι K M) :
    Module.Basis ι K (Submodule.snd K (Module.Dual K M) M) :=
  b.map (Submodule.sndEquiv K (Module.Dual K M) M).symm

@[simp]
theorem coe_hyperbolicBasis_apply {ι : Type w} (b : Module.Basis ι K M) (i : ι) :
    ((hyperbolicBasis b i : Submodule.snd K (Module.Dual K M) M) : Module.Dual K M × M) =
      (0, b i) := by
  rw [hyperbolicBasis, Module.Basis.map_apply]
  rfl

end SpinPolarizationData

end TauCeti
