/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# The Weyl element normalises the split torus

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ` and preserve an additive
subgroup `M ≤ V`, presented in a weight basis, and let `eᵢ`, `eⱼ` be distinguished root vectors
whose images span, together with the distinguished Cartan vector `h c`, an `sl₂` triple. The two
halves of the pinning built so far are the split torus `t(s)` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Torus.lean`, which acts on a weight
vector of weight `μ` by the character value `μ(s)`, and the Weyl element
`n = x_i(1) x_j(-1) x_i(1)` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Weyl/Basic.lean`, which
interchanges the root subgroups of `α` and `-α`. This file proves the remaining pinning relation
between them: `n` normalises the torus, and conjugation by it is the reflection `s_α`.

The mechanism is the coreflection formula for the Weyl element,
`TauCeti.inv_weylUnit_conj_of_lie_eq_smul`, which says that an operator acting on the raising and
lowering elements by the opposite scalars `c` and `-c` is conjugated to `y - c • H`. Applied to the
designated Cartan operators `ρ(hⱼ)`, with `α` the weight of `eᵢ`, it gives

```text
n⁻¹ ρ(hⱼ) n = ρ(hⱼ) - αⱼ ρ(h c),
```

so `n` carries a weight vector of weight `μ` to one of weight `s_α μ = μ - μ(c) α`. That is the
reflection acting on the weight lattice of the admissible lattice `M`, realised by an element of
the Chevalley group. Since a torus point acts on a weight vector by its character, the conjugate
`n t(s) n⁻¹` acts on a weight vector of weight `μ` by `(s_α μ)(s)`, which is the value at `μ` of the
character of the reflected point

```text
s_α(s) = s · α(s)⁻¹ at the coordinate c, and s elsewhere.
```

Nothing about the ring of points enters: the identities hold over every commutative ring, in
particular in characteristics two and three, because the whole content is the rational
Lie-algebra identity above transported through the integral divided powers.

The reflection of points is an involution, `α(α^∨) = 2` being forced by the `sl₂` triple, so the
conjugation statement upgrades from an inclusion to the equality of subgroups
`TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusPoints_range_conj_kostantWeylGL`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.weylUnit` and
  `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.inv_weylUnit`: the Weyl element
  and its inverse reflect the weight of a weight vector.
* `TauCeti.torusCharacter_weylReflectTorusPoint`: the reflected point computes the reflected
  character.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_kostantTorusPoints` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylGL_conj_kostantTorusPoints`: conjugating a torus
  point by the Weyl element gives the reflected torus point.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusPoints_range_conj_kostantWeylGL`: the Weyl
  element normalises the split torus.

## Roadmap

This completes the normaliser-of-the-torus relation of the pinning data in Layer 9, "pinned
Chevalley--Demazure group schemes over `ℤ`", of `TauCetiRoadmap/ReductiveGroups/README.md`, and is
consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open TensorProduct

namespace TauCeti

universe u v w

variable {κ : Type*}

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

variable {i j : ι} {c : κ} {α : κ → ℤ}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ j', ⁅h j', e i⁆ = (α j' : ℚ) • e i)
variable (hαneg : ∀ j', ⁅h j', e j⁆ = -((α j' : ℚ) • e j))

include hT in
/-- **A root takes the value two at its own coroot.** The Cartan index `c` of the `sl₂` triple is
the coroot of the weight `α` of the raising element, so the weight of `eᵢ` at `h c` is two.

This is not an extra normalisation: it is forced by the triple relation `⁅h, e⁆ = 2 e`, together
with `e ≠ 0`, which the triple also forces since `⁅e, f⁆ = h` is nonzero. -/
theorem rootWeight_apply_coroot_eq_two
    (hαc : ⁅h c, e i⁆ = (α c : ℚ) • e i) : α c = 2 := by
  have hαc' : (α c : ℚ) = 2 := TauCeti.IsSl2Triple.eq_two_of_lie_h_e_eq_smul hT
    (lie_map_ι_eq_smul ρ hαc)
  exact_mod_cast hαc'

/-! ## The Weyl element reflects weights -/

/-- Transport a Cartan weight vector through a unit whose inverse conjugation reflects every
designated Cartan operator. -/
private theorem IsCartanWeightVector.unit_of_conj {μ : κ → ℤ} {v : V}
    (hv : IsCartanWeightVector h ρ μ v) (n : (Module.End ℚ V)ˣ)
    (hconj : ∀ j', (((n⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) *
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j')) *
        (n : Module.End ℚ V)) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j')) -
        (α j' : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c))) :
    IsCartanWeightVector h ρ (μ - μ c • α) ((n : Module.End ℚ V) v) := by
  apply (isCartanWeightVector_iff (h := h) (ρ := ρ)).2
  intro j'
  have hcancel : ∀ z : V, (n : Module.End ℚ V)
      (((n⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) z) = z := fun z => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have happ := congrArg (fun f : Module.End ℚ V => f v) (hconj j')
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at happ
  have hv' := (isCartanWeightVector_iff (h := h) (ρ := ρ)).1 hv
  rw [hv' j', hv' c] at happ
  have hgoal : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j'))
      ((n : Module.End ℚ V) v) =
      (n : Module.End ℚ V) ((μ j' : ℚ) • v - (α j' : ℚ) • ((μ c : ℚ) • v)) := by
    rw [← happ, hcancel]
  rw [hgoal]
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  module

/-- The lowering root vector has the negated root weight after applying the representation. -/
private theorem lie_rho_h_rho_e_j
    (hαneg : ∀ j', ⁅h j', e j⁆ = -((α j' : ℚ) • e j)) (j' : κ) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j')),
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))⁆ =
      -((α j' : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) := by
  simpa only [neg_smul] using
    (lie_map_ι_eq_smul ρ (a := -(α j' : ℚ)) (by simpa only [neg_smul] using hαneg j'))

include hT hα hαneg in
/-- **The Weyl element reflects weights.** A weight vector of weight `μ` is carried by the Weyl
element of the root pair `(eᵢ, eⱼ)` to a weight vector of the reflected weight
`s_α μ = μ - μ(c) α`, where `α` is the weight of `eᵢ` and `c` is the Cartan index of the coroot.

The proof is the coreflection formula `TauCeti.inv_weylUnit_conj_of_lie_eq_smul` applied to each
designated Cartan operator; no property of `μ` beyond being a weight is used. -/
theorem IsCartanWeightVector.weylUnit {μ : κ → ℤ} {v : V}
    (hv : IsCartanWeightVector h ρ μ v) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      (((TauCeti.weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) := by
  apply IsCartanWeightVector.unit_of_conj (h := h) (ρ := ρ) hv (TauCeti.weylUnit hi hj)
  intro j'
  exact inv_weylUnit_conj_of_lie_eq_smul hT hi hj
    (lie_map_ι_eq_smul ρ (hα j')) (lie_rho_h_rho_e_j e h ρ hαneg j')

include hT hα hαneg in
/-- **The inverse Weyl element reflects weights.** The coreflection is an involution on the
designated Cartan operators, so conjugating by `n⁻¹` reflects a weight exactly as conjugating by
`n` does. -/
theorem IsCartanWeightVector.inv_weylUnit {μ : κ → ℤ} {v : V}
    (hv : IsCartanWeightVector h ρ μ v) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      ((((TauCeti.weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) := by
  apply IsCartanWeightVector.unit_of_conj (h := h) (ρ := ρ) hv (TauCeti.weylUnit hi hj)⁻¹
  intro j'
  simpa only [inv_inv] using weylUnit_conj_of_lie_eq_smul hT hi hj
    (lie_map_ι_eq_smul ρ (hα j')) (lie_rho_h_rho_e_j e h ρ hαneg j')

include hM hT hα hαneg in
/-- The integral Weyl element of the lattice reflects the weight of a weight vector of the
lattice. -/
theorem IsCartanWeightVector.kostantWeylRestrict {μ : κ → ℤ} {v : M}
    (hv : IsCartanWeightVector h ρ μ (v : V)) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      ((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
        e h ρ M hM hi hj v : M) : V) := by
  rw [coe_kostantWeylRestrict_apply, Module.End.smul_def]
  exact IsCartanWeightVector.weylUnit e h ρ hi hj hT hα hαneg hv

include hM hT hα hαneg in
/-- The inverse of the integral Weyl element reflects the weight of a weight vector of the
lattice. -/
theorem IsCartanWeightVector.kostantWeylRestrict_symm {μ : κ → ℤ} {v : M}
    (hv : IsCartanWeightVector h ρ μ (v : V)) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      (((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
        e h ρ M hM hi hj).symm v : M) : V) := by
  rw [coe_kostantWeylRestrict_symm_apply, Module.End.smul_def]
  exact IsCartanWeightVector.inv_weylUnit e h ρ hi hj hT hα hαneg hv

/-! ## Conjugation of the torus -/

section Conjugation

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable [Fintype κ] [DecidableEq κ]
variable {A : Type*} [CommRing A] [Algebra ℤ A]

include hM hT hα hαneg in
/-- **The Weyl element conjugates a torus point to the reflected torus point.** Over every
commutative ring of points,

```text
n t(s) n⁻¹ = t(s_α s),
```

with `s_α s` the reflected point of
`TauCeti.weylReflectTorusPoint`. Both sides are diagonal on the weight
basis: `n⁻¹` moves a basis vector of weight `μ` into the space of weight `s_α μ`, where `t(s)`
scales by `(s_α μ)(s)`, and `n` moves it back. -/
theorem kostantWeylPoints_conj_kostantTorusPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) (s : κ → Aˣ) :
    (kostantWeylPoints e h ρ M hM hi hj A).toLinearMap * (kostantTorusPoints M b wt A s).val *
        (kostantWeylPoints e h ρ M hM hi hj A).symm.toLinearMap =
      (kostantTorusPoints M b wt A (weylReflectTorusPoint α c s)).val := by
  refine Module.Basis.ext (b.baseChange A) fun x => ?_
  have hrefl : IsCartanWeightVector h ρ (wt x - wt x c • α)
      (((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
        e h ρ M hM hi hj).symm (b x) : M) : V) :=
    IsCartanWeightVector.kostantWeylRestrict_symm e h ρ M hM hi hj hT hα hαneg (hwt x)
  have h1 : (kostantWeylPoints e h ρ M hM hi hj A).symm.toLinearMap
      ((1 : A) ⊗ₜ[ℤ] (b x : M)) =
      (1 : A) ⊗ₜ[ℤ] ((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
        e h ρ M hM hi hj).symm (b x)) := by
    rw [LinearEquiv.coe_coe, kostantWeylPoints_symm_apply_tmul]
  have h2 : (kostantTorusPoints M b wt A s).val
      ((1 : A) ⊗ₜ[ℤ] ((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
        e h ρ M hM hi hj).symm (b x))) =
      ((torusCharacter s (wt x - wt x c • α) : A) * 1) ⊗ₜ[ℤ]
        ((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
          e h ρ M hM hi hj).symm (b x)) :=
    kostantTorusPoints_tmul_of_isCartanWeightVector e h ρ M hM b wt hwt hrefl s 1
  have h3 : (kostantWeylPoints e h ρ M hM hi hj A).toLinearMap
      (((torusCharacter s (wt x - wt x c • α) : A) * 1) ⊗ₜ[ℤ]
        ((_root_.TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict
          e h ρ M hM hi hj).symm (b x))) =
      ((torusCharacter s (wt x - wt x c • α) : A) * 1) ⊗ₜ[ℤ] (b x : M) := by
    rw [LinearEquiv.coe_coe, kostantWeylPoints_apply_tmul, LinearEquiv.apply_symm_apply]
  rw [Module.Basis.baseChange_apply, Module.End.mul_apply, Module.End.mul_apply, h1, h2, h3,
    kostantTorusPoints_tmul_basis, torusCharacter_weylReflectTorusPoint]

include hM hT hα hαneg in
/-- **The Weyl element conjugates a torus point to the reflected torus point**, in the general
linear group of the points of the lattice. -/
theorem kostantWeylGL_conj_kostantTorusPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) (s : κ → Aˣ) :
    kostantWeylGL e h ρ M hM hi hj A * kostantTorusPoints M b wt A s *
        (kostantWeylGL e h ρ M hM hi hj A)⁻¹ =
      kostantTorusPoints M b wt A (weylReflectTorusPoint α c s) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, kostantWeylGL_val, kostantWeylGL_inv_val]
  exact kostantWeylPoints_conj_kostantTorusPoints e h ρ M hM hi hj hT hα hαneg b wt hwt s

omit [DecidableEq κ] in
include hM hT hα hαneg in
/-- **The Weyl element normalises the split torus.** Conjugation by it permutes the torus
points by the reflection `s_α`, which is an involution, so it carries the group of torus points
onto itself. -/
theorem map_kostantTorusPoints_range_conj_kostantWeylGL
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) :
    Subgroup.map (MulAut.conj (kostantWeylGL e h ρ M hM hi hj A)).toMonoidHom
        (kostantTorusPoints M b wt A).range =
      (kostantTorusPoints M b wt A).range := by
  classical
  have hαc : α c = 2 := rootWeight_apply_coroot_eq_two e h ρ hT (hα c)
  have hconj : ∀ s : κ → Aˣ, kostantWeylGL e h ρ M hM hi hj A * kostantTorusPoints M b wt A s *
      (kostantWeylGL e h ρ M hM hi hj A)⁻¹ =
        kostantTorusPoints M b wt A (weylReflectTorusPoint α c s) := fun s =>
    kostantWeylGL_conj_kostantTorusPoints e h ρ M hM hi hj hT hα hαneg b wt hwt s
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨s, rfl⟩, rfl⟩
    exact ⟨weylReflectTorusPoint α c s, (hconj s).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨kostantTorusPoints M b wt A (weylReflectTorusPoint α c s),
      ⟨weylReflectTorusPoint α c s, rfl⟩, ?_⟩
    rw [hconj, weylReflectTorusPoint_weylReflectTorusPoint α hαc]

end Conjugation

end UniversalEnvelopingAlgebra

end TauCeti
