/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl

/-!
# The Weyl element normalises the split maximal torus

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ` and preserve an additive
subgroup `M ≤ V`, presented in a weight basis, and let `eᵢ`, `eⱼ` be distinguished root vectors
whose images span, together with the distinguished Cartan vector `h c`, an `sl₂` triple. The two
halves of the pinning built so far are the split torus `t(s)` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Torus.lean`, which acts on a weight
vector of weight `μ` by the character value `μ(s)`, and the Weyl element
`n = x_i(1) x_j(-1) x_i(1)` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Weyl.lean`, which interchanges the
root subgroups of `α` and `-α`. This file proves the remaining pinning relation between them: `n`
normalises the torus, and conjugation by it is the reflection `s_α`.

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
`TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusRange_conj_kostantWeylGL`.

## Main definitions

* `TauCeti.weylReflectTorusPoint`: the point of the split torus obtained by the reflection
  `s_α`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.apply_weylUnit` and
  `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.apply_inv_weylUnit`: the Weyl element
  and its inverse reflect the weight of a weight vector.
* `TauCeti.torusCharacter_weylReflectTorusPoint`: the reflected point computes the reflected
  character.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_kostantTorusPoints` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeylGL_conj_kostantTorusPoints`: conjugating a torus
  point by the Weyl element gives the reflected torus point.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusRange_conj_kostantWeylGL`: the Weyl element
  normalises the split torus.

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

/-! ## The reflected torus point

The reflection `s_α μ = μ - μ(α^∨) α` of weights is dual to a reflection of the points of the
split torus, and the latter is what a conjugation statement about the torus needs. In the
coordinates `κ` of the Cartan family, `α^∨` is the index `c` of the Cartan vector of the `sl₂`
triple, so the dual reflection divides the `c`-th coordinate of a point by the value `α(s)` there
and leaves the others alone. -/

section Reflect

variable [Fintype κ] [DecidableEq κ]

/-- The point of the split torus `𝔾ₘ^κ` obtained from `s` by the reflection `s_α` in the root
`α`, where `c` is the Cartan index of the coroot `α^∨`: the `c`-th coordinate of `s` is divided by
the value `α(s)` and the others are unchanged.

The characterising property is `TauCeti.torusCharacter_weylReflectTorusPoint`: the reflected
point takes at a weight `μ` the value that `s` takes at the reflected weight. -/
def weylReflectTorusPoint (α : κ → ℤ) (c : κ) {A : Type*} [CommRing A] (s : κ → Aˣ) : κ → Aˣ :=
  s * Pi.mulSingle c (torusCharacter s α)⁻¹

/-- **The reflected point computes the reflected character.** The character `μ` takes at the
reflected point the value that `μ - μ(c) α`, the reflection `s_α μ`, takes at the original one. -/
theorem torusCharacter_weylReflectTorusPoint (α : κ → ℤ) (c : κ) {A : Type*} [CommRing A]
    (s : κ → Aˣ) (μ : κ → ℤ) :
    torusCharacter (weylReflectTorusPoint α c s) μ = torusCharacter s (μ - μ c • α) := by
  rw [weylReflectTorusPoint, torusCharacter_mul, torusCharacter_mulSingle, torusCharacter_sub,
    torusCharacter_zsmul, inv_zpow, div_eq_mul_inv]

/-- **The reflection of points is an involution**, as soon as the root takes the value two at its
own coroot. -/
theorem weylReflectTorusPoint_weylReflectTorusPoint (α : κ → ℤ) {c : κ} (hαc : α c = 2)
    {A : Type*} [CommRing A] (s : κ → Aˣ) :
    weylReflectTorusPoint α c (weylReflectTorusPoint α c s) = s := by
  have hneg : α - α c • α = -α := by rw [hαc]; module
  have hchar : torusCharacter (weylReflectTorusPoint α c s) α = (torusCharacter s α)⁻¹ := by
    rw [torusCharacter_weylReflectTorusPoint, hneg, torusCharacter_neg]
  conv_lhs => rw [weylReflectTorusPoint, hchar, inv_inv]
  rw [weylReflectTorusPoint, mul_assoc, ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one,
    mul_one]

end Reflect

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

/-! ## Brackets in the representation -/

/-- A representation of the enveloping algebra turns a bracket of `L` into the commutator of the
two operators. -/
theorem lie_map_ι (x y : L) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x), ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)⁆ =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅x, y⁆) := by
  have hlie := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι ℚ) x y
  rw [LieRing.of_associative_ring_bracket] at hlie
  rw [LieRing.of_associative_ring_bracket, hlie, map_sub, map_mul, map_mul]

/-- An eigenvector of the adjoint action of `x` in `L` stays one in the representation. -/
theorem lie_map_ι_eq_smul {x y : L} {a : ℚ} (hxy : ⁅x, y⁆ = a • y) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x), ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)⁆ =
      a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) := by
  rw [lie_map_ι ρ, hxy, map_smul, map_smul]

/-- The negated form of `TauCeti.UniversalEnvelopingAlgebra.lie_map_ι_eq_smul`, which is the shape
the lowering element of an `sl₂` triple takes. -/
theorem lie_map_ι_eq_neg_smul {x y : L} {a : ℚ} (hxy : ⁅x, y⁆ = -(a • y)) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x), ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)⁆ =
      -(a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  rw [lie_map_ι ρ, hxy]
  simp only [map_neg, map_smul]

variable {i j : ι} {c : κ} {α : κ → ℤ}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ j', ⁅h j', e i⁆ = (α j' : ℚ) • e i)
variable (hαneg : ∀ j', ⁅h j', e j⁆ = -((α j' : ℚ) • e j))

include hT hα in
/-- **A root takes the value two at its own coroot.** The Cartan index `c` of the `sl₂` triple is
the coroot of the weight `α` of the raising element, so the weight of `eᵢ` at `h c` is two.

This is not an extra normalisation: it is forced by the triple relation `⁅h, e⁆ = 2 e`, together
with `e ≠ 0`, which the triple also forces since `⁅e, f⁆ = h` is nonzero. -/
theorem eq_two_of_isSl2Triple : α c = 2 := by
  have hne : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ≠ 0 := by
    intro h0
    exact hT.h_ne_zero (by rw [← hT.lie_e_f, h0]; exact zero_lie _)
  have hE : ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)),
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))⁆ =
      (α c : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) :=
    lie_map_ι_eq_smul ρ (hα c)
  have hE2 : ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)),
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))⁆ =
      (2 : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) := by
    rw [hT.lie_h_e_nsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    norm_num
  have hzero : ((α c : ℚ) - 2) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) = 0 := by
    rw [sub_smul, ← hE, ← hE2, sub_self]
  rcases smul_eq_zero.1 hzero with hz | hz
  · exact_mod_cast sub_eq_zero.1 hz
  · exact absurd hz hne

/-! ## The Weyl element reflects weights -/

include hT hα hαneg in
/-- **The Weyl element reflects weights.** A weight vector of weight `μ` is carried by the Weyl
element of the root pair `(eᵢ, eⱼ)` to a weight vector of the reflected weight
`s_α μ = μ - μ(c) α`, where `α` is the weight of `eᵢ` and `c` is the Cartan index of the coroot.

The proof is the coreflection formula `TauCeti.inv_weylUnit_conj_of_lie_eq_smul` applied to each
designated Cartan operator; no property of `μ` beyond being a weight is used. -/
theorem IsCartanWeightVector.apply_weylUnit {μ : κ → ℤ} {v : V}
    (hv : IsCartanWeightVector h ρ μ v) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      (((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) := by
  intro j'
  have hcancel : ∀ z : V, ((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V)
      ((((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) z) = z := fun z => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have key := inv_weylUnit_conj_of_lie_eq_smul hT hi hj
    (lie_map_ι_eq_smul ρ (hα j')) (lie_map_ι_eq_neg_smul ρ (hαneg j'))
  have happ := congrArg (fun f : Module.End ℚ V => f v) key
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at happ
  rw [hv j', hv c] at happ
  have hgoal : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j'))
      (((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) =
      ((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V)
        ((μ j' : ℚ) • v - (α j' : ℚ) • ((μ c : ℚ) • v)) := by
    rw [← happ, hcancel]
  rw [hgoal]
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  module

include hT hα hαneg in
/-- **The inverse Weyl element reflects weights.** The coreflection is an involution on the
designated Cartan operators, so conjugating by `n⁻¹` reflects a weight exactly as conjugating by
`n` does. -/
theorem IsCartanWeightVector.apply_inv_weylUnit {μ : κ → ℤ} {v : V}
    (hv : IsCartanWeightVector h ρ μ v) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      ((((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) := by
  intro j'
  have hcancel : ∀ z : V, (((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V)
      (((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) z) = z := fun z => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have key := weylUnit_conj_of_lie_eq_smul hT hi hj
    (lie_map_ι_eq_smul ρ (hα j')) (lie_map_ι_eq_neg_smul ρ (hαneg j'))
  have happ := congrArg (fun f : Module.End ℚ V => f v) key
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at happ
  rw [hv j', hv c] at happ
  have hgoal : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j'))
      ((((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) =
      (((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V)
        ((μ j' : ℚ) • v - (α j' : ℚ) • ((μ c : ℚ) • v)) := by
    rw [← happ, hcancel]
  rw [hgoal]
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  module

include hM hT hα hαneg in
/-- The integral Weyl element of the lattice reflects the weight of a weight vector of the
lattice. -/
theorem IsCartanWeightVector.apply_kostantWeylRestrict {μ : κ → ℤ} {v : M}
    (hv : IsCartanWeightVector h ρ μ (v : V)) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      ((kostantWeylRestrict e h ρ M hM hi hj v : M) : V) := by
  rw [coe_kostantWeylRestrict_apply, Module.End.smul_def]
  exact IsCartanWeightVector.apply_weylUnit e h ρ hi hj hT hα hαneg hv

include hM hT hα hαneg in
/-- The inverse of the integral Weyl element reflects the weight of a weight vector of the
lattice. -/
theorem IsCartanWeightVector.apply_kostantWeylRestrict_symm {μ : κ → ℤ} {v : M}
    (hv : IsCartanWeightVector h ρ μ (v : V)) :
    IsCartanWeightVector h ρ (μ - μ c • α)
      (((kostantWeylRestrict e h ρ M hM hi hj).symm v : M) : V) := by
  rw [coe_kostantWeylRestrict_symm_apply, Module.End.smul_def]
  exact IsCartanWeightVector.apply_inv_weylUnit e h ρ hi hj hT hα hαneg hv

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
      (((kostantWeylRestrict e h ρ M hM hi hj).symm (b x) : M) : V) :=
    IsCartanWeightVector.apply_kostantWeylRestrict_symm e h ρ M hM hi hj hT hα hαneg (hwt x)
  have h1 : (kostantWeylPoints e h ρ M hM hi hj A).symm.toLinearMap
      ((1 : A) ⊗ₜ[ℤ] (b x : M)) =
      (1 : A) ⊗ₜ[ℤ] ((kostantWeylRestrict e h ρ M hM hi hj).symm (b x)) := by
    rw [LinearEquiv.coe_coe, kostantWeylPoints_symm_apply_tmul]
  have h2 : (kostantTorusPoints M b wt A s).val
      ((1 : A) ⊗ₜ[ℤ] ((kostantWeylRestrict e h ρ M hM hi hj).symm (b x))) =
      ((torusCharacter s (wt x - wt x c • α) : A) * 1) ⊗ₜ[ℤ]
        ((kostantWeylRestrict e h ρ M hM hi hj).symm (b x)) :=
    kostantTorusPoints_tmul_of_isCartanWeightVector e h ρ M hM b wt hwt hrefl s 1
  have h3 : (kostantWeylPoints e h ρ M hM hi hj A).toLinearMap
      (((torusCharacter s (wt x - wt x c • α) : A) * 1) ⊗ₜ[ℤ]
        ((kostantWeylRestrict e h ρ M hM hi hj).symm (b x))) =
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
/-- **The Weyl element normalises the split maximal torus.** Conjugation by it permutes the torus
points by the reflection `s_α`, which is an involution, so it carries the group of torus points
onto itself. -/
theorem map_kostantTorusRange_conj_kostantWeylGL
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) :
    Subgroup.map (MulAut.conj (kostantWeylGL e h ρ M hM hi hj A)).toMonoidHom
        (kostantTorusPoints M b wt A).range =
      (kostantTorusPoints M b wt A).range := by
  classical
  have hαc : α c = 2 := eq_two_of_isSl2Triple e h ρ hT hα
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
