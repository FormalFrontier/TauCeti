/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# The split maximal torus of a Kostant elementary group

Let `U_ℤ = kostantForm e h` act on a rational representation `V` through `ρ` and preserve an
additive subgroup `M ≤ V`. A **weight basis** of `M` is an integral basis `b : Basis η ℤ M` each of
whose vectors is a joint eigenvector of the designated Cartan operators `ρ(hⱼ)`, with integer
eigenvalues recorded by `wt : η → κ → ℤ`. Over any commutative ring `A` of points, the split torus
`𝔾ₘ^κ` then acts diagonally on `A ⊗[ℤ] M`: a point `s : κ → Aˣ` scales the basis vector `b x` by
the value `∏ⱼ sⱼ ^ wt x j` of the character `wt x`.

This is the split maximal torus of the pinning. What makes it a *pinned* torus rather than an
arbitrary diagonal group is its interaction with the root subgroups. If the designated root vector
`eᵢ` has weight `α`, meaning `⁅hⱼ, eᵢ⁆ = αⱼ eᵢ` for every `j`, then

```text
t(s) xᵢ(u) t(s)⁻¹ = xᵢ(α(s) u),
```

with `α(s) = ∏ⱼ sⱼ ^ αⱼ` the value at `s` of the same character. So the torus normalizes each root
subgroup, acting on its parameter by the root, and consequently normalizes the whole elementary
group `E(A) = ⟨xᵢ(u)⟩`. Nothing here divides by a factorial, so the equations hold over a value
ring of any characteristic.

The same equation has an infinitesimal form. The designated root vector `eᵢ` restricts to the
integral operator `kostantRootOperator` on `M`, the pinning's `X_α`; it raises weights by `α`,
so a torus point conjugates it to `α(s) X_α`. This is
`kostantTorusPoints_conj_kostantRootOperator`, the other half of what pins the root subgroups
against the torus.

The analogous statement for the worked `GLₙ` example is
`TauCeti.GeneralLinear.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv`; here the diagonal group
is cut down to rank `κ` by the weight function, and the character by which it acts on a root
subgroup is the root rather than a difference `εᵢ - εⱼ` of coordinates.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector`: a joint eigenvector of the designated
  Cartan operators with prescribed integer eigenvalues.
* `TauCeti.UniversalEnvelopingAlgebra.kostantCartanOperator`: a designated Cartan vector as an
  integral operator on a Kostant-stable subgroup.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootOperator`: a designated root vector as an
  integral operator on a Kostant-stable subgroup — the pinning's `X_α`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints`: the split torus of rank `κ` on the
  points of a Kostant-stable lattice presented in a weight basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubgroup`: the image of that torus in the general
  linear group of the base-changed lattice.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix`: the same action in matrix coordinates.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.integralDividedPower`: a divided power
  of a root vector of weight `α` raises the weight of a weight vector by a multiple of `α`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_tmul_of_isCartanWeightVector`: a torus
  point acts on a weight vector by the value of its character.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusPoints`: naturality in the value ring.
* `TauCeti.UniversalEnvelopingAlgebra.mapScalarExtensionAutomorphisms_kostantTorusPoints`:
  scalar extension of a torus point is the torus point with mapped parameter.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam`: the
  pinning equation `t(s) xᵢ(u) t(s)⁻¹ = xᵢ(α(s) u)`.
* `TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_coe_kostantRootOperator`: the root
  operator raises weights by the root `α`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_mul_baseChange_kostantRootOperator`: the
  torus intertwines the root operator up to the value of the root, and
  `TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootOperator` is its
  conjugated form `t(s) X_α t(s)⁻¹ = α(s) X_α`.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantElementarySubgroup_conj_kostantTorusPoints`: the
  torus normalizes the elementary group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type*} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of the enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Weight vectors -/

/-- A vector of `V` is a **weight vector of weight `μ`** when it is a joint eigenvector of the
designated Cartan operators `ρ(hⱼ)` with the integer eigenvalues `μ j`. -/
def IsCartanWeightVector (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (μ : κ → ℤ) (m : V) : Prop :=
  ∀ j, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) m = (μ j : ℚ) • m

/-- The pointwise characterization of a Cartan weight vector. -/
theorem isCartanWeightVector_iff {μ : κ → ℤ} {m : V} :
    IsCartanWeightVector h ρ μ m ↔
      ∀ j, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) m = (μ j : ℚ) • m :=
  Iff.rfl

/-- Being a weight vector is joint membership in the eigenspaces of the Cartan operators. -/
theorem isCartanWeightVector_iff_mem_eigenspace {μ : κ → ℤ} {m : V} :
    IsCartanWeightVector h ρ μ m ↔
      ∀ j, m ∈ Module.End.eigenspace (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)))
        ((μ j : ℚ)) := by
  simp [IsCartanWeightVector]

namespace IsCartanWeightVector

variable {h ρ}

/-- Zero is a weight vector of every weight. -/
theorem zero (μ : κ → ℤ) : IsCartanWeightVector h ρ μ (0 : V) := fun j => by simp

/-- The sum of two weight vectors of the same weight has that weight. -/
theorem add {μ : κ → ℤ} {m n : V} (hm : IsCartanWeightVector h ρ μ m)
    (hn : IsCartanWeightVector h ρ μ n) : IsCartanWeightVector h ρ μ (m + n) := fun j => by
  rw [map_add, hm j, hn j, smul_add]

/-- The negation of a weight vector has the same weight. -/
theorem neg {μ : κ → ℤ} {m : V} (hm : IsCartanWeightVector h ρ μ m) :
    IsCartanWeightVector h ρ μ (-m) := fun j => by
  rw [map_neg, hm j, smul_neg]

/-- The difference of two weight vectors of the same weight has that weight. -/
theorem sub {μ : κ → ℤ} {m n : V} (hm : IsCartanWeightVector h ρ μ m)
    (hn : IsCartanWeightVector h ρ μ n) : IsCartanWeightVector h ρ μ (m - n) := by
  rw [sub_eq_add_neg]
  exact hm.add hn.neg

/-- A rational multiple of a weight vector is a weight vector of the same weight. -/
theorem smul {μ : κ → ℤ} {m : V} (hm : IsCartanWeightVector h ρ μ m) (c : ℚ) :
    IsCartanWeightVector h ρ μ (c • m) := fun j => by
  rw [map_smul, hm j, smul_comm]

/-- If the root vector `eᵢ` has weight `α`, then applying its action `n` times to a weight vector
of weight `μ` produces a weight vector of weight `μ + n α`. -/
theorem pow_rootVector {i : ι} {α μ : κ → ℤ} {m : V}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (hm : IsCartanWeightVector h ρ μ m) (n : ℕ) :
    IsCartanWeightVector h ρ (μ + n • α)
      ((ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ n) m) := by
  -- The image of `eᵢ` is an eigenvector of weight `α` for the adjoint action of the Cartan family.
  have hbr : ∀ j, ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)),
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))⁆ =
      (α j : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) := fun j =>
    lie_map_ι_eq_smul ρ (hα j)
  induction n with
  | zero => simpa using hm
  | succ n ih =>
      intro j
      have hpow : (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ (n + 1)) m =
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
            ((ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ n) m) := by
        rw [pow_succ', Module.End.mul_apply]
      have hbrj := hbr j
      rw [LieRing.of_associative_ring_bracket] at hbrj
      have happ := congrArg (fun f : Module.End ℚ V =>
        f ((ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ n) m)) hbrj
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at happ
      rw [ih j, map_smul, sub_eq_iff_eq_add, ← add_smul] at happ
      have hstep : (μ + (n + 1) • α) j = α j + (μ + n • α) j := by
        simp only [Pi.add_apply, Pi.smul_apply, succ_nsmul]
        abel
      rw [hpow, happ, hstep]
      push_cast
      module

/-- If the root vector `eᵢ` has weight `α`, its `n`-th divided power raises the weight of a weight
vector by `n α`. This is the statement that makes the torus act on a root subgroup through the
root. -/
theorem integralDividedPower {i : ι} {α μ : κ → ℤ} {m : V}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (hm : IsCartanWeightVector h ρ μ m) (n : ℕ) :
    IsCartanWeightVector h ρ (μ + n • α)
      (Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) • m) := by
  rw [Associative.dividedPower_def, smul_assoc]
  exact (pow_rootVector e hα hm n).smul _

end IsCartanWeightVector

/-! ## Cartan operators on a stable subgroup -/

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

/-- A designated Cartan vector acting on a Kostant-stable additive subgroup, as an integral
operator. It is the restriction of `ρ(hⱼ)`, which preserves `M` because `hⱼ` lies in the Kostant
form. -/
noncomputable def kostantCartanOperator (j : κ) : Module.End ℤ M where
  toFun v := ⟨ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) (v : V),
    hM _ (cartanVector_mem_kostantForm e h j) v v.2⟩
  map_add' v w := Subtype.ext (map_add _ (v : V) (w : V))
  map_smul' z v := Subtype.ext (map_zsmul _ z (v : V))

/-- The integral Cartan operator acts by the ambient representation. -/
@[simp] theorem coe_kostantCartanOperator_apply (j : κ) (v : M) :
    ((kostantCartanOperator e h ρ M hM j v : M) : V) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h j)) (v : V) := (rfl)

/-- On a weight vector the integral Cartan operator is multiplication by the integer weight. -/
theorem kostantCartanOperator_apply_of_isCartanWeightVector {μ : κ → ℤ} {v : M}
    (hv : IsCartanWeightVector h ρ μ (v : V)) (j : κ) :
    kostantCartanOperator e h ρ M hM j v = μ j • v :=
  Subtype.ext (by rw [coe_kostantCartanOperator_apply, hv j, AddSubgroup.coe_zsmul,
    Int.cast_smul_eq_zsmul])

/-- In a weight basis, the integral Cartan operator is diagonal: it multiplies the `y`-th
coordinate by `wt y j`. -/
theorem repr_kostantCartanOperator
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) (j : κ) (m : M) (y : η) :
    b.repr (kostantCartanOperator e h ρ M hM j m) y = wt y j * b.repr m y :=
  b.repr_apply_of_apply_basis
    (fun x => kostantCartanOperator_apply_of_isCartanWeightVector e h ρ M hM (hwt x) j) m y

include e hM in
/-- A weight basis separates weights: a weight vector of weight `μ` has vanishing coordinates at
every basis vector of a different weight. -/
theorem repr_eq_zero_of_isCartanWeightVector
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {μ : κ → ℤ} {m : M} (hm : IsCartanWeightVector h ρ μ (m : V)) {y : η} (hy : wt y ≠ μ) :
    b.repr m y = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, wt y j ≠ μ j := Function.ne_iff.1 hy
  have h1 : b.repr (kostantCartanOperator e h ρ M hM j m) y = wt y j * b.repr m y :=
    repr_kostantCartanOperator e h ρ M hM b wt hwt j m y
  have h2 : b.repr (kostantCartanOperator e h ρ M hM j m) y = μ j * b.repr m y := by
    rw [kostantCartanOperator_apply_of_isCartanWeightVector e h ρ M hM hm j]
    simp
  have := sub_eq_zero.2 (h1.symm.trans h2)
  rw [← sub_mul] at this
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hj)

/-! ## Root operators on a stable subgroup -/

section RootOperator

variable (i : ι)

/-- The designated root vector `eᵢ` acting on a Kostant-stable additive subgroup, as an integral
operator.

It is the first restricted divided power of `ρ(eᵢ)`, so it is the linear coefficient of the
divided-power exponential defining the root subgroup, and it is the root vector `X_α` of the
pinning. -/
noncomputable def kostantRootOperator : Module.End ℤ M :=
  integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 1
    (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 1 hv)

/-- The integral root operator acts by the ambient representation of the root vector. -/
@[simp] theorem coe_kostantRootOperator_apply (v : M) :
    ((kostantRootOperator e h ρ M hM i v : M) : V) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (v : V) := by
  rw [kostantRootOperator, coe_integralDividedPower_apply, Associative.dividedPower_one,
    Module.End.smul_def]

include e hM in
/-- The integral root operator raises weights by the root: it is the first divided power of a
root vector of weight `α`. -/
theorem isCartanWeightVector_coe_kostantRootOperator {α μ : κ → ℤ} {v : M}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hv : IsCartanWeightVector h ρ μ ((v : M) : V)) :
    IsCartanWeightVector h ρ (μ + α)
      ((kostantRootOperator e h ρ M hM i v : M) : V) := by
  have hstep := IsCartanWeightVector.integralDividedPower e hα hv 1
  rw [Associative.dividedPower_one, Module.End.smul_def] at hstep
  rw [coe_kostantRootOperator_apply]
  simpa only [one_smul] using hstep

end RootOperator

/-! ## The split torus on points -/

section Torus

variable [Fintype κ]

/-- The split maximal torus of rank `κ` on the `A`-points of a Kostant-stable lattice presented in
a weight basis: the point `s` scales the base-changed basis vector `b x` by the value at `s` of the
character `wt x`. -/
noncomputable def kostantTorusPoints (A : Type*) [CommRing A] [Algebra ℤ A] :
    (κ → Aˣ) →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).symm.toMonoidHom.comp
    (basisWeightTorus (b.baseChange A) wt)

/-- The image of the split weight torus in the general linear group of the base-changed lattice. -/
noncomputable def kostantTorusSubgroup (A : Type*) [CommRing A] [Algebra ℤ A] :
    Subgroup (LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) :=
  (kostantTorusPoints M b wt A).range

-- The public defining equation below cannot itself be `rfl`: the module does not expose the body
-- of `kostantTorusSubgroup`, so the proof is delegated to this private helper.
omit [Module ℚ V] in
private theorem kostantTorusSubgroup_eq_range_def (A : Type*) [CommRing A] [Algebra ℤ A] :
    kostantTorusSubgroup M b wt A = (kostantTorusPoints M b wt A).range :=
  rfl

omit [Module ℚ V] in
/-- The defining equation of `kostantTorusSubgroup`: it is the range of the torus points
homomorphism, so Mathlib's `MonoidHom.mem_range` characterizes its elements. -/
theorem kostantTorusSubgroup_eq_range (A : Type*) [CommRing A] [Algebra ℤ A] :
    kostantTorusSubgroup M b wt A = (kostantTorusPoints M b wt A).range :=
  kostantTorusSubgroup_eq_range_def M b wt A

section Pointwise

variable {A : Type*} [CommRing A] [Algebra ℤ A]

omit [Module ℚ V] in
/-- The linear automorphism underlying a torus point is the diagonal weight automorphism. -/
@[simp] theorem kostantTorusPoints_toLinearEquiv (s : κ → Aˣ) :
    (kostantTorusPoints M b wt A s).toLinearEquiv = basisWeightTorus (b.baseChange A) wt s := by
  rw [kostantTorusPoints]
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).apply_symm_apply _

omit [Module ℚ V] in
/-- A torus point acts by the diagonal weight automorphism of the base-changed basis. -/
theorem kostantTorusPoints_apply (s : κ → Aˣ) (z : A ⊗[ℤ] M) :
    (kostantTorusPoints M b wt A s).val z = basisWeightTorus (b.baseChange A) wt s z := by
  rw [← LinearMap.GeneralLinearGroup.coe_toLinearEquiv, kostantTorusPoints_toLinearEquiv]

include e hM in
/-- A torus point acts on a weight vector by the value of the corresponding character. -/
theorem kostantTorusPoints_tmul_of_isCartanWeightVector
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {μ : κ → ℤ} {m : M} (hm : IsCartanWeightVector h ρ μ (m : V)) (s : κ → Aˣ) (a : A) :
    (kostantTorusPoints M b wt A s).val (a ⊗ₜ[ℤ] m) =
      ((torusCharacter s μ : A) * a) ⊗ₜ[ℤ] m := by
  rw [kostantTorusPoints_apply,
    basisWeightTorus_apply_of_repr_eq_zero (b.baseChange A) wt s (μ := μ) (m := a ⊗ₜ[ℤ] m)
      (fun x hx => by
        rw [Module.Basis.baseChange_repr_tmul,
          repr_eq_zero_of_isCartanWeightVector e h ρ M hM b wt hwt hm hx]
        simp [Algebra.smul_def]),
    smul_tmul', smul_eq_mul]

omit [Module ℚ V] in
/-- A torus point scales a base-changed basis vector by the value of its weight character. -/
@[simp] theorem kostantTorusPoints_tmul_basis (s : κ → Aˣ) (a : A) (x : η) :
    (kostantTorusPoints M b wt A s).val (a ⊗ₜ[ℤ] b x) =
      ((torusCharacter s (wt x) : A) * a) ⊗ₜ[ℤ] b x := by
  rw [kostantTorusPoints_apply,
    basisWeightTorus_apply_of_repr_eq_zero (b.baseChange A) wt s (μ := wt x)
      (m := a ⊗ₜ[ℤ] (b x : M)) (fun y hy => by
        rw [Module.Basis.baseChange_repr_tmul, b.repr_self,
          Finsupp.single_eq_of_ne (show y ≠ x from fun hxy => hy (by rw [hxy]))]
        simp [Algebra.smul_def]),
    smul_tmul', smul_eq_mul]

end Pointwise

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

omit [Module ℚ V] in
/-- Naturality of the torus in the value ring, on a base-changed basis vector. -/
theorem map_kostantTorusPoints_tmul_basis (φ : A →+* B) (s : κ → Aˣ)
    (a : A) (x : η) :
    TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id
        ((kostantTorusPoints M b wt A s).val (a ⊗ₜ[ℤ] b x)) =
      (kostantTorusPoints M b wt B fun j => Units.map (φ : A →* B) (s j)).val
        (TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id (a ⊗ₜ[ℤ] b x)) := by
  rw [kostantTorusPoints_tmul_basis, TensorProduct.map_tmul, TensorProduct.map_tmul]
  simp only [LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_apply,
    map_mul, kostantTorusPoints_tmul_basis]
  rw [← map_torusCharacter φ s (wt x)]
  simp

omit [Module ℚ V] in
/-- The torus on points is natural in the value ring. -/
theorem map_kostantTorusPoints (φ : A →+* B) (s : κ → Aˣ) (z : A ⊗[ℤ] M) :
    TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id
        ((kostantTorusPoints M b wt A s).val z) =
      (kostantTorusPoints M b wt B fun j => Units.map (φ : A →* B) (s j)).val
        (TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id z) := by
  -- Both sides are additive, so it suffices to treat a pure tensor, and then to expand its
  -- second factor in the basis.
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a m =>
      conv_lhs => rw [← b.linearCombination_repr m]
      conv_rhs => rw [← b.linearCombination_repr m]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [TensorProduct.tmul_smul, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
        map_kostantTorusPoints_tmul_basis]

end Naturality

section CommAlgCatNaturality

variable {A B : CommAlgCat.{w} ℤ}

omit [Module ℚ V] in
/-- **Scalar extension of a torus point.** Extending the scalars of the torus point `s` along a
morphism of value rings gives the torus point whose parameter is mapped into the target ring. -/
theorem mapScalarExtensionAutomorphisms_kostantTorusPoints (φ : A ⟶ B) (s : κ → Aˣ) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ (kostantTorusPoints M b wt A s) =
      kostantTorusPoints M b wt B fun j => Units.map φ.hom.toRingHom.toMonoidHom (s j) := by
  refine Units.ext (Module.Basis.ext (b.baseChange B) fun x => ?_)
  have hchar := congrArg Units.val (map_torusCharacter φ.hom.toRingHom s (wt x))
  simp only [Units.coe_map, MonoidHom.coe_coe] at hchar
  rw [Module.Basis.baseChange_apply, GeneralLinear.mapScalarExtensionAutomorphisms_tmul,
    kostantTorusPoints_tmul_basis, kostantTorusPoints_tmul_basis, one_smul,
    GeneralLinear.scalarExtensionMap_tmul, map_mul]
  simp only [map_one, mul_one]
  exact congrArg (· ⊗ₜ[ℤ] (b x : M)) hchar

end CommAlgCatNaturality

end Torus

/-! ## Matrix coordinates -/

section Matrix

variable [Fintype κ] {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)
variable {A : Type*} [CommRing A] [Algebra ℤ A]

omit [Module ℚ V] in
/-- The torus attached to a weight basis, in the matrix coordinates of that basis. -/
noncomputable def kostantTorusMatrix :
    (κ → Aˣ) →* Matrix.GeneralLinearGroup (Fin n) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (kostantTorusPoints M b wt A)

omit [Module ℚ V] in
/-- Writing a Kostant torus point in the chosen basis gives `kostantTorusMatrix`. -/
@[simp]
theorem basisMatrix_kostantTorusPoints (s : κ → Aˣ) :
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (kostantTorusPoints M b wt A s) =
      kostantTorusMatrix M b wt s := by
  rw [kostantTorusMatrix, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe]

omit [Module ℚ V] in
private theorem kostantTorusMatrix_coe (s : κ → Aˣ) :
    (kostantTorusMatrix M b wt s : Matrix (Fin n) (Fin n) A) =
      LinearMap.toMatrix (b.baseChange A) (b.baseChange A)
        (kostantTorusPoints M b wt A s).toLinearEquiv.toLinearMap :=
  rfl

omit [Module ℚ V] in
/-- In a weight basis, a torus point is the diagonal matrix of its weight characters. -/
@[simp]
theorem kostantTorusMatrix_apply (s : κ → Aˣ) :
    kostantTorusMatrix M b wt s =
      diagGL fun i => torusCharacter s (wt i) := by
  apply Units.ext
  rw [kostantTorusMatrix_coe]
  have hlinear := congrArg LinearEquiv.toLinearMap
    (kostantTorusPoints_toLinearEquiv M b wt s)
  rw [hlinear, basisWeightTorus_apply, toMatrix_basisDiagonal, diagGL_coe]

end Matrix

/-! ## The pinning equation -/

section Pinning

variable [Fintype κ] {A : Type*} [CommRing A] [Algebra ℤ A]

/-- **The pinning equation for the torus and a root subgroup.** If the designated root vector `eᵢ`
has weight `α`, then the torus point `s` conjugates the root-subgroup element with parameter `u`
into the one with parameter `α(s) u`. -/
theorem kostantTorusPoints_mul_kostantRootSubgroupPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (s : κ → Aˣ) (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hg : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) =
      (torusCharacter s α : A) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f)) :
    kostantTorusPoints M b wt A s * kostantRootSubgroupPoints e h ρ M hM i hnil f =
      kostantRootSubgroupPoints e h ρ M hM i hnil g * kostantTorusPoints M b wt A s := by
  refine Units.ext (Module.Basis.ext (b.baseChange A) fun x => ?_)
  simp only [Units.val_mul, Module.End.mul_apply, Module.Basis.baseChange_apply,
    kostantRootSubgroupPoints_tmul, kostantTorusPoints_tmul_basis, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hw : IsCartanWeightVector h ρ (wt x + n • α)
      ((integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
          (b x) : M) : V) := by
    rw [coe_integralDividedPower_apply]
    exact IsCartanWeightVector.integralDividedPower e hα (hwt x) n
  rw [kostantTorusPoints_tmul_of_isCartanWeightVector e h ρ M hM b wt hwt hw, hg]
  have hchar : (torusCharacter s (wt x + n • α) : A) =
      (torusCharacter s (wt x) : A) * (torusCharacter s α : A) ^ n := by
    rw [torusCharacter_add, torusCharacter_nsmul]
    push_cast
    ring
  rw [hchar]
  ring_nf

/-! ### The pinning equation for the root vector -/

variable (i : ι) {α : κ → ℤ}

include e hM in
/-- The base-changed root operator carries a basis tensor to a tensor of weight `wt x + α`, on
which a torus point acts by the product of the two characters. This is the single basis-vector
calculation behind the two intertwining statements below. -/
private theorem kostantTorusPoints_baseChange_kostantRootOperator_tmul_basis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (s : κ → Aˣ) (a : A) (x : η) :
    (kostantTorusPoints M b wt A s).val
        ((kostantRootOperator e h ρ M hM i).baseChange A (a ⊗ₜ[ℤ] (b x : M))) =
      ((torusCharacter s α : A) * ((torusCharacter s (wt x) : A) * a)) ⊗ₜ[ℤ]
        kostantRootOperator e h ρ M hM i (b x) := by
  rw [LinearMap.baseChange_tmul,
    kostantTorusPoints_tmul_of_isCartanWeightVector e h ρ M hM b wt hwt
      (isCartanWeightVector_coe_kostantRootOperator e h ρ M hM i hα (hwt x)) s a,
    torusCharacter_add, Units.val_mul, mul_assoc,
    mul_left_comm (torusCharacter s (wt x) : A)]

include e hM in
/-- **The torus acts on the root operator through the root.** A torus point intertwines the
base-changed root operator with itself, up to the value `α(s)` of the root.

This is the infinitesimal form of the pinning equation
`kostantTorusPoints_conj_kostantRootSubgroupParam`. -/
theorem kostantTorusPoints_mul_baseChange_kostantRootOperator
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (s : κ → Aˣ) :
    (kostantTorusPoints M b wt A s).val *
        (kostantRootOperator e h ρ M hM i).baseChange A =
      (torusCharacter s α : A) •
        ((kostantRootOperator e h ρ M hM i).baseChange A *
          (kostantTorusPoints M b wt A s).val) := by
  refine (b.baseChange A).ext fun x => ?_
  rw [Module.End.mul_apply, Module.Basis.baseChange_apply,
    kostantTorusPoints_baseChange_kostantRootOperator_tmul_basis e h ρ M hM b wt i hwt hα]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, kostantTorusPoints_tmul_basis,
    LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul]

include e hM in
/-- **The pinning relation for the root vector**, in conjugated form: `t(s) X_α t(s)⁻¹` is
`α(s) X_α`. It says that the tangent vector of the root subgroup lies in the `α`-weight space of
the adjoint action of the split maximal torus. -/
theorem kostantTorusPoints_conj_kostantRootOperator
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (s : κ → Aˣ) :
    (kostantTorusPoints M b wt A s).val *
        (kostantRootOperator e h ρ M hM i).baseChange A *
        ((kostantTorusPoints M b wt A s)⁻¹).val =
      (torusCharacter s α : A) • (kostantRootOperator e h ρ M hM i).baseChange A := by
  rw [kostantTorusPoints_mul_baseChange_kostantRootOperator e h ρ M hM b wt i hwt hα s,
    smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]

end Pinning

/-! ## The torus inside the elementary group -/

section Elementary

variable [Fintype κ]

/-- **The pinning equation with the parameter read in the value ring.** Conjugation by the torus
point `s` carries the root-subgroup element `xᵢ(u)` to `xᵢ(α(s) u)`, where `α` is the weight of the
root vector `eᵢ`. -/
theorem kostantTorusPoints_conj_kostantRootSubgroupParam
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (A : CommAlgCat.{w} ℤ) (s : κ → Aˣ) (t : Multiplicative A) :
    kostantTorusPoints M b wt A s * kostantRootSubgroupParam e h ρ M hM i hnil A t *
        (kostantTorusPoints M b wt A s)⁻¹ =
      kostantRootSubgroupParam e h ρ M hM i hnil A
        (Multiplicative.ofAdd ((torusCharacter s α : A) * Multiplicative.toAdd t)) := by
  rw [mul_inv_eq_iff_eq_mul, kostantRootSubgroupParam_apply, kostantRootSubgroupParam_apply]
  refine kostantTorusPoints_mul_kostantRootSubgroupPoints e h ρ M hM b wt hwt hα hnil s _ _ ?_
  simp

include e hM in
/-- **The torus normalizes the elementary group.** Conjugation by a torus point permutes the root
subgroups, acting on the parameter of the `i`-th one through the root `α i`, so it carries the
group they generate onto itself. -/
theorem map_kostantElementarySubgroup_conj_kostantTorusPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (α : ι → κ → ℤ) (hα : ∀ i j, ⁅h j, e i⁆ = (α i j : ℚ) • e i)
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (A : CommAlgCat.{w} ℤ) (s : κ → Aˣ) :
    Subgroup.map (MulAut.conj (kostantTorusPoints M b wt A s)).toMonoidHom
        (kostantElementarySubgroup e h ρ M hM hnil A) =
      kostantElementarySubgroup e h ρ M hM hnil A := by
  have hconj : ∀ (i : ι) (t : Multiplicative A),
      (MulAut.conj (kostantTorusPoints M b wt A s)).toMonoidHom
          (kostantRootSubgroupParam e h ρ M hM i (hnil i) A t) =
        kostantRootSubgroupParam e h ρ M hM i (hnil i) A
          (Multiplicative.ofAdd ((torusCharacter s (α i) : A) * Multiplicative.toAdd t)) :=
    fun i t => kostantTorusPoints_conj_kostantRootSubgroupParam e h ρ M hM b wt hwt (hα i)
      (hnil i) A s t
  rw [kostantElementarySubgroup_eq_closure, MonoidHom.map_closure]
  congr 1
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, t, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_range] using hz
    exact Set.mem_iUnion.2 ⟨i, _, (hconj i t).symm⟩
  · intro y hy
    obtain ⟨i, t, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_range] using hy
    refine ⟨kostantRootSubgroupParam e h ρ M hM i (hnil i) A
      (Multiplicative.ofAdd ((↑(torusCharacter s (α i))⁻¹ : A) * Multiplicative.toAdd t)),
      Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩, ?_⟩
    rw [hconj i]
    congr 1
    simp only [toAdd_ofAdd, ← mul_assoc, Units.mul_inv, one_mul, ofAdd_toAdd]

end Elementary

end TauCeti.UniversalEnvelopingAlgebra
