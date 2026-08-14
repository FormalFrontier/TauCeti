/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The isometry group of a bilinear form

An endomorphism `f` of a module `M` is an *isometry* of a bilinear form `B` when
`B (f x) (f y) = B x y`. This file introduces that predicate, `TauCeti.IsFormIsometry`, and the
group it cuts out inside the linear automorphisms of `M`, `TauCeti.formIsometryGroup B`, together
with the API a consumer of the group needs: a Gram-matrix criterion, the resulting constraint
`(det f) ^ 2 = 1`, functoriality in the module and in the base ring, and stability of orthogonal
complements.

Mathlib bundles the same notion twice — as a map, `B₁ →bᵢ B₂`, and as an equivalence,
`LinearMap.BilinForm.IsometryEquiv B₁ B₂` — and both bridges are recorded here
(`TauCeti.IsFormIsometry.toIsometry`, `TauCeti.isFormIsometry_toLinearMap`, and
`TauCeti.formIsometryGroupEquivIsometryEquiv`, the last an equivalence of *types* between the
subgroup and `B.IsometryEquiv B`). What is new is the unbundled predicate, which is what lets
"preserves `B`" be a side condition on an endomorphism one already has — the hypothesis of the
automatic-invertibility theorem below, and the membership condition of a subgroup — and the group
structure, needed as soon as one wants subgroups of it, group homomorphisms into it, or a group
action, none of which a bare type of bundled equivalences provides.

Two statements are worth singling out.

* Over an integral domain, isometries of a nondegenerate form on a finite free module are
  *automatically* invertible (`TauCeti.IsFormIsometry.bijective`): preserving `B` forces
  `(det f) ^ 2 = 1`, so `det f` is a unit. For a `ℤ`-lattice this says that a form-preserving
  endomorphism of the lattice already lies in the arithmetic group `Aut(V, Q)`, which is how such
  an automorphism usually presents itself — as an integer matrix satisfying `Aᵀ * G * A = G`.
* Base change along an algebra `R → A` is a group homomorphism
  `Aut(M, B) →* Aut(A ⊗[R] M, B_A)` (`TauCeti.formIsometryGroupBaseChange`). For `R = ℤ` and
  `A = ℂ` this is the action of `Aut(V, Q)` on the complexification of the lattice, through which
  the monodromy of a variation of Hodge structure acts.

## Main definitions

* `TauCeti.IsFormIsometry`: an endomorphism preserves a bilinear form.
* `TauCeti.formIsometryGroup`: the isometry group `Aut(M, B) ≤ M ≃ₗ[R] M`.
* `TauCeti.IsFormIsometry.toLinearEquiv`: an isometry with invertible Gram determinant, as a
  linear automorphism.
* `TauCeti.formIsometryGroupBaseChange`: base change of isometries, as a group homomorphism.
* `TauCeti.formIsometryGroupCongr`: transport of the isometry group along a linear equivalence.

## Main results

* `TauCeti.isFormIsometry_iff_toMatrix`: the Gram-matrix criterion `Aᵀ * G * A = G`.
* `TauCeti.IsFormIsometry.det_sq_eq_one`: `(det f) ^ 2 = 1` for an isometry of a form whose Gram
  determinant is a non-zero-divisor.
* `TauCeti.IsFormIsometry.bijective`: over an integral domain, an isometry of a nondegenerate form
  on a finite free module is bijective.
* `TauCeti.IsFormIsometry.map_orthogonal`: a surjective isometry carries `B`-orthogonal complements
  to `B`-orthogonal complements.
-/

public section

namespace TauCeti

open Module
open LinearMap (BilinForm)
open scoped Matrix TensorProduct

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

/-- An endomorphism `f` of `M` is an *isometry* of the bilinear form `B` when it preserves `B`,
that is, when `B (f x) (f y) = B x y` for all `x` and `y`.

Specialised to a finite free `ℤ`-module `V` and an integral form `Q`, the isometries form the
arithmetic group `Aut(V, Q)`; see `TauCeti.formIsometryGroup`. -/
@[expose] def IsFormIsometry (B : BilinForm R M) (f : M →ₗ[R] M) : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

theorem isFormIsometry_iff_comp : IsFormIsometry B f ↔ B.comp f f = B :=
  ⟨fun h => LinearMap.BilinForm.ext fun x y => h x y, fun h x y =>
    LinearMap.BilinForm.congr_fun h x y⟩

theorem isFormIsometry_toLinearMap (φ : B →bᵢ B) : IsFormIsometry B φ.toLinearMap := φ.map_app

namespace IsFormIsometry

/-- An isometry, bundled as one of Mathlib's isometric maps `B →bᵢ B`. -/
@[expose] def toIsometry (hf : IsFormIsometry B f) : B →bᵢ B := ⟨f, hf⟩

@[simp]
theorem toIsometry_apply (hf : IsFormIsometry B f) (x : M) : hf.toIsometry x = f x := rfl

protected theorem id : IsFormIsometry B LinearMap.id := fun _ _ => rfl

protected theorem comp (hf : IsFormIsometry B f) (hg : IsFormIsometry B g) :
    IsFormIsometry B (f ∘ₗ g) := fun x y => (hf (g x) (g y)).trans (hg x y)

/-- An isometry of a left-separating form is injective: it cannot collapse a vector that pairs
nontrivially with something. -/
theorem injective (hB : B.SeparatingLeft) (hf : IsFormIsometry B f) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  refine hB x fun y => ?_
  rw [← hf x y, LinearMap.mem_ker.mp hx, LinearMap.map_zero₂]

/-- An isometry preserving a submodule restricts to an isometry of the restricted form. -/
theorem restrict {N : Submodule R M} (hf : IsFormIsometry B f) (hN : ∀ x ∈ N, f x ∈ N) :
    IsFormIsometry (B.restrict N) (f.restrict hN) := fun x y => hf x y

/-- An isometry maps the `B`-orthogonal complement of `N` into the `B`-orthogonal complement of
the image of `N`. -/
theorem map_orthogonal_le (hf : IsFormIsometry B f) (N : Submodule R M) :
    (B.orthogonal N).map f ≤ B.orthogonal (N.map f) := by
  rintro - ⟨x, hx, rfl⟩
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rintro - ⟨n, hn, rfl⟩
  show B (f n) (f x) = 0
  rw [hf n x]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) n hn

/-- A surjective isometry carries `B`-orthogonal complements to `B`-orthogonal complements. -/
theorem map_orthogonal (hf : IsFormIsometry B f) (hsurj : Function.Surjective f)
    (N : Submodule R M) : (B.orthogonal N).map f = B.orthogonal (N.map f) := by
  refine le_antisymm (hf.map_orthogonal_le N) fun x hx => ?_
  obtain ⟨z, rfl⟩ := hsurj x
  refine Submodule.mem_map_of_mem ?_
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  show B n z = 0
  rw [← hf n z]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ ⟨n, hn, rfl⟩

end IsFormIsometry

/-- The isometry group `Aut(M, B)` of a bilinear form `B` on `M`: the linear automorphisms of `M`
that preserve `B`.

For a finite free `ℤ`-module `V` carrying an integral form `Q` this is the arithmetic group
`Aut(V, Q)`; a variation of Hodge structure has its monodromy representation land in it, acting on
the complexification through `TauCeti.formIsometryGroupBaseChange`. -/
def formIsometryGroup (B : BilinForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {e | IsFormIsometry B (e : M →ₗ[R] M)}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => (ha (b x) (b y)).trans (hb x y)
  inv_mem' := fun {a} ha x y => by
    simpa using (ha (a.symm x) (a.symm y)).symm

@[simp]
theorem mem_formIsometryGroup_iff {e : M ≃ₗ[R] M} :
    e ∈ formIsometryGroup B ↔ ∀ x y, B (e x) (e y) = B x y := Iff.rfl

/-- An element of the isometry group carries `B`-orthogonal complements to `B`-orthogonal
complements. -/
theorem map_orthogonal_of_mem_formIsometryGroup {e : M ≃ₗ[R] M} (he : e ∈ formIsometryGroup B)
    (N : Submodule R M) :
    (B.orthogonal N).map (e : M →ₗ[R] M) = B.orthogonal (N.map (e : M →ₗ[R] M)) :=
  IsFormIsometry.map_orthogonal he e.surjective N

/-- Membership in `Aut(M, B)` is exactly Mathlib's notion of a self-isometry of `B`: the subgroup
`TauCeti.formIsometryGroup B` and the type `LinearMap.BilinForm.IsometryEquiv B B` carry the same
data, the subgroup adding the group structure. -/
def formIsometryGroupEquivIsometryEquiv (B : BilinForm R M) :
    formIsometryGroup B ≃ B.IsometryEquiv B where
  toFun e := ⟨e.1, fun x y => e.2 x y⟩
  invFun e := ⟨e.toLinearEquiv, fun x y => e.map_app y x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transporting a bilinear form along a linear equivalence transports its isometry group. -/
def formIsometryGroupCongr (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    formIsometryGroup B ≃* formIsometryGroup (LinearMap.BilinForm.congr e B) where
  toFun a := ⟨e.symm ≪≫ₗ (a : M ≃ₗ[R] M) ≪≫ₗ e, fun x y => by
    simpa using a.2 (e.symm x) (e.symm y)⟩
  invFun a := ⟨e ≪≫ₗ (a : M' ≃ₗ[R] M') ≪≫ₗ e.symm, fun x y => by
    simpa using a.2 (e x) (e y)⟩
  left_inv a := Subtype.ext (by ext x; simp)
  right_inv a := Subtype.ext (by ext x; simp)
  map_mul' a b := Subtype.ext (by ext x; simp)

/-! ### The Gram-matrix criterion -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An endomorphism is an isometry of `B` exactly when its matrix `A` in a basis `b` satisfies
`Aᵀ * G * A = G` for the Gram matrix `G` of `B` in `b`. -/
theorem isFormIsometry_iff_toMatrix (b : Basis ι R M) :
    IsFormIsometry B f ↔
      (LinearMap.toMatrix b b f)ᵀ * LinearMap.BilinForm.toMatrix b B * LinearMap.toMatrix b b f
        = LinearMap.BilinForm.toMatrix b B := by
  rw [isFormIsometry_iff_comp, ← (LinearMap.BilinForm.toMatrix b).injective.eq_iff,
    LinearMap.BilinForm.toMatrix_comp b b B f f]

namespace IsFormIsometry

/-- An isometry scales the Gram determinant by the square of its determinant — and hence, the form
being preserved, not at all. -/
theorem det_sq_mul_det_toMatrix (b : Basis ι R M) (hf : IsFormIsometry B f) :
    LinearMap.det f ^ 2 * (LinearMap.BilinForm.toMatrix b B).det =
      (LinearMap.BilinForm.toMatrix b B).det := by
  have h := congrArg Matrix.det ((isFormIsometry_iff_toMatrix b).mp hf)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at h
  rw [show LinearMap.det f ^ 2 * (LinearMap.BilinForm.toMatrix b B).det
      = LinearMap.det f * (LinearMap.BilinForm.toMatrix b B).det * LinearMap.det f from by ring]
  exact h

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor has determinant
squaring to `1`; over `ℤ` this says its determinant is `±1`. -/
theorem det_sq_eq_one (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) : LinearMap.det f ^ 2 = 1 := by
  have h : (LinearMap.det f ^ 2 - 1) * (LinearMap.BilinForm.toMatrix b B).det = 0 := by
    rw [sub_mul, one_mul, hf.det_sq_mul_det_toMatrix b, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hG).2 _ h)

theorem isUnit_det (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) : IsUnit (LinearMap.det f) :=
  IsUnit.of_mul_eq_one _ (by rw [← sq]; exact hf.det_sq_eq_one b hG)

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor is a linear
automorphism. This is how an element of `Aut(V, Q)` usually presents itself: as an endomorphism
of the lattice `V` preserving `Q`, with invertibility a consequence rather than a hypothesis. -/
noncomputable def toLinearEquiv (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) : M ≃ₗ[R] M :=
  LinearEquiv.ofIsUnitDet (v := b) (v' := b)
    (by rw [LinearMap.det_toMatrix]; exact hf.isUnit_det b hG)

@[simp]
theorem coe_toLinearEquiv (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) : (toLinearEquiv b hG hf : M →ₗ[R] M) = f :=
  LinearEquiv.coe_ofIsUnitDet _

@[simp]
theorem toLinearEquiv_apply (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) (x : M) : toLinearEquiv b hG hf x = f x :=
  congrArg (fun l : M →ₗ[R] M => l x) (coe_toLinearEquiv b hG hf)

theorem toLinearEquiv_mem_formIsometryGroup (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsFormIsometry B f) : toLinearEquiv b hG hf ∈ formIsometryGroup B := fun x y => by
  simpa using hf x y

/-- Over an integral domain, an endomorphism of a finite free module preserving a nondegenerate
bilinear form is automatically bijective. -/
theorem bijective [IsDomain R] [Module.Free R M] [Module.Finite R M] (hB : B.Nondegenerate)
    (hf : IsFormIsometry B f) : Function.Bijective f := by
  set b := Module.Free.chooseBasis R M
  have hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)
  have h := (toLinearEquiv b hG hf).bijective
  rwa [show ⇑(toLinearEquiv b hG hf) = ⇑f from funext (toLinearEquiv_apply b hG hf)] at h

end IsFormIsometry

end Matrix

/-! ### Base change -/

section BaseChange

variable (A : Type*) [CommRing A] [Algebra R A]

theorem IsFormIsometry.baseChange (hf : IsFormIsometry B f) :
    IsFormIsometry (LinearMap.BilinForm.baseChange A B) (f.baseChange A) := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul a' m' => simp [hf m m']

/-- Base change along an `R`-algebra `A` is a group homomorphism
`Aut(M, B) →* Aut(A ⊗[R] M, B_A)`. For `R = ℤ` and `A = ℂ` this is the action of the arithmetic
group `Aut(V, Q)` on the complexification of the lattice. -/
def formIsometryGroupBaseChange (B : BilinForm R M) :
    formIsometryGroup B →* formIsometryGroup (LinearMap.BilinForm.baseChange A B) where
  toFun e := ⟨LinearEquiv.baseChange R A M M (e : M ≃ₗ[R] M),
    fun x y => IsFormIsometry.baseChange A e.2 x y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [LinearEquiv.baseChange_mul])

end BaseChange

end TauCeti
