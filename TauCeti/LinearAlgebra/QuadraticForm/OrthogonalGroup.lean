/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Reflection

/-!
# The orthogonal group of a quadratic form

Mathlib knows the orthogonal group only in matrix form: `Matrix.orthogonalGroup n R` is the group of
matrices `A` with `Aᵀ * A = 1` (`Matrix.mem_orthogonalGroup_iff'`), that is, the isometry group of
the *standard* form `x ↦ ∑ i, x i ^ 2` on `n → R`. For an abstract quadratic map
`Q : QuadraticMap R M N` the
corresponding group is missing, even though Mathlib does have the individual isometries as
`QuadraticMap.IsometryEquiv Q Q`: what it lacks is the observation that they form a subgroup of the
linear automorphism group `M ≃ₗ[R] M`, and hence a group to act with.

This file supplies that subgroup, together with its determinant-one subgroup and the reflections in
the hyperplanes of vectors of invertible norm. The orthogonal group is the target of the
twisted-conjugation homomorphism out of the Pin group, so it is the object the Pin/Spin double
covers are stated against, and the reflections are what Cartan-Dieudonné factors its elements into.

## Main definitions

* `TauCeti.QuadraticMap.orthogonalGroup Q`: the `Q`-preserving linear automorphisms of `M`, as a
  subgroup of `M ≃ₗ[R] M`.
* `TauCeti.QuadraticMap.specialOrthogonalGroup Q`: its determinant-one subgroup.
* `TauCeti.QuadraticMap.reflection Q v`: the reflection in the hyperplane orthogonal to a vector `v`
  with `Q v` invertible, built from Mathlib's `Module.reflection`.

## Main results

* `TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup`: an orthogonal automorphism preserves
  the polarization of `Q`, and therefore (`isOrtho_iff_of_mem_orthogonalGroup`) the orthogonality
  relation. In characteristic not two the converse holds as well,
  `TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar`, which is the usual identification of the
  isometries of a quadratic form with the isometries of its polar bilinear form.
* `TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv`: the underlying set of the orthogonal
  group is Mathlib's type of self-isometries `Q.IsometryEquiv Q`. This is the compatibility with the
  Mathlib vocabulary; the point of `orthogonalGroup` is the group structure, which
  `QuadraticMap.IsometryEquiv` does not carry.
* `TauCeti.QuadraticMap.orthogonalGroupCongr`: isometric quadratic maps have isomorphic orthogonal
  groups. Over an algebraically closed field this is what makes `O(Q)` depend only on the rank of
  `Q`.
* `TauCeti.QuadraticMap.reflection_mem_orthogonalGroup`: the reflection in a vector of invertible
  norm is orthogonal; `TauCeti.QuadraticMap.reflection_mul_self` says it is an involution, and
  `TauCeti.QuadraticMap.reflection_apply_of_isOrtho` that it fixes the orthogonal hyperplane. These
  are the elements Cartan-Dieudonné writes every orthogonal automorphism as a product of, and the
  image of the Pin group's generating vectors under twisted conjugation.
* `TauCeti.QuadraticMap.specialOrthogonalGroup_normal`: `SO(Q)` is normal in `O(Q)`, being the
  kernel of the determinant restricted there.

## Implementation notes

`orthogonalGroup` is defined for a `QuadraticMap R M N` valued in an arbitrary module `N`, since
preserving `Q` makes sense at that generality. The reflections need to divide by `Q v` and so are
stated for a `QuadraticForm R M`, that is, for `N = R`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 2, "the abstract orthogonal group".
* J.-P. Serre, *A Course in Arithmetic* (1973), Chapter IV.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

universe u v w

namespace TauCeti

namespace QuadraticMap

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The orthogonal group of a quadratic map: the linear automorphisms of `M` that preserve `Q`.

Mathlib's `Matrix.orthogonalGroup n R` is the special case of the standard form on `n → R`, written
in coordinates; `QuadraticMap.IsometryEquiv Q Q` is the same underlying set (see
`orthogonalGroupEquivIsometryEquiv`) but carries no group structure. -/
@[expose] def orthogonalGroup (Q : QuadraticMap R M N) : Subgroup (M ≃ₗ[R] M) where
  carrier := {f | ∀ m, Q (f m) = Q m}
  one_mem' _ := rfl
  mul_mem' hf hg m := (hf _).trans (hg m)
  inv_mem' {f} hf m := by
    have h := hf (f.symm m)
    rwa [f.apply_symm_apply, eq_comm] at h

variable {Q : QuadraticMap R M N}

@[simp]
theorem mem_orthogonalGroup_iff {f : M ≃ₗ[R] M} :
    f ∈ orthogonalGroup Q ↔ ∀ m, Q (f m) = Q m := Iff.rfl

/-- The defining property of an orthogonal automorphism, in the form in which it rewrites. -/
theorem map_app_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (m : M) :
    Q (f m) = Q m := hf m

/-- An orthogonal automorphism preserves the polarization of `Q`, because the polarization is
built from `Q` and the additive structure alone. -/
theorem polar_apply_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (x y : M) :
    polar Q (f x) (f y) = polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, map_app_of_mem_orthogonalGroup hf]

/-- An orthogonal automorphism preserves orthogonality of vectors. -/
theorem isOrtho_iff_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (x y : M) :
    Q.IsOrtho (f x) (f y) ↔ Q.IsOrtho x y := by
  simp only [isOrtho_def, ← map_add, map_app_of_mem_orthogonalGroup hf]

/-- In characteristic not two, preserving the polarization is the same as preserving the quadratic
map: an automorphism is orthogonal exactly when it is an isometry of the polar bilinear form.

This fails in characteristic two, where the polarization forgets `Q` entirely on the diagonal, so
the hypothesis `Invertible (2 : R)` is not an artefact of the proof. -/
theorem mem_orthogonalGroup_iff_polar [Invertible (2 : R)] {f : M ≃ₗ[R] M} :
    f ∈ orthogonalGroup Q ↔ ∀ x y, polar Q (f x) (f y) = polar Q x y := by
  refine ⟨polar_apply_of_mem_orthogonalGroup, fun h m => ?_⟩
  have key : ∀ x : M, Q x = ⅟(2 : R) • polar Q x x := fun x => by
    rw [polar_self, two_nsmul, ← two_smul R, smul_smul, invOf_mul_self, one_smul]
  rw [key (f m), key m, h]

/-- The special orthogonal group: the orthogonal automorphisms of determinant one.

The determinant is Mathlib's `LinearEquiv.det`, which is `1` by convention on a module that is not
finite free; on such a module this subgroup is therefore all of `orthogonalGroup Q`. -/
@[expose] noncomputable def specialOrthogonalGroup (Q : QuadraticMap R M N) :
    Subgroup (M ≃ₗ[R] M) :=
  orthogonalGroup Q ⊓ (LinearEquiv.det (R := R) (M := M)).ker

theorem mem_specialOrthogonalGroup_iff {f : M ≃ₗ[R] M} :
    f ∈ specialOrthogonalGroup Q ↔ f ∈ orthogonalGroup Q ∧ LinearEquiv.det f = 1 := Iff.rfl

theorem specialOrthogonalGroup_le_orthogonalGroup (Q : QuadraticMap R M N) :
    specialOrthogonalGroup Q ≤ orthogonalGroup Q := inf_le_left

/-- `SO(Q)` is normal in `O(Q)`: inside the orthogonal group it is the kernel of the determinant. -/
instance specialOrthogonalGroup_normal (Q : QuadraticMap R M N) :
    ((specialOrthogonalGroup Q).subgroupOf (orthogonalGroup Q)).Normal := by
  rw [specialOrthogonalGroup, Subgroup.inf_subgroupOf_left]
  infer_instance

/-- The orthogonal group of `Q`, as a set, is Mathlib's type of self-isometries of `Q`. The content
of `orthogonalGroup` is the group structure, which `QuadraticMap.IsometryEquiv` does not carry. -/
@[expose] def orthogonalGroupEquivIsometryEquiv (Q : QuadraticMap R M N) :
    orthogonalGroup Q ≃ Q.IsometryEquiv Q where
  toFun f := { (f : M ≃ₗ[R] M) with map_app' := mem_orthogonalGroup_iff.mp f.2 }
  invFun e := ⟨(e : M ≃ₗ[R] M), mem_orthogonalGroup_iff.mpr e.map_app⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_orthogonalGroupEquivIsometryEquiv (Q : QuadraticMap R M N) (f : orthogonalGroup Q) :
    ⇑(orthogonalGroupEquivIsometryEquiv Q f) = ⇑(f : M ≃ₗ[R] M) := rfl

@[simp]
theorem coe_orthogonalGroupEquivIsometryEquiv_symm (Q : QuadraticMap R M N)
    (e : Q.IsometryEquiv Q) :
    (((orthogonalGroupEquivIsometryEquiv Q).symm e : M ≃ₗ[R] M) : M → M) = ⇑e := rfl

section Congr

variable {M₁ : Type*} {M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}

/-- Isometric quadratic maps have isomorphic orthogonal groups: conjugation by an isometric
equivalence `e : Q₁ ≃qᵢ Q₂` carries `O(Q₁)` onto `O(Q₂)`.

Over an algebraically closed field every nondegenerate quadratic form of a given rank is isometric
to every other, so this is what makes `O(Q)` depend on the rank alone. -/
@[expose] def orthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) :
    orthogonalGroup Q₁ ≃* orthogonalGroup Q₂ where
  toFun f :=
    ⟨(e.toLinearEquiv.symm ≪≫ₗ (f : M₁ ≃ₗ[R] M₁)) ≪≫ₗ e.toLinearEquiv,
      mem_orthogonalGroup_iff.mpr fun m => by
      have h₁ : Q₁ (e.toLinearEquiv.symm m) = Q₂ m := by
        conv_rhs => rw [← e.toLinearEquiv.apply_symm_apply m]
        exact (e.map_app _).symm
      simp only [LinearEquiv.trans_apply]
      exact ((e.map_app _).trans
        (map_app_of_mem_orthogonalGroup f.2 (e.toLinearEquiv.symm m))).trans h₁⟩
  invFun g :=
    ⟨(e.toLinearEquiv ≪≫ₗ (g : M₂ ≃ₗ[R] M₂)) ≪≫ₗ e.toLinearEquiv.symm,
      mem_orthogonalGroup_iff.mpr fun m => by
      have h₁ : ∀ x : M₂, Q₁ (e.toLinearEquiv.symm x) = Q₂ x := fun x => by
        conv_rhs => rw [← e.toLinearEquiv.apply_symm_apply x]
        exact (e.map_app _).symm
      simp only [LinearEquiv.trans_apply]
      exact (h₁ _).trans
        ((map_app_of_mem_orthogonalGroup g.2 (e.toLinearEquiv m)).trans (e.map_app m))⟩
  left_inv f :=
    Subtype.ext (LinearEquiv.ext fun m => by
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply])
  right_inv g :=
    Subtype.ext (LinearEquiv.ext fun m => by
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply])
  map_mul' f g :=
    Subtype.ext (LinearEquiv.ext fun m => by
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply])

@[simp]
theorem coe_orthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) (f : orthogonalGroup Q₁) (m : M₂) :
    (orthogonalGroupCongr e f : M₂ ≃ₗ[R] M₂) m
      = e.toLinearEquiv ((f : M₁ ≃ₗ[R] M₁) (e.toLinearEquiv.symm m)) := rfl

end Congr

section Reflection

variable (Q : QuadraticForm R M) (v : M) [Invertible (Q v)]

/-- The linear functional `y ↦ polar Q v y / Q v` cutting out the hyperplane fixed by the reflection
in `v`. It is normalized so that it takes the value `2` at `v`, which is Mathlib's convention for
`Module.reflection`. -/
def reflectionDual : Module.Dual R M := ⅟(Q v) • Q.polarBilin v

theorem reflectionDual_apply (y : M) : reflectionDual Q v y = ⅟(Q v) * polar Q v y := by
  simp [reflectionDual]

@[simp]
theorem reflectionDual_apply_self : reflectionDual Q v v = 2 := by
  rw [reflectionDual_apply, polar_self, two_nsmul, ← two_mul, ← mul_assoc, mul_right_comm,
    invOf_mul_self, one_mul]

/-- The reflection of `M` in the hyperplane orthogonal to a vector `v` of invertible norm:
`y ↦ y - (polar Q v y / Q v) • v`. This is Mathlib's `Module.reflection` for the functional
`reflectionDual Q v`. -/
noncomputable def reflection : M ≃ₗ[R] M :=
  Module.reflection (reflectionDual_apply_self Q v)

theorem reflection_apply (y : M) :
    reflection Q v y = y - (⅟(Q v) * polar Q v y) • v := by
  rw [reflection, Module.reflection_apply, reflectionDual_apply]

@[simp]
theorem reflection_apply_self : reflection Q v v = -v :=
  Module.reflection_apply_self _

/-- The reflection in `v` fixes the hyperplane cut out by `polar Q v`. -/
theorem reflection_apply_of_polar_eq_zero {y : M} (hy : polar Q v y = 0) :
    reflection Q v y = y := by
  rw [reflection_apply, hy, mul_zero, zero_smul, sub_zero]

/-- The reflection in `v` fixes every vector orthogonal to `v`. Together with
`reflection_apply_self` this says it is the reflection in the hyperplane `v ^ ⊥`. -/
theorem reflection_apply_of_isOrtho {y : M} (hy : Q.IsOrtho v y) : reflection Q v y = y :=
  reflection_apply_of_polar_eq_zero Q v hy.polar_eq_zero

/-- A reflection is an involution, so it has order dividing two in the orthogonal group. -/
theorem reflection_mul_self : reflection Q v * reflection Q v = 1 :=
  LinearEquiv.ext fun y => Module.involutive_reflection _ y

/-- **Reflections are orthogonal.** Cartan-Dieudonné writes every orthogonal automorphism of a
nondegenerate form as a product of these, and they are the image of the generating vectors of the
Pin group under twisted conjugation. -/
theorem reflection_mem_orthogonalGroup : reflection Q v ∈ orthogonalGroup Q := by
  have hadd : ∀ a b : M, Q (a + b) = Q a + Q b + polar Q a b := fun a b => by
    simp only [QuadraticMap.polar]; ring
  intro y
  rw [reflection_apply]
  set c : R := ⅟(Q v) * polar Q v y with hc
  have hcv : c * Q v = polar Q v y := by
    rw [hc, mul_comm (⅟(Q v)) (polar Q v y), mul_assoc, invOf_mul_self, mul_one]
  have hexp : Q (y - c • v) = Q y + c * (c * Q v) - c * polar Q v y := by
    rw [sub_eq_add_neg, hadd, QuadraticMap.map_neg, QuadraticMap.map_smul, polar_neg_right,
      polar_smul_right, QuadraticMap.polar_comm ⇑Q y v, smul_eq_mul, smul_eq_mul]
    ring
  rw [hexp, hcv, add_sub_cancel_right]

end Reflection

end QuadraticMap

end TauCeti
