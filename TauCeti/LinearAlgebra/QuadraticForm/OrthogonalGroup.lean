/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.Reflection

/-!
# The orthogonal group of a quadratic form

Mathlib knows the orthogonal group only in matrix form: `Matrix.orthogonalGroup n R` is the group of
matrices `A` with `Aᵀ * A = 1` (`Matrix.mem_orthogonalGroup_iff'`). Such matrices preserve the
*standard* form `x ↦ ∑ i, x i ^ 2` on `n → R`, and, as soon as `2` is not a zero divisor in `R`,
they are exactly its isometries: evaluating `Q (A x) = Q x` at the basis vectors and their pairwise
sums says that `Aᵀ * A` has unit diagonal and that twice each off-diagonal entry vanishes. In
characteristic two the two notions part company, since there the standard form no longer sees the
off-diagonal entries at all. For an abstract quadratic map `Q : QuadraticMap R M N` the
corresponding group is missing, even though Mathlib does have the individual isometries as
`QuadraticMap.IsometryEquiv Q Q`: what it lacks is the observation that they form a subgroup of the
linear automorphism group `M ≃ₗ[R] M`, and hence a group to act with.

This file supplies that subgroup, together with its determinant-one subgroup and the reflections in
the hyperplanes of vectors of invertible norm. The orthogonal group is the target of the
twisted-conjugation homomorphism out of the Pin group, so it is the object the Pin/Spin double
covers are stated against, and the reflections are the generators an eventual Cartan-Dieudonné
theorem factors an orthogonal automorphism into. The structural and reflection declarations below
hold over an arbitrary commutative ring. The equal-norm dichotomy and fixed-subspace correction
assume a field in which `2` is nonzero. The characteristic restriction is not incidental: in
characteristic two `polar Q v v = 2 • Q v` vanishes, so `reflection Q v` fixes `v` instead of
negating it and is a transvection rather than a reflection in `v ^ ⊥`.

## Main definitions

* `TauCeti.QuadraticMap.orthogonalGroup Q`: the `Q`-preserving linear automorphisms of `M`, as a
  subgroup of `M ≃ₗ[R] M`.
* `TauCeti.QuadraticMap.specialOrthogonalGroup Q`: its determinant-one subgroup.
* `TauCeti.QuadraticMap.reflection Q v`: the reflection in the hyperplane orthogonal to a vector `v`
  with `Q v` invertible, built from Mathlib's `Module.reflection`.
* `TauCeti.QuadraticMap.reflectionOrthogonal Q v`: the same reflection bundled as an element of
  `orthogonalGroup Q`, so that statements about products of reflections and about the ranges of the
  Pin and Spin actions can name it. `TauCeti.QuadraticMap.reflectionOrthogonal_mul_self` and
  `TauCeti.QuadraticMap.reflectionOrthogonal_inv` are its group-level involution facts.

## Main results

* `TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup`: an orthogonal automorphism preserves
  the polarization of `Q`; it preserves the orthogonality relation as well
  (`isOrtho_iff_of_mem_orthogonalGroup`). As soon as `2` acts injectively on the target the
  converse holds, `TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar`, which is the usual
  identification of the isometries of a quadratic form with the isometries of its polar bilinear
  form. At the level of groups this is
  `TauCeti.QuadraticMap.orthogonalGroup_eq_isometryGroup_polarBilin`: `O(Q)` is the isometry group
  `TauCeti.BilinForm.isometryGroup` of `Q.polarBilin`, so the bilinear-form API applies to it.
* `TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv`: the underlying set of the orthogonal
  group is Mathlib's type of self-isometries `Q.IsometryEquiv Q`. This is the compatibility with the
  Mathlib vocabulary; the point of `orthogonalGroup` is the group structure, which
  `QuadraticMap.IsometryEquiv` does not carry.
* `TauCeti.QuadraticMap.orthogonalGroupCongr`: isometric quadratic maps have isomorphic orthogonal
  groups. Over an algebraically closed field this is what makes `O(Q)` depend only on the rank of
  `Q`.
* `TauCeti.QuadraticMap.reflection_mem_orthogonalGroup`: the reflection in a vector of invertible
  norm is orthogonal; `TauCeti.QuadraticMap.reflection_mul_self` says it is an involution, and
  `TauCeti.QuadraticMap.reflection_apply_of_isOrtho` that it fixes the orthogonal hyperplane, while
  `TauCeti.QuadraticMap.det_reflection` computes its determinant on a finite free module. These are
  the elements a Cartan-Dieudonné theorem would write an orthogonal automorphism as a product of,
  under hypotheses (a field of characteristic not two, a nondegenerate form, finite dimension)
  that are not assumed here, and the image of the Pin group's generating vectors under twisted
  conjugation.
* `TauCeti.QuadraticMap.exists_mem_subgroup_mul_eqOn_sup_span_singleton_of_reflection_mem`: a
  subgroup containing the invertible-norm reflections supplies the one-step fixed-subspace
  correction used by Cartan--Dieudonne induction.
* `TauCeti.QuadraticMap.specialOrthogonalGroup_normal`: `SO(Q)` is normal in `O(Q)`, being the
  kernel of the determinant restricted there.

## Implementation notes

`orthogonalGroup` is defined for a `QuadraticMap R M N` valued in an arbitrary module `N`, since
preserving `Q` makes sense at that generality. The file is therefore laid out by hypothesis
strength: the group itself, its identification with `IsometryEquiv`, and its transport along an
isometric equivalence need only a `CommSemiring` and additive monoids; the polarization needs
subtraction in `M` and `N`, since `QuadraticMap.polar` is stated for `[AddCommGroup M]
[AddCommGroup N]`, but still no more than a `CommSemiring`; the determinant needs `M` to be an
additive group over a `CommRing`, and the
reflections need to divide by `Q v` and so are stated for a `QuadraticForm R M`, that is, for
`N = R`. The fixed-subspace correction assumes a field and `2 ≠ 0`; the closing
Cartan--Dieudonne dichotomy assumes a field, a nonzero common quadratic value, and `2 ≠ 0`.

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

section CommSemiring

variable {R : Type u} {M : Type v} {N : Type w} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The orthogonal group of a quadratic map: the linear automorphisms of `M` that preserve `Q`.

Mathlib's `Matrix.orthogonalGroup n R` is a coordinate version of this for the standard form on
`n → R`: its matrices preserve `x ↦ ∑ i, x i ^ 2`, and are all of its isometries as soon as `2` is
not a zero divisor in `R`. `QuadraticMap.IsometryEquiv Q Q` is the same underlying set as
`orthogonalGroup Q` (see `orthogonalGroupEquivIsometryEquiv`) but carries no group structure. -/
def orthogonalGroup (Q : QuadraticMap R M N) : Subgroup (M ≃ₗ[R] M) where
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

/-- The defining property of an orthogonal automorphism, in the form in which it rewrites.

This is deliberately not a `simp` lemma: its left-hand side `Q (f m)` matches every application
of every quadratic map to every linear equivalence, and discharging the side goal
`f ∈ orthogonalGroup Q` unfolds through `mem_orthogonalGroup_iff` to `∀ m, Q (f m) = Q m`, which
this lemma applies to again. Name it explicitly in the `simp` calls that want it. -/
theorem map_app_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (m : M) :
    Q (f m) = Q m := hf m

/-- An orthogonal automorphism preserves orthogonality of vectors. -/
@[simp]
theorem isOrtho_iff_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (x y : M) :
    Q.IsOrtho (f x) (f y) ↔ Q.IsOrtho x y := by
  simp only [isOrtho_def, ← map_add, map_app_of_mem_orthogonalGroup hf]

/-- The orthogonal group of `Q`, as a set, is Mathlib's type of self-isometries of `Q`. The content
of `orthogonalGroup` is the group structure, which `QuadraticMap.IsometryEquiv` does not carry. -/
def orthogonalGroupEquivIsometryEquiv (Q : QuadraticMap R M N) :
    orthogonalGroup Q ≃ Q.IsometryEquiv Q where
  toFun f := { (f : M ≃ₗ[R] M) with map_app' := mem_orthogonalGroup_iff.mp f.2 }
  invFun e := ⟨(e : M ≃ₗ[R] M), mem_orthogonalGroup_iff.mpr e.map_app⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_orthogonalGroupEquivIsometryEquiv (Q : QuadraticMap R M N) (f : orthogonalGroup Q) :
    ⇑(orthogonalGroupEquivIsometryEquiv Q f) = ⇑(f : M ≃ₗ[R] M) := by
  simp only [orthogonalGroupEquivIsometryEquiv]
  rfl

@[simp]
theorem coe_orthogonalGroupEquivIsometryEquiv_symm (Q : QuadraticMap R M N)
    (e : Q.IsometryEquiv Q) :
    (((orthogonalGroupEquivIsometryEquiv Q).symm e : M ≃ₗ[R] M) : M → M) = ⇑e := by
  simp [orthogonalGroupEquivIsometryEquiv]

section Congr

variable {M₁ : Type*} {M₂ : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}

/-- Conjugation by an isometric equivalence carries `O(Q₁)` onto `O(Q₂)`. -/
private theorem map_orthogonalGroup (e : Q₁.IsometryEquiv Q₂) :
    (orthogonalGroup Q₁).map (LinearEquiv.congrAut e.toLinearEquiv : _ →* _)
      = orthogonalGroup Q₂ := by
  have key : ∀ x : M₁, Q₂ (e.toLinearEquiv x) = Q₁ x := e.map_app
  have key' : ∀ x : M₂, Q₁ (e.toLinearEquiv.symm x) = Q₂ x := fun x => by
    rw [← key (e.toLinearEquiv.symm x), e.toLinearEquiv.apply_symm_apply]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.coe_coe, mem_orthogonalGroup_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩ m
    rw [LinearEquiv.congrAut_apply, key, hf, key']
  · refine fun hg => ⟨(LinearEquiv.congrAut e.toLinearEquiv).symm g, fun m => ?_,
      (LinearEquiv.congrAut e.toLinearEquiv).apply_symm_apply g⟩
    rw [LinearEquiv.congrAut_symm_apply, key', hg, key]

/-- Isometric quadratic maps have isomorphic orthogonal groups: conjugation by an isometric
equivalence `e : Q₁ ≃qᵢ Q₂` carries `O(Q₁)` onto `O(Q₂)`.

Over an algebraically closed field every nondegenerate quadratic form of a given rank is isometric
to every other, so this is what makes `O(Q)` depend on the rank alone. -/
def orthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) :
    orthogonalGroup Q₁ ≃* orthogonalGroup Q₂ :=
  ((LinearEquiv.congrAut e.toLinearEquiv).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_orthogonalGroup e))

@[simp]
theorem coe_orthogonalGroupCongr_apply (e : Q₁.IsometryEquiv Q₂) (f : orthogonalGroup Q₁) (m : M₂) :
    (orthogonalGroupCongr e f : M₂ ≃ₗ[R] M₂) m
      = e.toLinearEquiv ((f : M₁ ≃ₗ[R] M₁) (e.toLinearEquiv.symm m)) := by
  simp [orthogonalGroupCongr, LinearEquiv.congrAut_apply]

@[simp]
theorem coe_orthogonalGroupCongr_symm_apply (e : Q₁.IsometryEquiv Q₂) (g : orthogonalGroup Q₂)
    (m : M₁) : ((orthogonalGroupCongr e).symm g : M₁ ≃ₗ[R] M₁) m
      = e.toLinearEquiv.symm ((g : M₂ ≃ₗ[R] M₂) (e.toLinearEquiv m)) := by
  simp [orthogonalGroupCongr, LinearEquiv.congrAut_symm_apply]

end Congr

end CommSemiring

section Polar

variable {R : Type u} {M : Type v} {N : Type w} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {Q : QuadraticMap R M N}

/-- An orthogonal automorphism preserves the polarization of `Q`, because the polarization is
built from `Q` and the additive structure alone. -/
@[simp]
theorem polar_apply_of_mem_orthogonalGroup {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) (x y : M) :
    polar Q (f x) (f y) = polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, map_app_of_mem_orthogonalGroup hf]

/-- As soon as `2` acts injectively on the target, preserving the polarization is the same as
preserving the quadratic map: an automorphism is orthogonal exactly when it is an isometry of the
polar bilinear form.

Only injectivity is needed, not invertibility of `2`, so this covers integral forms as well: over
`ℤ`, or more generally whenever `N` is `2`-torsion-free, `2` is not a unit but the polarization
still determines `Q`. When `2` is invertible in `R` the hypothesis is
`(isUnit_of_invertible (2 : R)).isSMulRegular N`. Some such hypothesis is needed: in characteristic
two the polarization forgets `Q` entirely on the diagonal. -/
theorem mem_orthogonalGroup_iff_polar (h2 : IsSMulRegular N (2 : R)) {f : M ≃ₗ[R] M} :
    f ∈ orthogonalGroup Q ↔ ∀ x y, polar Q (f x) (f y) = polar Q x y := by
  refine ⟨polar_apply_of_mem_orthogonalGroup, fun h m => ?_⟩
  -- Mathlib's `polar_self` is stated over a `CommRing`; the diagonal identity itself needs only
  -- `QuadraticMap.map_add_self`, which holds over a `CommSemiring`.
  have key : ∀ x : M, (2 : R) • Q x = polar Q x x := fun x => by
    rw [two_smul]
    simp only [QuadraticMap.polar, QuadraticMap.map_add_self]
    abel
  exact h2 ((key (f m)).trans ((h m m).trans (key m).symm))

end Polar

section PolarBilin

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The orthogonal group of a quadratic form is the isometry group of its polar bilinear form, as
soon as `2` is a regular scalar: `orthogonalGroup Q` and `TauCeti.BilinForm.isometryGroup
Q.polarBilin` are then two names for the same subgroup of `M ≃ₗ[R] M`, and the bilinear-form API —
the Gram-matrix criterion, `det ^ 2 = 1`, base change — applies to `O(Q)` through it. Some such
hypothesis is needed: in characteristic two the polarization forgets `Q` on the diagonal. -/
theorem orthogonalGroup_eq_isometryGroup_polarBilin (h2 : IsSMulRegular R (2 : R))
    (Q : QuadraticForm R M) : orthogonalGroup Q = BilinForm.isometryGroup Q.polarBilin := by
  ext f
  simp only [mem_orthogonalGroup_iff_polar h2, BilinForm.mem_isometryGroup_iff,
    QuadraticMap.polarBilin_apply_apply]

end PolarBilin

section Det

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The special orthogonal group: the orthogonal automorphisms of determinant one.

The determinant is Mathlib's `LinearEquiv.det`, which is `1` by convention on a module that is not
finite free; on such a module this subgroup is therefore all of `orthogonalGroup Q`. -/
noncomputable def specialOrthogonalGroup (Q : QuadraticMap R M N) :
    Subgroup (M ≃ₗ[R] M) :=
  orthogonalGroup Q ⊓ (LinearEquiv.det (R := R) (M := M)).ker

variable {Q : QuadraticMap R M N}

@[simp]
theorem mem_specialOrthogonalGroup_iff {f : M ≃ₗ[R] M} :
    f ∈ specialOrthogonalGroup Q ↔ f ∈ orthogonalGroup Q ∧ LinearEquiv.det f = 1 := Iff.rfl

theorem specialOrthogonalGroup_le_orthogonalGroup (Q : QuadraticMap R M N) :
    specialOrthogonalGroup Q ≤ orthogonalGroup Q := inf_le_left

/-- `SO(Q)` is normal in `O(Q)`: inside the orthogonal group it is the kernel of the determinant. -/
instance specialOrthogonalGroup_normal (Q : QuadraticMap R M N) :
    ((specialOrthogonalGroup Q).subgroupOf (orthogonalGroup Q)).Normal := by
  rw [specialOrthogonalGroup, Subgroup.inf_subgroupOf_left]
  infer_instance

end Det

section Reflection

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) (v : M) [Invertible (Q v)]

/-- The linear functional `y ↦ polar Q v y / Q v` cutting out the hyperplane fixed by the reflection
in `v`. It is normalized so that it takes the value `2` at `v`, which is Mathlib's convention for
`Module.reflection`. -/
private def reflectionDual : Module.Dual R M := ⅟(Q v) • Q.polarBilin v

private theorem reflectionDual_apply (y : M) :
    reflectionDual Q v y = ⅟(Q v) * polar Q v y := by
  simp [reflectionDual]

private theorem reflectionDual_apply_self : reflectionDual Q v v = 2 := by
  rw [reflectionDual_apply, polar_self, two_nsmul, ← two_mul, ← mul_assoc, mul_right_comm,
    invOf_mul_self, one_mul]

/-- The reflection of `M` in the hyperplane orthogonal to a vector `v` of invertible norm:
`y ↦ y - (polar Q v y / Q v) • v`. This is Mathlib's `Module.reflection` for the functional
`y ↦ polar Q v y / Q v`. -/
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

/-- A reflection is its own inverse. -/
@[simp]
theorem reflection_inv : (reflection Q v)⁻¹ = reflection Q v :=
  Module.reflection_inv _

/-- A reflection is its own inverse, as a linear equivalence. -/
@[simp]
theorem reflection_symm : (reflection Q v).symm = reflection Q v :=
  Module.reflection_symm _

/-- The determinant of a reflection is `-1` on a finite free module. -/
@[simp]
theorem det_reflection [Module.Free R M] [Module.Finite R M] :
    LinearEquiv.det (reflection Q v) = (-1 : Rˣ) := by
  exact Module.det_reflection (reflectionDual_apply_self Q v)

/-- **Reflections are orthogonal.** These are the generators a Cartan-Dieudonné theorem writes an
orthogonal automorphism as a product of, over a field of characteristic not two, for a nondegenerate
form, in finite dimension; none of that is assumed here. In characteristic two `polar Q v v` is
`2 • Q v = 0`, so `reflection Q v` fixes `v` rather than negating it and is a transvection, which is
why that theorem excludes characteristic two. They are also the image of the generating vectors of
the Pin group under twisted conjugation. -/
theorem reflection_mem_orthogonalGroup : reflection Q v ∈ orthogonalGroup Q := by
  intro y
  rw [reflection_apply]
  set c : R := ⅟(Q v) * polar Q v y with hc
  have hcv : c * Q v = polar Q v y := by
    rw [hc, mul_comm (⅟(Q v)) (polar Q v y), mul_assoc, invOf_mul_self, mul_one]
  have hexp : Q (y - c • v) = Q y + c * (c * Q v) - c * polar Q v y := by
    rw [sub_eq_add_neg, QuadraticMap.map_add ⇑Q, QuadraticMap.map_neg, QuadraticMap.map_smul,
      polar_neg_right, polar_smul_right, QuadraticMap.polar_comm ⇑Q y v, smul_eq_mul, smul_eq_mul]
    ring
  rw [hexp, hcv, add_sub_cancel_right]

/-- The reflection in a vector of invertible norm, as an element of the orthogonal group.

`reflection_mem_orthogonalGroup` gives the membership; this bundles it, so that statements about
reflections inside `orthogonalGroup Q` — products of reflections, membership in the range of the
Pin and Spin actions, generation results — can name the group element instead of repeating the
anonymous constructor. -/
noncomputable def reflectionOrthogonal : orthogonalGroup Q :=
  ⟨reflection Q v, reflection_mem_orthogonalGroup Q v⟩

@[simp]
theorem coe_reflectionOrthogonal :
    (reflectionOrthogonal Q v : M ≃ₗ[R] M) = reflection Q v := by
  simp only [reflectionOrthogonal]

/-- The bundled reflection is an involution, so it has order dividing two in the orthogonal
group. -/
@[simp]
theorem reflectionOrthogonal_mul_self :
    reflectionOrthogonal Q v * reflectionOrthogonal Q v = 1 :=
  Subtype.ext <| by
    simp only [Subgroup.coe_mul, coe_reflectionOrthogonal, Subgroup.coe_one, reflection_mul_self]

/-- The bundled reflection is its own inverse in the orthogonal group. -/
@[simp]
theorem reflectionOrthogonal_inv :
    (reflectionOrthogonal Q v)⁻¹ = reflectionOrthogonal Q v :=
  inv_eq_of_mul_eq_one_left (reflectionOrthogonal_mul_self Q v)

end Reflection

section CartanDieudonneStep

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- If `x` and `y` have the same quadratic value, reflecting `x` in `x - y` carries it to `y`
whenever `x - y` has invertible norm. -/
theorem reflection_sub_apply_eq_of_map_eq (x y : M) (hxy : Q x = Q y)
    [Invertible (Q (x - y))] :
    reflection Q (x - y) x = y := by
  rw [reflection_apply]
  have hpolar : polar Q (x - y) x = Q (x - y) := by
    calc
      _ = (2 : R) * Q x - polar Q y x := by
        rw [polar_sub_left, polar_self]
        ring
      _ = Q (x - y) := by
        conv_rhs =>
          rw [sub_eq_add_neg, QuadraticMap.map_add ⇑Q, QuadraticMap.map_neg, polar_neg_right]
        rw [hxy, QuadraticMap.polar_comm ⇑Q y x]
        ring
  rw [hpolar, invOf_mul_self, one_smul, sub_sub_cancel]

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) [NeZero (2 : K)]

/-- If `x` and `y` have the same nonzero quadratic value, at least one of `x - y` and `x + y`
has nonzero, hence invertible, norm. -/
theorem isUnit_sub_or_add_of_map_eq (x y : V) (hxy : Q x = Q y) (hy : Q y ≠ 0) :
    IsUnit (Q (x - y)) ∨ IsUnit (Q (x + y)) := by
  rw [isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  by_cases hsub : Q (x - y) = 0
  · right
    intro hadd
    have hsum : Q (x - y) + Q (x + y) = 4 * Q y := by
      rw [sub_eq_add_neg, QuadraticMap.map_add ⇑Q, QuadraticMap.map_neg, polar_neg_right,
        QuadraticMap.map_add ⇑Q, hxy]
      ring
    have hzero : (4 : K) * Q y = 0 := by simpa [hsub, hadd] using hsum.symm
    have h4 : (4 : K) ≠ 0 := by
      simpa only [show (4 : K) = 2 * 2 by norm_num] using
        mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
    exact hy ((mul_eq_zero.mp hzero).resolve_left h4)
  · exact Or.inl hsub

end Field

section FixedSubspace

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) [NeZero (2 : K)]

omit [NeZero (2 : K)] in
private theorem linearEquiv_eqOn_sup_span_singleton
    (f : V ≃ₗ[K] V) (W : Submodule K V) (x : V)
    (hW : ∀ w ∈ W, f w = w) (hx : f x = x) :
    ∀ y ∈ W ⊔ Submodule.span K {x}, f y = y := by
  apply LinearMap.eqOn_sup (f := f) (g := LinearEquiv.refl K V)
  · intro w hw
    simpa only [LinearEquiv.refl_apply] using hW w hw
  · apply LinearMap.eqOn_span'
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    -- Remove the identity-equivalence coercion introduced by `eqOn_span'`.
    change f x = x
    exact hx

/-- Let `H` be a subgroup of the orthogonal group containing every reflection in a vector of
invertible norm. If `g` fixes a subspace `W` pointwise and `x` is anisotropic and orthogonal to
`W`, an element of `H` can be multiplied into `g` so that the product fixes
`W ⊔ K ∙ x` pointwise. -/
theorem exists_mem_subgroup_mul_eqOn_sup_span_singleton_of_reflection_mem
    (H : Subgroup (QuadraticMap.orthogonalGroup Q))
    (hreflection : ∀ (v : V) [Invertible (Q v)],
      QuadraticMap.reflectionOrthogonal Q v ∈ H)
    (g : QuadraticMap.orthogonalGroup Q) (W : Submodule K V)
    (hfix : ∀ w ∈ W, ((g : V ≃ₗ[K] V) w) = w)
    (x : V) [Invertible (Q x)]
    (hx : ∀ w ∈ W, Q.IsOrtho x w) :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ H ∧
      ∀ y ∈ W ⊔ Submodule.span K {x},
        (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) y) = y := by
  have hmap : Q ((g : V ≃ₗ[K] V) x) = Q x :=
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2 x
  have hgx : ∀ w ∈ W, Q.IsOrtho ((g : V ≃ₗ[K] V) x) w := by
    intro w hw
    rw [← hfix w hw]
    exact (QuadraticMap.isOrtho_iff_of_mem_orthogonalGroup g.2 x w).mpr (hx w hw)
  have hsub : ∀ w ∈ W, Q.IsOrtho ((g : V ≃ₗ[K] V) x - x) w := by
    intro w hw
    apply QuadraticMap.isOrtho_polarBilin.mp
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left,
      (hgx w hw).polar_eq_zero, (hx w hw).polar_eq_zero, sub_self]
  have hadd : ∀ w ∈ W, Q.IsOrtho ((g : V ≃ₗ[K] V) x + x) w := by
    intro w hw
    apply QuadraticMap.isOrtho_polarBilin.mp
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_left,
      (hgx w hw).polar_eq_zero, (hx w hw).polar_eq_zero, add_zero]
  rcases QuadraticMap.isUnit_sub_or_add_of_map_eq Q _ x hmap
      (isUnit_of_invertible (Q x)).ne_zero with hsubUnit | haddUnit
  · let : Invertible (Q ((g : V ≃ₗ[K] V) x - x)) := hsubUnit.invertible
    let r : QuadraticMap.orthogonalGroup Q :=
      QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[K] V) x - x)
    refine ⟨r, hreflection _, ?_⟩
    apply linearEquiv_eqOn_sup_span_singleton _ W x
    · intro w hw
      -- Expose the reflection underlying the subgroup product before applying its pointwise API.
      change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - x)
        ((g : V ≃ₗ[K] V) w) = w
      rw [hfix w hw]
      apply QuadraticMap.reflection_apply_of_isOrtho
      exact hsub w hw
    · -- Expose the reflection underlying the subgroup product at the new generator.
      change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - x)
        ((g : V ≃ₗ[K] V) x) = x
      exact QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ x hmap
  · have : Invertible (Q ((g : V ≃ₗ[K] V) x - -x)) := by
      simpa only [sub_neg_eq_add] using haddUnit.invertible
    have hadd' : ∀ w ∈ W, Q.IsOrtho ((g : V ≃ₗ[K] V) x - -x) w := by
      simpa only [sub_neg_eq_add] using hadd
    let r₁ : QuadraticMap.orthogonalGroup Q :=
      QuadraticMap.reflectionOrthogonal Q x
    let r₂ : QuadraticMap.orthogonalGroup Q :=
      QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[K] V) x - -x)
    refine ⟨r₁ * r₂, H.mul_mem (hreflection x) (hreflection _), ?_⟩
    apply linearEquiv_eqOn_sup_span_singleton _ W x
    · intro w hw
      -- Expose the two reflections underlying the subgroup product.
      change QuadraticMap.reflection Q x
        (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x)
          ((g : V ≃ₗ[K] V) w)) = w
      rw [hfix w hw]
      have hfix₂ : QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x) w = w :=
        QuadraticMap.reflection_apply_of_isOrtho Q _
        (hadd' w hw)
      rw [hfix₂]
      exact QuadraticMap.reflection_apply_of_isOrtho Q _
        (hx w hw)
    · -- Expose the two reflections underlying the subgroup product at the new generator.
      change QuadraticMap.reflection Q x
        (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x)
          ((g : V ≃ₗ[K] V) x)) = x
      rw [QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ (-x)
        (hmap.trans (Q.map_neg x).symm), map_neg, QuadraticMap.reflection_apply_self, neg_neg]

end FixedSubspace

end CartanDieudonneStep

end QuadraticMap

end TauCeti
