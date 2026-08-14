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
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Congr

/-!
# The isometry group of a bilinear form

An endomorphism `f` of a module `M` is an *isometry* of a bilinear form `B` when
`B (f x) (f y) = B x y`. Starting from the predicate `TauCeti.BilinForm.IsIsometry` defined in the
dependency-light module `TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic`, this file builds the
group it cuts out inside the linear automorphisms of `M`, `TauCeti.BilinForm.isometryGroup B`,
together with the API a consumer of the group needs: a Gram-matrix criterion, the resulting
constraint `(det f) ^ 2 = 1`, functoriality in the module and in the base ring, and stability of
orthogonal complements.

Mathlib bundles the same notion twice — as a map, `B₁ →bᵢ B₂`, and as an equivalence,
`LinearMap.BilinForm.IsometryEquiv B₁ B₂` — and both bridges are recorded here
(`TauCeti.BilinForm.IsIsometry.toIsometry`, `TauCeti.BilinForm.isIsometry_toLinearMap`, and
`TauCeti.BilinForm.isometryGroupEquivIsometryEquiv`, the last an equivalence of *types* between the
subgroup and `B.IsometryEquiv B`). What is new is the unbundled predicate, which is what lets
"preserves `B`" be a side condition on an endomorphism one already has — the hypothesis of the
automatic-invertibility theorem below, and the membership condition of a subgroup — and the group
structure, needed as soon as one wants subgroups of it, group homomorphisms into it, or a group
action, none of which a bare type of bundled equivalences provides.

Two statements are worth singling out.

* Over an integral domain, isometries of a left-separating form on a finite free module are
  *automatically* invertible, so they already form elements of the group
  (`TauCeti.BilinForm.IsIsometry.toIsometryGroup`, `TauCeti.BilinForm.IsIsometry.bijective`):
  preserving `B` forces `(det f) ^ 2 = 1`, so `det f` is a unit. For a `ℤ`-lattice this says that a
  form-preserving endomorphism of the lattice already lies in the arithmetic group `Aut(V, Q)`,
  which is how such an automorphism usually presents itself — as an integer matrix satisfying
  `Aᵀ * G * A = G`.
* Base change along an algebra `R → A` is a group homomorphism
  `Aut(M, B) →* Aut(A ⊗[R] M, B_A)` (`TauCeti.BilinForm.isometryGroupBaseChange`). For `R = ℤ` and
  `A = ℂ` this is the action of `Aut(V, Q)` on the complexification of the lattice. When `Q` is
  preserved by monodromy, the monodromy of a variation of Hodge structure acts through this map.

## Main definitions

* `TauCeti.BilinForm.IsIsometry`: an endomorphism preserves a bilinear form.
* `TauCeti.BilinForm.isometryGroup`: the isometry group `Aut(M, B) ≤ M ≃ₗ[R] M`.
* `TauCeti.BilinForm.IsIsometry.toIsometryGroup`: an isometry of a left-separating form on a finite
  free module over an integral domain, as an element of the isometry group.
* `TauCeti.BilinForm.isometryGroupBaseChange`: base change of isometries, as a group homomorphism.
* `TauCeti.BilinForm.isometryGroupCongr`: transport of the isometry group along a linear
  equivalence.

## Main results

* `TauCeti.BilinForm.isIsometry_iff_toMatrix`: the Gram-matrix criterion `Aᵀ * G * A = G`.
* `TauCeti.BilinForm.IsIsometry.det_sq_eq_one`: `(det f) ^ 2 = 1` for an isometry of a form whose
  Gram determinant is a non-zero-divisor.
* `TauCeti.BilinForm.IsIsometry.bijective`: over an integral domain, an isometry of a
  left-separating form on a finite free module is bijective.
* `TauCeti.BilinForm.IsIsometry.map_orthogonal`: a surjective isometry carries `B`-orthogonal
  complements to `B`-orthogonal complements.

## Implementation notes

The API is laid out by hypothesis strength: the imported predicate and elementary bridge to
Mathlib, the group, transport along a linear equivalence, the Gram-matrix criterion, and base
change need only a `CommSemiring` and additive monoids, which is where every Mathlib ingredient
they consume is stated; injectivity needs subtraction in `M`; the determinant results need `M` to
be an additive group over a `CommRing`; the automatic invertibility of an isometry of a
left-separating form needs an integral domain and a finite free module.

This is the bilinear-form counterpart of `TauCeti.QuadraticMap.orthogonalGroup` in
`TauCeti/LinearAlgebra/QuadraticForm/OrthogonalGroup.lean`, whose API it follows; for a quadratic
form `Q` over a ring in which `2` is a regular scalar the orthogonal group of `Q` is the isometry
group of `Q.polarBilin`, `TauCeti.QuadraticMap.orthogonalGroup_eq_isometryGroup_polarBilin`.

The roadmap names the predicate `IsLatticeIsometry Qint`, on a lattice automorphism `e : V ≃ₗ[ℤ] V`.
Preserving a bilinear form is not lattice-specific, so it is stated here for an endomorphism of a
module over an arbitrary commutative ring, with the roadmap's integral case `R = ℤ` the intended
specialisation and the automatic invertibility of an isometry of a left-separating integral form
(`TauCeti.BilinForm.IsIsometry.toIsometryGroup`) recovering the automorphism form; the declaration
is named after the general statement rather than after the lattice. For the same reason the file
sits with the repository's other bilinear-form material rather than under `TauCeti/Geometry/Hodge/`.

## References

* [Hodge structures, polarizations and period domains roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HodgeStructures/README.md),
  Layer 3, "Period-domain points; the symmetry group": `IsLatticeIsometry Qint` cutting out
  `Aut(V, Qint)`, and its companion "the `Subgroup`/`Group` packaging of `Aut(V, Qint)`".
-/

public section

namespace TauCeti

open Module
open LinearMap (BilinForm)
open scoped Matrix TensorProduct

namespace BilinForm

section CommSemiring

variable {R M M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
  [Module R M']

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

namespace IsIsometry

/-- An isometry preserving a submodule restricts to an isometry of the restricted form. -/
theorem restrict {N : Submodule R M} (hf : IsIsometry B f) (hN : ∀ x ∈ N, f x ∈ N) :
    IsIsometry (B.restrict N) (f.restrict hN) := isIsometry_iff.mpr fun x y => by
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.coe_restrict_apply]
  exact hf.apply x y

/-- An isometry maps the `B`-orthogonal complement of `N` into the `B`-orthogonal complement of
the image of `N`. -/
theorem map_orthogonal_le (hf : IsIsometry B f) (N : Submodule R M) :
    (B.orthogonal N).map f ≤ B.orthogonal (N.map f) := by
  rintro - ⟨x, hx, rfl⟩
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rintro - ⟨n, hn, rfl⟩
  rw [hf.apply n x]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) n hn

/-- A surjective isometry carries `B`-orthogonal complements to `B`-orthogonal complements. -/
theorem map_orthogonal (hf : IsIsometry B f) (hsurj : Function.Surjective f) (N : Submodule R M) :
    (B.orthogonal N).map f = B.orthogonal (N.map f) := by
  refine le_antisymm (hf.map_orthogonal_le N) fun x hx => ?_
  obtain ⟨z, rfl⟩ := hsurj x
  refine Submodule.mem_map_of_mem ?_
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [← hf.apply n z]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ ⟨n, hn, rfl⟩

end IsIsometry

/-- The isometry group `Aut(M, B)` of a bilinear form `B` on `M`: the linear automorphisms of `M`
that preserve `B`.

For a finite free `ℤ`-module `V` carrying an integral form `Q` this is the arithmetic group
`Aut(V, Q)`; when `Q` is preserved by monodromy, a variation of Hodge structure has its monodromy
representation land in this group and act on the complexification through
`TauCeti.BilinForm.isometryGroupBaseChange`. -/
def isometryGroup (B : BilinForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {e | IsIsometry B (e : M →ₗ[R] M)}
  one_mem' := isIsometry_iff.mpr fun _ _ => rfl
  mul_mem' := fun {a b} ha hb => isIsometry_iff.mpr fun x y =>
    (ha.apply (b x) (b y)).trans (hb.apply x y)
  inv_mem' := fun {a} ha => isIsometry_iff.mpr fun x y => by
    simpa using (ha.apply (a.symm x) (a.symm y)).symm

/-- Membership in the isometry group is the isometry predicate. -/
theorem mem_isometryGroup {e : M ≃ₗ[R] M} :
    e ∈ isometryGroup B ↔ IsIsometry B (e : M →ₗ[R] M) := Iff.rfl

@[simp]
theorem mem_isometryGroup_iff {e : M ≃ₗ[R] M} :
    e ∈ isometryGroup B ↔ ∀ x y, B (e x) (e y) = B x y :=
  mem_isometryGroup.trans isIsometry_iff

/-- Membership in `Aut(M, B)` is exactly Mathlib's notion of a self-isometry of `B`: the subgroup
`TauCeti.BilinForm.isometryGroup B` and the type `LinearMap.BilinForm.IsometryEquiv B B` carry the
same data, the subgroup adding the group structure. -/
def isometryGroupEquivIsometryEquiv (B : BilinForm R M) :
    isometryGroup B ≃ B.IsometryEquiv B where
  toFun e := ⟨e.1, fun x y => (mem_isometryGroup.mp e.2).apply x y⟩
  invFun e := ⟨e.toLinearEquiv,
    mem_isometryGroup.mpr (isIsometry_iff.mpr fun x y => e.map_app y x)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_isometryGroupEquivIsometryEquiv (B : BilinForm R M) (e : isometryGroup B) :
    ⇑(isometryGroupEquivIsometryEquiv B e) = ⇑(e : M ≃ₗ[R] M) := (rfl)

@[simp]
theorem coe_isometryGroupEquivIsometryEquiv_symm (B : BilinForm R M) (e : B.IsometryEquiv B) :
    (((isometryGroupEquivIsometryEquiv B).symm e : M ≃ₗ[R] M) : M → M) = ⇑e := (rfl)

section Congr

/-- Conjugation by `e` carries `Aut(M, B)` onto `Aut(M', B ∘ e⁻¹)`. -/
private theorem map_isometryGroup (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    (isometryGroup B).map (LinearEquiv.congrAut e : _ →* _)
      = isometryGroup (LinearMap.BilinForm.congr e B) := by
  ext g
  simp only [Subgroup.mem_map, MonoidHom.coe_coe, mem_isometryGroup_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ x y
    simp only [LinearEquiv.congrAut_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_apply_apply]
    exact ha _ _
  · refine fun hg => ⟨(LinearEquiv.congrAut e).symm g, fun x y => ?_,
      (LinearEquiv.congrAut e).apply_symm_apply g⟩
    have := hg (e x) (e y)
    simpa only [LinearEquiv.congrAut_symm_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_apply_apply] using this

/-- Transporting a bilinear form along a linear equivalence transports its isometry group:
conjugation by `e : M ≃ₗ[R] M'` carries `Aut(M, B)` onto `Aut(M', B ∘ e⁻¹)`. -/
def isometryGroupCongr (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    isometryGroup B ≃* isometryGroup (LinearMap.BilinForm.congr e B) :=
  ((LinearEquiv.congrAut e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_isometryGroup B e))

@[simp]
theorem coe_isometryGroupCongr_apply (B : BilinForm R M) (e : M ≃ₗ[R] M') (a : isometryGroup B)
    (x : M') : (isometryGroupCongr B e a : M' ≃ₗ[R] M') x = e ((a : M ≃ₗ[R] M) (e.symm x)) := by
  simp [isometryGroupCongr]

@[simp]
theorem coe_isometryGroupCongr_symm_apply (B : BilinForm R M) (e : M ≃ₗ[R] M')
    (a : isometryGroup (LinearMap.BilinForm.congr e B)) (x : M) :
    ((isometryGroupCongr B e).symm a : M ≃ₗ[R] M) x
      = e.symm ((a : M' ≃ₗ[R] M') (e x)) := by
  simp [isometryGroupCongr]

end Congr

/-! ### The Gram-matrix criterion -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An endomorphism is an isometry of `B` exactly when its matrix `A` in a basis `b` satisfies
`Aᵀ * G * A = G` for the Gram matrix `G` of `B` in `b`. -/
theorem isIsometry_iff_toMatrix (b : Basis ι R M) :
    IsIsometry B f ↔
      (LinearMap.toMatrix b b f)ᵀ * LinearMap.BilinForm.toMatrix b B * LinearMap.toMatrix b b f
        = LinearMap.BilinForm.toMatrix b B := by
  rw [isIsometry_iff_comp, ← (LinearMap.BilinForm.toMatrix b).injective.eq_iff,
    LinearMap.BilinForm.toMatrix_comp b b B f f]

end Matrix

/-! ### Base change -/

section BaseChange

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- Base change along an `R`-algebra `A` carries an isometry of `B` to an isometry of the
base-changed form. -/
theorem IsIsometry.baseChange (hf : IsIsometry B f) :
    IsIsometry (LinearMap.BilinForm.baseChange A B) (f.baseChange A) := by
  rw [isIsometry_iff]
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul a' m' => simp [hf.apply m m']

/-- Base change along an `R`-algebra `A` is a group homomorphism
`Aut(M, B) →* Aut(A ⊗[R] M, B_A)`. For `R = ℤ` and `A = ℂ` this is the action of the arithmetic
group `Aut(V, Q)` on the complexification of the lattice, through which monodromy acts when it
preserves `Q`. -/
def isometryGroupBaseChange (B : BilinForm R M) :
    isometryGroup B →* isometryGroup (LinearMap.BilinForm.baseChange A B) where
  toFun e := ⟨LinearEquiv.baseChange R A M M (e : M ≃ₗ[R] M),
    mem_isometryGroup.mpr (IsIsometry.baseChange A (mem_isometryGroup.mp e.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [_root_.LinearEquiv.baseChange_mul])

@[simp]
theorem coe_isometryGroupBaseChange (B : BilinForm R M) (e : isometryGroup B) :
    (isometryGroupBaseChange A B e : A ⊗[R] M ≃ₗ[A] A ⊗[R] M)
      = LinearEquiv.baseChange R A M M (e : M ≃ₗ[R] M) := (rfl)

end BaseChange

end CommSemiring

section AddCommGroup

variable {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {B : BilinForm R M} {f : M →ₗ[R] M}

/-- An isometry of a left-separating form is injective: it cannot collapse a vector that pairs
nontrivially with something. -/
theorem IsIsometry.injective (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    Function.Injective f := by
  intro x y hxy
  rw [← sub_eq_zero]
  refine hB (x - y) fun z => ?_
  rw [← hf.apply (x - y) z, map_sub, hxy, sub_self, LinearMap.map_zero₂]

end AddCommGroup

/-! ### Determinants -/

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}
  {f : M →ₗ[R] M}

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace IsIsometry

/-- An isometry scales the Gram determinant by the square of its determinant — and hence, the form
being preserved, not at all. -/
theorem det_sq_mul_det_toMatrix_self (b : Basis ι R M) (hf : IsIsometry B f) :
    LinearMap.det f ^ 2 * (LinearMap.BilinForm.toMatrix b B).det =
      (LinearMap.BilinForm.toMatrix b B).det := by
  have h := congrArg Matrix.det ((isIsometry_iff_toMatrix b).mp hf)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at h
  calc LinearMap.det f ^ 2 * (LinearMap.BilinForm.toMatrix b B).det
      = LinearMap.det f * (LinearMap.BilinForm.toMatrix b B).det * LinearMap.det f := by ring
    _ = (LinearMap.BilinForm.toMatrix b B).det := h

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor has determinant
squaring to `1`; over `ℤ` this says its determinant is `±1`. -/
theorem det_sq_eq_one (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsIsometry B f) : LinearMap.det f ^ 2 = 1 := by
  have h : (LinearMap.det f ^ 2 - 1) * (LinearMap.BilinForm.toMatrix b B).det = 0 := by
    rw [sub_mul, one_mul, hf.det_sq_mul_det_toMatrix_self b, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hG).2 _ h)

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor has unit
determinant, its square being `1`. -/
theorem isUnit_det (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsIsometry B f) : IsUnit (LinearMap.det f) :=
  IsUnit.of_mul_eq_one _ (by rw [← sq]; exact hf.det_sq_eq_one b hG)

end IsIsometry

/-- Over an integral domain, the Gram determinant of a left-separating form is a
non-zero-divisor. -/
theorem det_toMatrix_mem_nonZeroDivisors [IsDomain R] (b : Basis ι R M)
    (hB : B.SeparatingLeft) :
    (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero b).mp hB)

end Matrix

section UnitDeterminant

variable [Module.Free R M] [Module.Finite R M]

namespace IsIsometry

/-- An isometry whose underlying endomorphism has unit determinant, as an element of the isometry
group. -/
noncomputable def toIsometryGroupOfIsUnitDet (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) : isometryGroup B :=
  ⟨LinearMap.equivOfIsUnitDet hdet,
    mem_isometryGroup.mpr (isIsometry_iff.mpr fun x y => by simpa using hf.apply x y)⟩

@[simp]
theorem coe_toIsometryGroupOfIsUnitDet (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) :
    ((hf.toIsometryGroupOfIsUnitDet hdet : isometryGroup B) : M →ₗ[R] M) = f :=
  LinearMap.coe_equivOfIsUnitDet hdet

@[simp]
theorem toIsometryGroupOfIsUnitDet_apply (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) (x : M) :
    (hf.toIsometryGroupOfIsUnitDet hdet : M ≃ₗ[R] M) x = f x :=
  LinearMap.equivOfIsUnitDet_apply hdet x

end IsIsometry

end UnitDeterminant

section SeparatingLeft

variable [IsDomain R] [Module.Free R M] [Module.Finite R M]

namespace IsIsometry

/-- An isometry of a left-separating form on a finite free module over an integral domain has unit
determinant. -/
theorem isUnit_det_of_separatingLeft (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    IsUnit (LinearMap.det f) :=
  hf.isUnit_det (Module.Free.chooseBasis R M)
    (det_toMatrix_mem_nonZeroDivisors (Module.Free.chooseBasis R M) hB)

/-- Over an integral domain, an endomorphism of a finite free module preserving a left-separating
bilinear form is automatically invertible, hence an element of the isometry group. This is how an
element of `Aut(V, Q)` usually presents itself: as an endomorphism of the lattice `V` preserving
`Q`, with invertibility a consequence rather than a hypothesis. -/
noncomputable def toIsometryGroup (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    isometryGroup B :=
  hf.toIsometryGroupOfIsUnitDet (hf.isUnit_det_of_separatingLeft hB)

@[simp]
theorem coe_toIsometryGroup (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    ((hf.toIsometryGroup hB : isometryGroup B) : M →ₗ[R] M) = f :=
  LinearMap.coe_equivOfIsUnitDet (hf.isUnit_det_of_separatingLeft hB)

@[simp]
theorem toIsometryGroup_apply (hB : B.SeparatingLeft) (hf : IsIsometry B f) (x : M) :
    (hf.toIsometryGroup hB : M ≃ₗ[R] M) x = f x :=
  LinearMap.equivOfIsUnitDet_apply (hf.isUnit_det_of_separatingLeft hB) x

/-- Over an integral domain, an endomorphism of a finite free module preserving a left-separating
bilinear form is automatically bijective. -/
theorem bijective (hB : B.SeparatingLeft) (hf : IsIsometry B f) : Function.Bijective f :=
  (Module.End.isUnit_iff f).mp
    ((LinearMap.isUnit_iff_isUnit_det f).mpr (hf.isUnit_det_of_separatingLeft hB))

end IsIsometry

end SeparatingLeft

end CommRing

end BilinForm

end TauCeti
