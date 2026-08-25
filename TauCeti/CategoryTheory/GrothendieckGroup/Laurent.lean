/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent
public import TauCeti.CategoryTheory.GrothendieckGroup.Graded

/-!
# The Laurent coefficient ring acting on the graded Grothendieck group

The grading shift `{1}` of a graded exact category acts on its exact Grothendieck group by the
automorphism `TauCeti.GradedExactStructure.shiftEquiv`, and iterating it gives the `ℤ`-action
`TauCeti.GradedExactStructure.shiftZPow`.  Repackaging that `ℤ`-action as a module structure over
`ℤ[q,q⁻¹] = LaurentPolynomial ℤ` is what turns graded `K₀` into the lattice on which a `q`-Euler
form can live.

`TauCeti.LaurentK0 E` is the graded Grothendieck group of a graded exact category `E` carrying that
module structure.  It is a type synonym for `TauCeti.ExactK0 E.toExactStructure`, moved across by
the additive equivalence `TauCeti.LaurentK0.ofExactK0`: no new group is constructed, and no
relation is added.  The synonym exists only because the module structure depends on the grading
shift, which the underlying exact structure does not remember.  The defining property is
`TauCeti.LaurentK0.T_smul`, the normalization `[M{n}] = qⁿ [M]` of the roadmap.

The universal property `TauCeti.LaurentK0.liftEquiv` is the `ℤ[q,q⁻¹]`-linear form of the graded
one: for a `ℤ[q,q⁻¹]`-module `N`, the `ℤ[q,q⁻¹]`-linear maps out of `LaurentK0 E` are exactly the
conflation-additive invariants `a` with `a(M{1}) = q · a(M)`, that is, the shift-compatible
invariants of `TauCeti.GradedExactStructure.ShiftInvariant` for the automorphism
`TauCeti.laurentTAut N` of multiplication by `q`.

## Main definitions

* `TauCeti.LaurentK0`: the graded exact Grothendieck group as a `ℤ[q,q⁻¹]`-module.
* `TauCeti.LaurentK0.ofExactK0`: the additive equivalence with the underlying exact `K₀`.
* `TauCeti.LaurentK0.of`: the class `[M]` of an object.
* `TauCeti.LaurentK0.lift`: the `ℤ[q,q⁻¹]`-linear map induced by a shift-compatible invariant.
* `TauCeti.LaurentK0.map`: the `ℤ[q,q⁻¹]`-linear map induced by a graded conflation-exact functor.
* `TauCeti.LaurentK0.mapEquiv`: the isomorphism induced by a graded exact equivalence.

## Main results

* `TauCeti.LaurentK0.T_smul`: `qⁿ · [M] = [M{n}]`, and its generating cases
  `TauCeti.LaurentK0.T_one_smul_of` and `TauCeti.LaurentK0.T_neg_one_smul_of`.
* `TauCeti.LaurentK0.liftEquiv`: the universal property over the Laurent coefficient ring.
* `TauCeti.LaurentK0.hom_ext`: a `ℤ[q,q⁻¹]`-linear map out of `LaurentK0 E` is determined by its
  values on object classes.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, Definition 2.3, where the graded
  Grothendieck group is presented as a `ℤ[q,q⁻¹]`-module with `[M{1}] = q[M]`.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, first bullet: "For a graded exact
  category from Layer 2, construct the `R`-module structure on its graded `K₀` and prove
  `[M{n}] = qⁿ[M]` for every `n : ℤ`, in particular `[M{1}] = q[M]`.  State the universal property
  for additive invariants equipped with a compatible invertible shift action."
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w w' w'' v v' v'' u u' u''

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- **The graded Grothendieck group of a graded exact category, over the Laurent coefficient
ring.**  The underlying additive group is the exact Grothendieck group of the underlying exact
structure; the grading shift makes it a module over `ℤ[q,q⁻¹]`, with `q` acting as `[M] ↦ [M{1}]`.

The type synonym is needed because a `ℤ[q,q⁻¹]`-module structure is determined by an automorphism
of the group, and `ExactK0 E.toExactStructure` does not mention the grading shift.  Use
`TauCeti.LaurentK0.ofExactK0` to move between the two views. -/
@[expose]
def LaurentK0 (E : GradedExactStructure C) : Type w := ExactK0 E.toExactStructure

namespace LaurentK0

variable (E : GradedExactStructure C)

instance : AddCommGroup (LaurentK0 E) :=
  inferInstanceAs (AddCommGroup (ExactK0 E.toExactStructure))

/-- **The graded Grothendieck group is the exact one.**  Moving a class across this equivalence
changes nothing but which module structure is in scope. -/
@[expose]
def ofExactK0 : ExactK0 E.toExactStructure ≃+ LaurentK0 E :=
  AddEquiv.refl _

/-- The grading shift, as a `ℤ`-linear automorphism of the graded Grothendieck group. -/
@[expose]
noncomputable def shiftLinearEquiv : LaurentK0 E ≃ₗ[ℤ] LaurentK0 E :=
  { E.shiftEquiv with map_smul' := fun a x => map_zsmul E.shiftEquiv a x }

/-- The grading shift as a unit of the endomorphism ring of the graded Grothendieck group: this is
the unit at which the Laurent variable is evaluated. -/
@[expose]
noncomputable def shiftUnit : (Module.End ℤ (LaurentK0 E))ˣ where
  val := shiftLinearEquiv E
  inv := (shiftLinearEquiv E).symm
  val_inv := LinearMap.ext fun x => (shiftLinearEquiv E).apply_symm_apply x
  inv_val := LinearMap.ext fun x => (shiftLinearEquiv E).symm_apply_apply x

/-- **The Laurent coefficient ring acts on the graded Grothendieck group**, the variable acting
by the grading shift. -/
noncomputable instance : Module (LaurentPolynomial ℤ) (LaurentK0 E) :=
  Module.compHom (LaurentK0 E) (laurentEval (shiftUnit E)).toRingHom

/-- The Laurent action is evaluation of the polynomial at the grading shift. -/
lemma smul_def (p : LaurentPolynomial ℤ) (x : LaurentK0 E) :
    p • x = laurentEval (shiftUnit E) p x :=
  (rfl)

lemma shiftUnit_apply (x : ExactK0 E.toExactStructure) :
    (shiftUnit E : Module.End ℤ (LaurentK0 E)) (ofExactK0 E x) = ofExactK0 E (E.shiftEquiv x) :=
  (rfl)

lemma shiftUnit_inv_apply (x : ExactK0 E.toExactStructure) :
    (↑(shiftUnit E)⁻¹ : Module.End ℤ (LaurentK0 E)) (ofExactK0 E x) =
      ofExactK0 E (E.shiftEquiv.symm x) :=
  (rfl)

lemma shiftUnit_zpow_apply (n : ℤ) (x : ExactK0 E.toExactStructure) :
    (↑(shiftUnit E ^ n) : Module.End ℤ (LaurentK0 E)) (ofExactK0 E x) =
      ofExactK0 E (E.shiftZPow n x) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [GradedExactStructure.shiftZPow_add_one_apply, ← shiftUnit_apply, ← ih,
        ← Module.End.mul_apply, ← Units.val_mul, ← zpow_one_add, add_comm 1 (k : ℤ)]
  | pred k ih =>
      rw [GradedExactStructure.shiftZPow_sub_one_apply, ← shiftUnit_inv_apply, ← ih,
        ← Module.End.mul_apply, ← Units.val_mul, ← zpow_neg_one, ← zpow_add]
      have h : (-1 : ℤ) + (-(k : ℤ)) = -(k : ℤ) - 1 := by ring
      rw [h]

/-- **`qⁿ · [M] = [M{n}]`**: the Laurent variable acts on the graded Grothendieck group by the
grading shift, and its `n`-th power by the `n`-fold shift.  This is the normalization fixed by the
roadmap, and it determines the module structure. -/
@[simp]
theorem T_smul (n : ℤ) (x : ExactK0 E.toExactStructure) :
    (T n : LaurentPolynomial ℤ) • ofExactK0 E x = ofExactK0 E (E.shiftZPow n x) := by
  rw [smul_def, laurentEval_T, shiftUnit_zpow_apply]

/-- The class `[M]` of an object in the graded Grothendieck group. -/
noncomputable def of (X : C) : LaurentK0 E :=
  ofExactK0 E (ExactK0.of X)

@[simp]
lemma ofExactK0_exactK0_of (X : C) : ofExactK0 E (ExactK0.of X) = of E X :=
  (rfl)

/-- Isomorphic objects have the same class. -/
theorem of_congr {X Y : C} (e : X ≅ Y) : of E X = of E Y := by
  rw [← ofExactK0_exactK0_of, ← ofExactK0_exactK0_of, ExactK0.of_congr e]

/-- **`q · [M] = [M{1}]`.** -/
@[simp]
theorem T_one_smul_of (X : C) :
    (T 1 : LaurentPolynomial ℤ) • of E X = of E (E.shift.functor.obj X) := by
  rw [← ofExactK0_exactK0_of, T_smul, GradedExactStructure.shiftZPow_one_apply_of,
    ofExactK0_exactK0_of]

/-- **`q⁻¹ · [M] = [M{-1}]`.** -/
@[simp]
theorem T_neg_one_smul_of (X : C) :
    (T (-1) : LaurentPolynomial ℤ) • of E X = of E (E.shift.inverse.obj X) := by
  rw [← ofExactK0_exactK0_of, T_smul, GradedExactStructure.shiftZPow_neg_one_apply_of,
    ofExactK0_exactK0_of]

/-- The constants of the Laurent coefficient ring act by the integer scalar multiplication of the
underlying abelian group. -/
lemma C_smul (a : ℤ) (x : LaurentK0 E) :
    (LaurentPolynomial.C a : LaurentPolynomial ℤ) • x = a • x :=
  laurentC_smul a x

instance : IsScalarTower ℤ (LaurentPolynomial ℤ) (LaurentK0 E) where
  smul_assoc a p x := by
    rw [laurent_zsmul_eq_C_mul, mul_smul, C_smul]

/-- **A `ℤ[q,q⁻¹]`-linear map out of the graded Grothendieck group is determined by its values on
object classes**, because those classes generate the underlying group. -/
theorem hom_ext {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]
    {f g : LaurentK0 E →ₗ[LaurentPolynomial ℤ] N} (h : ∀ X : C, f (of E X) = g (of E X)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  have key : f.toAddMonoidHom.comp (ofExactK0 E).toAddMonoidHom =
      g.toAddMonoidHom.comp (ofExactK0 E).toAddMonoidHom :=
    ExactK0.hom_ext fun X => by simpa using h X
  simpa using DFunLike.congr_fun key ((ofExactK0 E).symm x)

section UniversalProperty

variable {E}
variable {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]

/-- An additive map out of the exact Grothendieck group which turns the grading shift into
multiplication by `q` turns the whole `ℤ`-action into multiplication by `qⁿ`. -/
theorem apply_shiftZPow (f : ExactK0 E.toExactStructure →+ N)
    (hf : ∀ x, f (E.shiftEquiv x) = (T 1 : LaurentPolynomial ℤ) • f x) (n : ℤ)
    (x : ExactK0 E.toExactStructure) :
    f (E.shiftZPow n x) = (T n : LaurentPolynomial ℤ) • f x := by
  have hsymm : ∀ y, f (E.shiftEquiv.symm y) = (T (-1) : LaurentPolynomial ℤ) • f y := fun y => by
    have hy := hf (E.shiftEquiv.symm y)
    rw [AddEquiv.apply_symm_apply] at hy
    rw [hy, smul_smul, ← T_add]
    simp
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [GradedExactStructure.shiftZPow_add_one_apply, hf, ih, smul_smul, ← T_add,
        add_comm 1 (k : ℤ)]
  | pred k ih =>
      rw [GradedExactStructure.shiftZPow_sub_one_apply, hsymm, ih, smul_smul, ← T_add]
      have h : (-1 : ℤ) + (-(k : ℤ)) = -(k : ℤ) - 1 := by ring
      rw [h]

/-- The `ℤ[q,q⁻¹]`-linear map out of the graded Grothendieck group determined by a
shift-compatible additive map on the underlying exact one. -/
noncomputable def liftAux (f : ExactK0 E.toExactStructure →+ N)
    (hf : ∀ x, f (E.shiftEquiv x) = (T 1 : LaurentPolynomial ℤ) • f x) :
    LaurentK0 E →ₗ[LaurentPolynomial ℤ] N where
  toFun x := f ((ofExactK0 E).symm x)
  map_add' x y := by simp
  map_smul' p x := by
    simp only [RingHom.id_apply]
    obtain ⟨z, rfl⟩ : ∃ z, ofExactK0 E z = x := ⟨(ofExactK0 E).symm x, by simp⟩
    simp only [AddEquiv.symm_apply_apply]
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
        rw [add_smul, map_add, map_add, hp, hq, add_smul]
    | C_mul_T n a =>
        rw [mul_smul, T_smul, laurentC_smul, ← map_zsmul (ofExactK0 E),
          AddEquiv.symm_apply_apply, map_zsmul f, apply_shiftZPow f hf, mul_smul,
          laurentC_smul]

@[simp]
lemma liftAux_of (f : ExactK0 E.toExactStructure →+ N)
    (hf : ∀ x, f (E.shiftEquiv x) = (T 1 : LaurentPolynomial ℤ) • f x) (X : C) :
    liftAux f hf (of E X) = f (ExactK0.of X) :=
  (rfl)

variable (E) in
/-- **The homomorphism out of graded `K₀` induced by a shift-compatible invariant**, as a map of
`ℤ[q,q⁻¹]`-modules.  The invariant is compared against multiplication by `q` on the target. -/
noncomputable def lift (a : GradedExactStructure.ShiftInvariant E (laurentTAut N)) :
    LaurentK0 E →ₗ[LaurentPolynomial ℤ] N :=
  liftAux a.lift fun x => by simpa using a.lift_shiftEquiv x

@[simp]
lemma lift_of (a : GradedExactStructure.ShiftInvariant E (laurentTAut N)) (X : C) :
    lift E a (of E X) = a.obj X := by
  rw [lift, liftAux_of, GradedExactStructure.ShiftInvariant.lift_of]

variable (E) in
/-- **The universal property of graded `K₀` over the Laurent coefficient ring.**  For a
`ℤ[q,q⁻¹]`-module `N`, the `ℤ[q,q⁻¹]`-linear maps out of `LaurentK0 E` correspond bijectively to
the conflation-additive invariants whose value on `M{1}` is `q` times the value on `M`.

This is the Layer 2 universal property of a shift-compatible invariant, with the abstract
automorphism of the target replaced by the one the coefficient ring supplies. -/
noncomputable def liftEquiv :
    GradedExactStructure.ShiftInvariant E (laurentTAut N) ≃
      (LaurentK0 E →ₗ[LaurentPolynomial ℤ] N) where
  toFun := lift E
  invFun g :=
    (GradedExactStructure.ShiftInvariant.liftEquiv (laurentTAut N)).symm
      ⟨g.toAddMonoidHom.comp (ofExactK0 E).toAddMonoidHom, fun x => by
        simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, laurentTAut_apply,
          LinearMap.toAddMonoidHom_coe]
        conv_rhs => rw [← map_smul g, T_smul]
        simp⟩
  left_inv a := by
    ext X
    simp
  right_inv g := by
    refine hom_ext E fun X => ?_
    simp [lift]

end UniversalProperty

section Functoriality

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
variable {E} {E' : GradedExactStructure D} {F : C ⥤ D} [F.Additive]

/-- **A graded conflation-exact functor induces a `ℤ[q,q⁻¹]`-linear map** of graded Grothendieck
groups: the shift-equivariance proved in the `ℤ`-graded layer is exactly `q`-linearity. -/
noncomputable def map (h : GradedConflationExact E E' F) :
    LaurentK0 E →ₗ[LaurentPolynomial ℤ] LaurentK0 E' :=
  liftAux ((ofExactK0 E').toAddMonoidHom.comp (ExactK0.map F h.isConflationExact)) fun x => by
    simp [GradedExactStructure.map_shiftEquiv h]

@[simp]
lemma map_of (h : GradedConflationExact E E' F) (X : C) :
    map h (of E X) = of E' (F.obj X) := by
  rw [map, liftAux_of, AddMonoidHom.comp_apply, ExactK0.map_of, AddEquiv.coe_toAddMonoidHom,
    ofExactK0_exactK0_of]

@[simp]
theorem map_id : map (GradedConflationExact.id E) = LinearMap.id :=
  hom_ext E fun X => by simp

variable {K : Type u''} [Category.{v''} K] [Preadditive K] [HasZeroObject K]
  [HasBinaryBiproducts K] [EssentiallySmall.{w''} K]

theorem map_comp {E'' : GradedExactStructure K} {H : D ⥤ K} [H.Additive]
    (h : GradedConflationExact E E' F) (h' : GradedConflationExact E' E'' H) :
    map (h.comp h') = (map h').comp (map h) :=
  hom_ext E fun X => by simp

end Functoriality

section Invariance

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
variable {E} {E' : GradedExactStructure D}

/-- **A graded exact equivalence induces an isomorphism of `ℤ[q,q⁻¹]`-modules.**  Graded `K₀` over
the Laurent coefficient ring is therefore an invariant of the graded exact category, not of a
presentation of it. -/
noncomputable def mapEquiv (h : GradedExactEquiv E E') :
    LaurentK0 E ≃ₗ[LaurentPolynomial ℤ] LaurentK0 E' :=
  LinearEquiv.ofLinearMap (map h.toGradedConflationExact) (map h.symm.toGradedConflationExact)
    (hom_ext E' fun X => by
      simp only [LinearMap.comp_apply, map_of, GradedExactEquiv.symm_equiv,
        Equivalence.symm_functor, LinearMap.id_coe, id_eq]
      exact of_congr E' (h.equiv.counitIso.app X))
    (hom_ext E fun X => by
      simp only [LinearMap.comp_apply, map_of, GradedExactEquiv.symm_equiv,
        Equivalence.symm_functor, LinearMap.id_coe, id_eq]
      exact of_congr E (h.equiv.unitIso.app X).symm)

@[simp]
lemma mapEquiv_of (h : GradedExactEquiv E E') (X : C) :
    mapEquiv h (of E X) = of E' (h.equiv.functor.obj X) := by
  simp [mapEquiv, LinearEquiv.ofLinearMap]

@[simp]
lemma mapEquiv_symm_of (h : GradedExactEquiv E E') (X : D) :
    (mapEquiv h).symm (of E' X) = of E (h.equiv.inverse.obj X) := by
  simp [mapEquiv, LinearEquiv.ofLinearMap, GradedExactEquiv.symm_equiv]

end Invariance

end LaurentK0

end TauCeti
