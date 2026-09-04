/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic
public import TauCeti.Algebra.Homology.Ext.Equivalence
public import TauCeti.CategoryTheory.Equivalence.Pow

/-!
# The shift identities of the graded Ext-Euler characteristic

Let `C` be a `k`-linear abelian category with a grading shift `e : C ≌ C`, written `{1}`.  The
q-Euler characteristic `χ_q(X, Y) = ∑ n,j (-1)^n q⁻ʲ dim_k Ext^n(X, Y{j})` of
`TauCeti.gradedExtEuler` is q-linear in its second argument and q-antilinear in its first:

```text
χ_q(X, Y{1}) = q · χ_q(X, Y),        χ_q(X{1}, Y) = q⁻¹ · χ_q(X, Y).
```

These are the generating identities behind the sesquilinearity of the q-Euler form, and they fix
the handedness of the internal grading.

Both identities come from a reindexing of the internal degree.  Shifting the target by one
identifies `Ext^{n,j}(X, Y{1})` with `Ext^{n,j+1}(X, Y)`, which multiplies the target-shift graded
dimension by `q`; shifting the source instead identifies `Ext^{n,j}(X{1}, Y)` with
`Ext^{n,j-1}(X, Y)` and multiplies it by `q⁻¹`.  The source identity uses that `Ext` is invariant
under the equivalence `e`, so it needs `e` to be `k`-linear and not merely additive: an additive
isomorphism of `k`-vector spaces need not preserve dimension.  The comparison of `e ^ (j + 1)`
with the composites `e ^ j ∘ e` and `e ∘ e ^ j` is `TauCeti.equivPowSuccIso` and
`TauCeti.equivPowSuccRightIso`.

## Main definitions

* `TauCeti.gradedExtShiftTargetEquiv`: `Ext^{n,j}(X, Y{1}) ≃ₗ[k] Ext^{n,j+1}(X, Y)`.
* `TauCeti.gradedExtShiftSourceEquiv`: `Ext^{n,j}(X{1}, Y) ≃ₗ[k] Ext^{n,j-1}(X, Y)`.

## Main results

* `TauCeti.IsGradedEulerAdmissible.shiftTarget` and
  `TauCeti.IsGradedEulerAdmissible.shiftSource`: graded Euler-admissibility is preserved by the
  grading shift in either variable.
* `TauCeti.gradedExtEuler_shiftTarget`: `χ_q(X, Y{1}) = q · χ_q(X, Y)`.
* `TauCeti.gradedExtEuler_shiftSource`: `χ_q(X{1}, Y) = q⁻¹ · χ_q(X, Y)`.
* `TauCeti.gradedExtEuler_shiftTarget_inverse` and
  `TauCeti.gradedExtEuler_shiftSource_inverse`: the two identities for the inverse shift `{-1}`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Sections 1.2 and 2.2, for the q-antilinear/q-linear
  convention of the q-Euler form.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "q-Euler form".
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]
  (k : Type t) [Field k] [Linear k C] [HasExt.{w} C] (e : C ≌ C)

/-! ### Shifting the target

Nothing in this section needs the shift to be additive or linear: the reindexing is induced by an
isomorphism of objects. -/

/-- Shifting the target of a bigraded `Ext` group raises its internal degree by one:
`Ext^{n,j}(X, Y{1}) ≅ Ext^{n,j+1}(X, Y)`. -/
noncomputable def gradedExtShiftTargetEquiv (X Y : C) (n : ℕ) (j : ℤ) :
    GradedExt.{w} e X (e.functor.obj Y) n j ≃ₗ[k] GradedExt.{w} e X Y n (j + 1) :=
  extLinearEquivOfIso k (Iso.refl X) ((equivPowSuccIso e j).app Y).symm n

variable {k e}
variable {X Y : C}

/-- Finite internal support of bigraded `Ext` is preserved by shifting the target. -/
theorem IsGradedExtInternallyFinite.shiftTarget
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    IsGradedExtInternallyFinite.{w} k e X (e.functor.obj Y) :=
  ⟨fun n => ((h.finiteLaurentSupport n).reindex_add 1).of_equiv fun j =>
    (gradedExtShiftTargetEquiv k e X Y n j).symm⟩

/-- A cohomological vanishing bound is preserved by shifting the target. -/
theorem IsGradedExtBoundedBy.shiftTarget {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) :
    IsGradedExtBoundedBy.{w} e X (e.functor.obj Y) N :=
  ⟨fun n hn j => have := h.subsingleton hn (j + 1)
    (extAddEquivOfIso (Iso.refl X) ((equivPowSuccIso e j).app Y).symm n).toEquiv.subsingleton⟩

/-- Eventual cohomological vanishing of bigraded `Ext` is preserved by shifting the target. -/
theorem IsGradedExtBounded.shiftTarget (h : IsGradedExtBounded.{w} e X Y) :
    IsGradedExtBounded.{w} e X (e.functor.obj Y) :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.shiftTarget⟩

/-- **Graded Euler-admissibility is preserved by shifting the target.** -/
theorem IsGradedEulerAdmissible.shiftTarget (h : IsGradedEulerAdmissible.{w} k e X Y) :
    IsGradedEulerAdmissible.{w} k e X (e.functor.obj Y) :=
  ⟨h.internallyFinite.shiftTarget, h.bounded.shiftTarget⟩

/-- Shifting the target multiplies the graded `Ext` dimension in one cohomological degree by
`q`. -/
theorem gradedExtDimension_shiftTarget {n : ℕ}
    (h : HasFiniteLaurentSupport k (GradedExt.{w} e X Y n))
    (h' : HasFiniteLaurentSupport k (GradedExt.{w} e X (e.functor.obj Y) n)) :
    gradedExtDimension k e h' = T 1 * gradedExtDimension k e h := by
  ext j
  simp only [T, coeff_gradedExtDimension, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  rw [(gradedExtShiftTargetEquiv k e X Y n (-j)).finrank_eq]
  have hj : -j + 1 = -(-1 + j) := by omega
  rw [hj]

/-- Shifting the target multiplies every truncation of the q-Euler sum by `q`. -/
theorem truncatedGradedExtEuler_shiftTarget (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (h' : IsGradedExtInternallyFinite.{w} k e X (e.functor.obj Y)) (N : ℕ) :
    truncatedGradedExtEuler k e h' N = T 1 * truncatedGradedExtEuler k e h N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [truncatedGradedExtEuler_succ, truncatedGradedExtEuler_succ, ih, mul_add,
        gradedExtDimension_shiftTarget (h.finiteLaurentSupport N) (h'.finiteLaurentSupport N),
        mul_smul_comm]

/-- **`χ_q(X, Y{1}) = q · χ_q(X, Y)`**: the q-Euler characteristic is q-linear in its second
argument. -/
theorem gradedExtEuler_shiftTarget (h : IsGradedEulerAdmissible.{w} k e X Y)
    (h' : IsGradedEulerAdmissible.{w} k e X (e.functor.obj Y)) :
    gradedExtEuler k e h' = T 1 * gradedExtEuler k e h := by
  obtain ⟨N, hN⟩ := h.bounded.exists_bound
  rw [gradedExtEuler_eq k e h hN, gradedExtEuler_eq k e h' hN.shiftTarget]
  exact truncatedGradedExtEuler_shiftTarget h.internallyFinite h'.internallyFinite N

/-- **`χ_q(X, Y{-1}) = q⁻¹ · χ_q(X, Y)`**: the inverse shift of the second argument. -/
theorem gradedExtEuler_shiftTarget_inverse (h : IsGradedEulerAdmissible.{w} k e X Y)
    (h' : IsGradedEulerAdmissible.{w} k e X (e.inverse.obj Y)) :
    gradedExtEuler k e h' = T (-1) * gradedExtEuler k e h := by
  have hcounit : gradedExtEuler k e h = gradedExtEuler k e h'.shiftTarget :=
    gradedExtEuler_of_iso k h h'.shiftTarget (Iso.refl X) (e.counitIso.app Y).symm
  rw [hcounit, gradedExtEuler_shiftTarget h' h'.shiftTarget, ← mul_assoc, ← T_add]
  simp

/-! ### Shifting the source

The source identity uses that `Ext` is invariant under `e`, so `e` must be `k`-linear and not
merely additive. -/

variable (k e)
variable [e.functor.Additive] [e.functor.Linear k]

/-- The comparison `(Y{j-1}){1} ≅ Y{j}`, which moves a source shift into the internal degree. -/
private noncomputable def shiftSourceObjIso (Y : C) (j : ℤ) :
    e.functor.obj ((e ^ (j - 1)).functor.obj Y) ≅ (e ^ j).functor.obj Y :=
  ((equivPowSuccRightIso e (j - 1)).app Y).symm ≪≫
    (equivPowCongrIso e (by ring : j - 1 + 1 = j)).app Y

/-- Shifting the source of a bigraded `Ext` group lowers its internal degree by one:
`Ext^{n,j}(X{1}, Y) ≅ Ext^{n,j-1}(X, Y)`. -/
noncomputable def gradedExtShiftSourceEquiv (X Y : C) (n : ℕ) (j : ℤ) :
    GradedExt.{w} e (e.functor.obj X) Y n j ≃ₗ[k] GradedExt.{w} e X Y n (j - 1) :=
  ((extLinearEquivOfEquivalence k e X ((e ^ (j - 1)).functor.obj Y) n).trans
    (extLinearEquivOfIso k (Iso.refl (e.functor.obj X)) (shiftSourceObjIso e Y j) n)).symm

variable {k e}
variable {X Y : C}

/-- Finite internal support of bigraded `Ext` is preserved by shifting the source. -/
theorem IsGradedExtInternallyFinite.shiftSource
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    IsGradedExtInternallyFinite.{w} k e (e.functor.obj X) Y :=
  ⟨fun n => ((h.finiteLaurentSupport n).reindex_add (-1)).of_equiv fun j =>
    (gradedExtShiftSourceEquiv k e X Y n j).symm⟩

omit [Functor.Linear k e.functor] in
/-- A cohomological vanishing bound is preserved by shifting the source. -/
theorem IsGradedExtBoundedBy.shiftSource {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N) :
    IsGradedExtBoundedBy.{w} e (e.functor.obj X) Y N :=
  ⟨fun n hn j => have := h.subsingleton hn (j - 1)
    (((extAddEquivOfEquivalence e X ((e ^ (j - 1)).functor.obj Y) n).trans
      (extAddEquivOfIso (Iso.refl (e.functor.obj X))
        (shiftSourceObjIso e Y j) n)).symm).toEquiv.subsingleton⟩

omit [Functor.Linear k e.functor] in
/-- Eventual cohomological vanishing of bigraded `Ext` is preserved by shifting the source. -/
theorem IsGradedExtBounded.shiftSource (h : IsGradedExtBounded.{w} e X Y) :
    IsGradedExtBounded.{w} e (e.functor.obj X) Y :=
  ⟨h.exists_bound.choose, h.exists_bound.choose_spec.shiftSource⟩

/-- **Graded Euler-admissibility is preserved by shifting the source.** -/
theorem IsGradedEulerAdmissible.shiftSource (h : IsGradedEulerAdmissible.{w} k e X Y) :
    IsGradedEulerAdmissible.{w} k e (e.functor.obj X) Y :=
  ⟨h.internallyFinite.shiftSource, h.bounded.shiftSource⟩

/-- Shifting the source multiplies the graded `Ext` dimension in one cohomological degree by
`q⁻¹`. -/
theorem gradedExtDimension_shiftSource {n : ℕ}
    (h : HasFiniteLaurentSupport k (GradedExt.{w} e X Y n))
    (h' : HasFiniteLaurentSupport k (GradedExt.{w} e (e.functor.obj X) Y n)) :
    gradedExtDimension k e h' = T (-1) * gradedExtDimension k e h := by
  ext j
  simp only [T, coeff_gradedExtDimension, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  rw [(gradedExtShiftSourceEquiv k e X Y n (-j)).finrank_eq]
  have hj : -j - 1 = -(- -1 + j) := by omega
  rw [hj]

/-- Shifting the source multiplies every truncation of the q-Euler sum by `q⁻¹`. -/
theorem truncatedGradedExtEuler_shiftSource (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (h' : IsGradedExtInternallyFinite.{w} k e (e.functor.obj X) Y) (N : ℕ) :
    truncatedGradedExtEuler k e h' N = T (-1) * truncatedGradedExtEuler k e h N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [truncatedGradedExtEuler_succ, truncatedGradedExtEuler_succ, ih, mul_add,
        gradedExtDimension_shiftSource (h.finiteLaurentSupport N) (h'.finiteLaurentSupport N),
        mul_smul_comm]

/-- **`χ_q(X{1}, Y) = q⁻¹ · χ_q(X, Y)`**: the q-Euler characteristic is q-antilinear in its first
argument. -/
theorem gradedExtEuler_shiftSource (h : IsGradedEulerAdmissible.{w} k e X Y)
    (h' : IsGradedEulerAdmissible.{w} k e (e.functor.obj X) Y) :
    gradedExtEuler k e h' = T (-1) * gradedExtEuler k e h := by
  obtain ⟨N, hN⟩ := h.bounded.exists_bound
  rw [gradedExtEuler_eq k e h hN, gradedExtEuler_eq k e h' hN.shiftSource]
  exact truncatedGradedExtEuler_shiftSource h.internallyFinite h'.internallyFinite N

/-- **`χ_q(X{-1}, Y) = q · χ_q(X, Y)`**: the inverse shift of the first argument. -/
theorem gradedExtEuler_shiftSource_inverse (h : IsGradedEulerAdmissible.{w} k e X Y)
    (h' : IsGradedEulerAdmissible.{w} k e (e.inverse.obj X) Y) :
    gradedExtEuler k e h' = T 1 * gradedExtEuler k e h := by
  have hcounit : gradedExtEuler k e h = gradedExtEuler k e h'.shiftSource :=
    gradedExtEuler_of_iso k h h'.shiftSource (e.counitIso.app X).symm (Iso.refl Y)
  rw [hcounit, gradedExtEuler_shiftSource h' h'.shiftSource, ← mul_assoc, ← T_add]
  simp

end TauCeti
