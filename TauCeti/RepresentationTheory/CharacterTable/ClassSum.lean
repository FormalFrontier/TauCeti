module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Class sums in a finite group algebra

This file defines the element of a group algebra obtained by summing the members of a conjugacy
class.  It proves that every class sum is central, the first input to the class-algebra side of
finite-group character theory.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {k G : Type*} [Group G] [Fintype G] [DecidableEq G]

section

/-- The sum in `k[G]` of the elements in the conjugacy class `C`. -/
noncomputable def classSum [Semiring k] (C : ConjClasses G) : MonoidAlgebra k G := by
  classical
  by_cases h : Nontrivial k
  · letI : Nontrivial k := h
    exact
      { coeff :=
          { support := Finset.univ.filter (fun x => ConjClasses.mk x = C)
            toFun := fun x => if ConjClasses.mk x = C then 1 else 0
            mem_support_toFun := by simp } }
  · exact 0

/-- The computable class sum, when equality of coefficients is decidable. -/
def classSumOfDecidableEq [Semiring k] [DecidableEq k] (C : ConjClasses G) : MonoidAlgebra k G :=
  { coeff :=
      { support :=
          Finset.univ.filter (fun x =>
            (if ConjClasses.mk x = C then 1 else 0 : k) ≠ 0)
        toFun := fun x => if ConjClasses.mk x = C then 1 else 0
        mem_support_toFun := by simp } }

/-- A class sum is the sum of the basis elements in its conjugacy class. -/
theorem classSum_eq_sum [Semiring k] (C : ConjClasses G) :
    classSum (k := k) C = ∑ x : C.carrier, MonoidAlgebra.of k G x := by
  classical
  by_cases hk : Nontrivial k
  · letI : Nontrivial k := hk
    have sum_apply (f : C.carrier → G →₀ k) (x : G) :
        (∑ i, f i) x = ∑ i, f i x := by
      change ((Finset.univ : Finset C.carrier).sum f) x =
        (Finset.univ : Finset C.carrier).sum fun i => f i x
      induction (Finset.univ : Finset C.carrier) using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => simp [ha, Finsupp.add_apply, ih]
    ext x
    rw [MonoidAlgebra.coeff_sum]
    rw [sum_apply]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [classSum, dif_pos hk, MonoidAlgebra.coeff_ofCoeff]
    simp only [Finsupp.coe_mk]
    change (if ConjClasses.mk x = C then 1 else 0) =
      ∑ i : C.carrier, if (i : G) = x then 1 else 0
    by_cases hx : ConjClasses.mk x = C
    · let xc : C.carrier := ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr hx⟩
      rw [if_pos hx]
      rw [Finset.sum_eq_single xc]
      · simp [xc]
      · intro b _ hbx
        rw [if_neg]
        intro h
        apply hbx
        ext
        simpa [xc] using h
      · simp
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg]
      intro h
      exact hx (by rw [← h]; exact ConjClasses.mem_carrier_iff_mk_eq.mp c.property)
  · haveI : Subsingleton k := not_nontrivial_iff_subsingleton.mp hk
    exact Subsingleton.elim _ _

/-- Conjugation by `g` permutes every conjugacy class. -/
def conjugateCarrierEquiv (g : G) (C : ConjClasses G) : C.carrier ≃ C.carrier where
  toFun x := ⟨g * x * g⁻¹, by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    have hx := ConjClasses.mem_carrier_iff_mk_eq.mp x.property
    apply Eq.trans _ hx
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact isConj_iff.mpr ⟨g⁻¹, by simp [mul_assoc]⟩⟩
  invFun x := ⟨g⁻¹ * x * g, by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    have hx := ConjClasses.mem_carrier_iff_mk_eq.mp x.property
    apply Eq.trans _ hx
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact isConj_iff.mpr ⟨g, by simp [mul_assoc]⟩⟩
  left_inv x := by
    ext
    simp [mul_assoc]
  right_inv x := by
    ext
    simp [mul_assoc]

/-- A class sum commutes with each group element in the group algebra. -/
theorem classSum_commutes_of [Semiring k] (C : ConjClasses G) (g : G) :
    classSum (k := k) C * MonoidAlgebra.of k G g =
      MonoidAlgebra.of k G g * classSum (k := k) C := by
  rw [classSum_eq_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of k G).map_mul]
  rw [← (conjugateCarrierEquiv g C).sum_comp fun x => MonoidAlgebra.of k G (x * g)]
  congr 1
  ext x
  simp [conjugateCarrierEquiv, mul_assoc]

end

/-- Every class sum lies in the center of the group algebra. -/
theorem classSum_mem_center [CommSemiring k] (C : ConjClasses G) :
    classSum (k := k) C ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact (classSum_commutes_of (k := k) C g).symm
  | hadd x y hx hy =>
    rw [mul_add, add_mul, hx, hy]
  | hsmul r x hx =>
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]

end TauCeti
