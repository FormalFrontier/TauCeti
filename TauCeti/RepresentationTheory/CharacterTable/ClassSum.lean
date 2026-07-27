module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
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
noncomputable def classSum [Semiring k] (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ x : C.carrier, MonoidAlgebra.of k G x

/-- A class sum is the sum of the basis elements in its conjugacy class. -/
theorem classSum_eq_sum [Semiring k] (C : ConjClasses G) :
    classSum (k := k) C = ∑ x : C.carrier, MonoidAlgebra.of k G x := by
  rfl

/-- The coefficient of `g` in the class sum of `C` is `1` if `g` lies in `C`, and `0` otherwise. -/
@[simp]
theorem classSum_coeff [Semiring k] (C : ConjClasses G) (g : G) :
    (classSum (k := k) C).coeff g = if ConjClasses.mk g = C then 1 else 0 := by
  rw [classSum_eq_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : ConjClasses.mk g = C
  · rw [if_pos hg,
      Finset.sum_eq_single (⟨g, ConjClasses.mem_carrier_iff_mk_eq.mpr hg⟩ : C.carrier)]
    · simp
    · exact fun b _ hb => if_neg fun h => hb (Subtype.ext h)
    · simp
  · rw [if_neg hg]
    refine Finset.sum_eq_zero fun c _ => if_neg fun h => hg ?_
    rw [← h]
    exact ConjClasses.mem_carrier_iff_mk_eq.mp c.property

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

omit [Fintype G] [DecidableEq G] in
/-- `conjugateCarrierEquiv g C` sends `x` to its conjugate `g * x * g⁻¹`. -/
@[simp]
theorem conjugateCarrierEquiv_apply (g : G) (C : ConjClasses G) (x : C.carrier) :
    (conjugateCarrierEquiv g C x : G) = g * x * g⁻¹ := by
  simp [conjugateCarrierEquiv]

/-- A class sum commutes with each group element in the group algebra. -/
theorem classSum_commutes [Semiring k] (C : ConjClasses G) (g : G) :
    classSum (k := k) C * MonoidAlgebra.of k G g =
      MonoidAlgebra.of k G g * classSum (k := k) C := by
  rw [classSum_eq_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of k G).map_mul]
  rw [← (conjugateCarrierEquiv g C).sum_comp fun x => MonoidAlgebra.of k G (x * g)]
  congr 1
  ext x
  simp [mul_assoc]

end

/-- Every class sum lies in the center of the group algebra. -/
theorem classSum_mem_center [CommSemiring k] (C : ConjClasses G) :
    classSum (k := k) C ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact (classSum_commutes (k := k) C g).symm
  | hadd x y hx hy =>
    rw [mul_add, add_mul, hx, hy]
  | hsmul r x hx =>
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]

end TauCeti
