import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Class sums in a finite group algebra

This file defines the element of a group algebra obtained by summing the members of a conjugacy
class.  It proves that every class sum is central, the first input to the class-algebra side of
finite-group character theory.
-/

namespace TauCeti

open scoped BigOperators

variable {k G : Type*} [CommRing k] [Group G] [Fintype G] [DecidableEq G]

/-- The sum in `k[G]` of the elements in the conjugacy class `C`. -/
noncomputable def classSum (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ x : C.carrier, MonoidAlgebra.of k G x

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
theorem classSum_commutes_of (C : ConjClasses G) (g : G) :
    classSum (k := k) C * MonoidAlgebra.of k G g =
      MonoidAlgebra.of k G g * classSum (k := k) C := by
  rw [classSum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of k G).map_mul]
  rw [← (conjugateCarrierEquiv g C).sum_comp fun x => MonoidAlgebra.of k G (x * g)]
  congr 1
  ext x
  simp [conjugateCarrierEquiv, mul_assoc]

/-- Every class sum lies in the center of the group algebra. -/
theorem classSum_mem_center (C : ConjClasses G) :
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
