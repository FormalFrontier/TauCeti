/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
-- Private: `LinearMap.mulLeft` occurs only in the body of `CliffordAlgebra.paritySwap`, and
-- `Module.forall_dual_apply_eq_zero_iff` only inside the proof that a nonzero vector space
-- carries a parity-swapping pair; neither is named by an exported statement.
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# An odd automorphism of a Clifford algebra

The two halves `evenOdd Q 0` and `evenOdd Q 1` of the `ℤ/2`-grading of a Clifford algebra are in
general only submodules, with nothing relating their sizes. They become isomorphic as soon as some
*odd* operator on `CliffordAlgebra Q` is invertible, because an odd operator carries each half into
the other.

This file builds such an operator out of the two elementary odd operators there are: exterior
multiplication by a vector, `x ↦ ι Q e * x`, and contraction against a linear functional,
`x ↦ d⌋x`. Their sum

`paritySwap Q e d : x ↦ ι Q e * x + d⌋x`

squares to the scalar `Q e + d e` (`CliffordAlgebra.paritySwap_paritySwap`), because the two cross
terms cancel by `CliffordAlgebra.contractLeft_ι_mul` while each operator squares to `Q e`
respectively `0`. So whenever `Q e + d e` is a unit the operator is a linear automorphism, and it
exchanges the two halves of the grading.

Both degenerate choices are useful. Taking `d = 0` recovers multiplication by an anisotropic
vector, the classical reason a nondegenerate Clifford algebra has equidimensional halves; taking
`Q = 0` — the exterior algebra, where *no* vector is anisotropic — leaves the contraction to do all
the work, and `Q e + d e = d e` is a unit as soon as `d` does not annihilate `e`. That second case
is the one that was missing: it is what makes the two half-spin summands `⋀ᵉᵛᵉⁿ W` and `⋀ᵒᵈᵈ W` of
a spinor module equidimensional.

Over a field the hypothesis is never an obstruction: a nonzero vector space always carries such a
pair (`CliffordAlgebra.exists_quadraticForm_add_dual_eq_one`), since a nonzero vector is not
annihilated by every functional, and rescaling that functional turns `Q e + d e` into `1`.  Hence
`CliffordAlgebra.nonempty_evenOddEquivAddOne`: over a field, the two halves of the grading of the
Clifford algebra of a nonzero space are isomorphic, *for every quadratic form*. The dimension count
that follows is `CliffordAlgebra.finrank_evenOdd` in
`TauCeti/LinearAlgebra/CliffordAlgebra/Dimension.lean`.

## Main definitions

* `CliffordAlgebra.paritySwap`: the operator `x ↦ ι Q e * x + d⌋x`.
* `CliffordAlgebra.paritySwapEquiv`: that operator as a linear automorphism, when `Q e + d e` is a
  unit.
* `CliffordAlgebra.evenOddEquivAddOne`: the induced isomorphism `evenOdd Q i ≃ₗ evenOdd Q (i + 1)`.

## Main results

* `CliffordAlgebra.paritySwap_paritySwap`: the operator squares to the scalar `Q e + d e`.
* `CliffordAlgebra.map_evenOdd_paritySwapEquiv`: it carries `evenOdd Q i` *onto*
  `evenOdd Q (i + 1)`.
* `CliffordAlgebra.exists_quadraticForm_add_dual_eq_one`: over a field, a nonzero vector space
  carries a vector and a functional with `Q e + d e = 1`.
* `CliffordAlgebra.nonempty_evenOddEquivAddOne`: over a field, the two halves of the grading of the
  Clifford algebra of a nonzero space are isomorphic.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II, for the exterior
  multiplication and contraction operators and the Clifford relation between them.
* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 5, "The half-spin representation of `𝔰𝔬(2l)` has dimension `2^{l-1}`", whose dimension
  count this supplies.
-/

public section

universe u v

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) (e : M) (d : Module.Dual R M)

/-- **The parity-swapping operator** `x ↦ ι Q e * x + d⌋x`, the sum of exterior multiplication by
a vector and contraction against a linear functional.

Both summands are odd, so the sum is odd: it carries `evenOdd Q i` into `evenOdd Q (i + 1)`
(`CliffordAlgebra.map_evenOdd_paritySwap_le`). It squares to the scalar `Q e + d e`
(`CliffordAlgebra.paritySwap_paritySwap`), hence is invertible whenever that scalar is a unit
(`CliffordAlgebra.paritySwapEquiv`). -/
noncomputable def paritySwap : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  LinearMap.mulLeft R (ι Q e) + contractLeft d

/-- The parity-swapping operator, applied to an element. -/
@[simp]
theorem paritySwap_apply (x : CliffordAlgebra Q) :
    paritySwap Q e d x = ι Q e * x + contractLeft d x :=
  -- `(rfl)`, not `rfl`: the body of `paritySwap` is not `@[expose]`d.
  (rfl)

/-- **The parity-swapping operator squares to a scalar.** The two cross terms
`ι Q e * (d⌋x)` cancel by `CliffordAlgebra.contractLeft_ι_mul`, exterior multiplication squares to
`Q e` by the Clifford relation, and contraction squares to `0`. -/
theorem paritySwap_paritySwap (x : CliffordAlgebra Q) :
    paritySwap Q e d (paritySwap Q e d x) = (Q e + d e) • x := by
  rw [paritySwap_apply, paritySwap_apply, mul_add, map_add, contractLeft_ι_mul,
    contractLeft_contractLeft, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, add_smul]
  abel

/-- The parity-swapping operator is odd: it carries `evenOdd Q i` into `evenOdd Q (i + 1)`. -/
theorem map_evenOdd_paritySwap_le (i : ZMod 2) :
    (evenOdd Q i).map (paritySwap Q e d) ≤ evenOdd Q (i + 1) := by
  rintro _ ⟨x, hx, rfl⟩
  refine add_mem ?_ (contractLeft_mem_evenOdd d hx)
  rw [add_comm i 1]
  exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q e) hx

variable {Q e d}

/-- The parity-swapping operator as a **linear automorphism**, for a vector and a functional whose
scalar `Q e + d e` is a unit. The inverse is the same operator rescaled by that unit, since the
operator squares to it. -/
noncomputable def paritySwapEquiv (h : IsUnit (Q e + d e)) :
    CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q := by
  refine LinearEquiv.ofLinearMap (paritySwap Q e d) ((↑h.unit⁻¹ : R) • paritySwap Q e d) ?_ ?_ <;>
    · ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, map_smul,
        paritySwap_paritySwap, smul_smul, h.val_inv_mul, one_smul, LinearMap.id_coe, id_eq]

/-- The parity-swapping automorphism is the parity-swapping operator. -/
@[simp]
theorem paritySwapEquiv_apply (h : IsUnit (Q e + d e)) (x : CliffordAlgebra Q) :
    paritySwapEquiv h x = ι Q e * x + contractLeft d x :=
  -- `(rfl)`, not `rfl`: the body of `paritySwapEquiv` is not `@[expose]`d.
  (rfl)

/-- The inverse of `CliffordAlgebra.paritySwapEquiv` is the same operator rescaled by the inverse
of the unit it squares to. -/
@[simp]
theorem paritySwapEquiv_symm_apply (h : IsUnit (Q e + d e)) (x : CliffordAlgebra Q) :
    (paritySwapEquiv h).symm x = (↑h.unit⁻¹ : R) • (ι Q e * x + contractLeft d x) :=
  -- `(rfl)`, not `rfl`: the body of `paritySwapEquiv` is not `@[expose]`d.
  (rfl)

/-- **The parity-swapping automorphism exchanges the two halves of the grading.** The inclusion
`≤` is oddness; the reverse holds because the preimage of `y` is a scalar multiple of
`paritySwap Q e d y`, which lies in `evenOdd Q (i + 1 + 1) = evenOdd Q i`. -/
theorem map_evenOdd_paritySwapEquiv (h : IsUnit (Q e + d e)) (i : ZMod 2) :
    (evenOdd Q i).map (paritySwapEquiv h).toLinearMap = evenOdd Q (i + 1) := by
  have hi : i + 1 + 1 = i := by revert i; decide
  refine le_antisymm (map_evenOdd_paritySwap_le Q e d i) fun y hy => ?_
  refine ⟨(paritySwapEquiv h).symm y, ?_, (paritySwapEquiv h).apply_symm_apply y⟩
  rw [paritySwapEquiv_symm_apply]
  refine Submodule.smul_mem _ _ ?_
  have := map_evenOdd_paritySwap_le Q e d (i + 1) (Submodule.mem_map_of_mem hy)
  rwa [hi, paritySwap_apply] at this

/-- **The two halves of the `ℤ/2`-grading are isomorphic**, for a vector and a functional whose
scalar `Q e + d e` is a unit: the parity-swapping automorphism restricts to an isomorphism between
them. -/
noncomputable def evenOddEquivAddOne (h : IsUnit (Q e + d e)) (i : ZMod 2) :
    evenOdd Q i ≃ₗ[R] evenOdd Q (i + 1) :=
  (Submodule.equivMapOfInjective _ (paritySwapEquiv h).injective _).trans
    (LinearEquiv.ofEq _ _ (map_evenOdd_paritySwapEquiv h i))

/-- The isomorphism between the two halves of the grading is the parity-swapping operator, read
inside the Clifford algebra. -/
@[simp]
theorem coe_evenOddEquivAddOne_apply (h : IsUnit (Q e + d e)) (i : ZMod 2) (x : evenOdd Q i) :
    (evenOddEquivAddOne h i x : CliffordAlgebra Q)
      = ι Q e * (x : CliffordAlgebra Q) + contractLeft d (x : CliffordAlgebra Q) :=
  -- `(rfl)`, not `rfl`: the body of `evenOddEquivAddOne` is not `@[expose]`d.
  (rfl)

/-- The inverse of the isomorphism between the two halves of the grading is the parity-swapping
operator rescaled by the inverse of the unit it squares to, read inside the Clifford algebra. It
is not `rfl`: `Submodule.equivMapOfInjective` inverts through the chosen inverse of an injection,
so the inverse is instead identified by applying the operator to
`CliffordAlgebra.coe_evenOddEquivAddOne_apply`. -/
@[simp]
theorem coe_evenOddEquivAddOne_symm_apply (h : IsUnit (Q e + d e)) (i : ZMod 2)
    (y : evenOdd Q (i + 1)) :
    ((evenOddEquivAddOne h i).symm y : CliffordAlgebra Q) = (↑h.unit⁻¹ : R) •
      (ι Q e * (y : CliffordAlgebra Q) + contractLeft d (y : CliffordAlgebra Q)) := by
  have hy : paritySwap Q e d ((evenOddEquivAddOne h i).symm y : CliffordAlgebra Q)
      = (y : CliffordAlgebra Q) := by
    rw [paritySwap_apply, ← coe_evenOddEquivAddOne_apply h i,
      (evenOddEquivAddOne h i).apply_symm_apply]
  rw [← paritySwap_apply, ← hy, paritySwap_paritySwap, smul_smul, h.val_inv_mul, one_smul]

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- **A nonzero vector space carries a parity-swapping pair, for every quadratic form.** Choose a
nonzero vector `e`; some functional does not annihilate it, and rescaling that functional makes
`Q e + d e` equal to `1`.

This is what frees `CliffordAlgebra.evenOddEquivAddOne` from any hypothesis on `Q`: the classical
choice `d = 0` needs an anisotropic vector, which an exterior algebra has none of, while here the
contraction supplies the missing unit. -/
theorem exists_quadraticForm_add_dual_eq_one [Nontrivial V] (Q : QuadraticForm K V) :
    ∃ (e : V) (d : Module.Dual K V), Q e + d e = 1 := by
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := not_forall.1 fun h : ∀ φ : Module.Dual K V, φ e = 0 =>
    he ((Module.forall_dual_apply_eq_zero_iff K e).1 h)
  refine ⟨e, ((1 - Q e) / f e) • f, ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hf]
  ring

/-- **Over a field the two halves of the `ℤ/2`-grading of the Clifford algebra of a nonzero space
are isomorphic**, for every quadratic form — in particular for the zero form, where the algebra is
the exterior algebra and the halves are the even and the odd exterior powers.

The isomorphism is not canonical: it depends on the parity-swapping pair chosen by
`CliffordAlgebra.exists_quadraticForm_add_dual_eq_one`, so it is produced as a `Nonempty`. -/
theorem nonempty_evenOddEquivAddOne [Nontrivial V] (Q : QuadraticForm K V) (i : ZMod 2) :
    Nonempty (evenOdd Q i ≃ₗ[K] evenOdd Q (i + 1)) := by
  obtain ⟨e, d, hed⟩ := exists_quadraticForm_add_dual_eq_one Q
  exact ⟨evenOddEquivAddOne (hed ▸ isUnit_one) i⟩

end Field

end CliffordAlgebra
