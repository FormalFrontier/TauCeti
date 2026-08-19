/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
-- Private: `Module.Projective.exists_dual_eq_one` occurs only inside the proof that a nonzero
-- vector space carries a parity-swapping pair; it is not named by an exported statement.
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# An odd linear automorphism of a Clifford algebra

The two halves `evenOdd Q 0` and `evenOdd Q 1` of the `ℤ/2`-grading of a Clifford algebra are in
general only submodules, with nothing relating their sizes. They become isomorphic as soon as some
*odd* operator on `CliffordAlgebra Q` is invertible, because an odd operator carries each half into
the other.

The odd operator to use is already in Mathlib: `CliffordAlgebra.changeFormAux Q B e`, the
difference

`x ↦ ι Q e * x - (B e)⌋x`

of left Clifford multiplication by a vector — which is exterior multiplication only in the special
case `Q = 0`, since in general it squares to `Q e` rather than to `0` — and contraction against the
functional `B e`. Mathlib introduces it to build `CliffordAlgebra.changeForm` and proves there that
it squares to the scalar `Q e - B e e` (`CliffordAlgebra.changeFormAux_changeFormAux`): expanding
the square leaves the two cross terms `ι Q e * ((B e)⌋x)` and `(B e)⌋(ι Q e * x)`, and
`CliffordAlgebra.contractLeft_ι_mul` rewrites the second as `B e e • x - ι Q e * ((B e)⌋x)`, whose
second term cancels the first cross term while `B e e • x` survives; multiplication contributes
`Q e • x` by the Clifford relation and the contraction squares to `0`.

What Mathlib does not record is that the operator is *odd*, both of its summands being odd
(`CliffordAlgebra.map_evenOdd_changeFormAux_le`). So whenever `Q e - B e e` is a unit the operator
is a linear automorphism (`CliffordAlgebra.paritySwapEquiv`) exchanging the two halves of the
grading.

Both degenerate choices are useful. Taking `B = 0` recovers multiplication by an anisotropic
vector, the classical reason a nondegenerate Clifford algebra has equidimensional halves; taking
`Q = 0` — the exterior algebra, where *no* vector is anisotropic — leaves the contraction to do all
the work, and `Q e - B e e = -B e e` is a unit as soon as `B e` does not annihilate `e`. That
second case is the one that was missing: it is what makes the two half-spin summands `⋀ᵉᵛᵉⁿ W` and
`⋀ᵒᵈᵈ W` of a spinor module equidimensional.

Over a field the hypothesis is never an obstruction: a nonzero vector space always carries such a
pair (`QuadraticMap.exists_sub_bilinForm_eq_one`), since a nonzero vector is not annihilated by
every functional, and a rank-one bilinear form built from such a functional turns `Q e - B e e`
into `1`. Hence `CliffordAlgebra.nonempty_evenOddEquivAddOne`: over a field, the two halves of the
grading of the Clifford algebra of a nonzero space are isomorphic, *for every quadratic form*. The
dimension count that follows is `CliffordAlgebra.finrank_evenOdd` in
`TauCeti/LinearAlgebra/CliffordAlgebra/Dimension.lean`.

## Main definitions

* `CliffordAlgebra.paritySwapEquiv`: `CliffordAlgebra.changeFormAux` as a linear automorphism,
  when `Q e - B e e` is a unit.
* `CliffordAlgebra.evenOddEquivAddOne`: the induced isomorphism `evenOdd Q i ≃ₗ evenOdd Q (i + 1)`.

## Main results

* `CliffordAlgebra.map_evenOdd_changeFormAux_le`: the operator is odd.
* `CliffordAlgebra.map_evenOdd_paritySwapEquiv`: it carries `evenOdd Q i` *onto*
  `evenOdd Q (i + 1)`.
* `QuadraticMap.exists_sub_bilinForm_eq_one`: over a field, a nonzero vector space carries a vector
  and a bilinear form with `Q e - B e e = 1`.
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

open LinearMap (BilinForm)

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) (B : BilinForm R M) (e : M)

/-- **The parity-swapping operator is odd**: `CliffordAlgebra.changeFormAux` carries `evenOdd Q i`
into `evenOdd Q (i + 1)`, because both of its summands do — multiplication by a vector by the
grading, contraction by `CliffordAlgebra.contractLeft_mem_evenOdd`. -/
theorem map_evenOdd_changeFormAux_le (i : ZMod 2) :
    (evenOdd Q i).map (changeFormAux Q B e) ≤ evenOdd Q (i + 1) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [changeFormAux_apply_apply]
  refine sub_mem ?_ (contractLeft_mem_evenOdd (B e) hx)
  rw [add_comm i 1]
  exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q e) hx

variable {Q B e}

/-- **The parity-swapping automorphism**: `CliffordAlgebra.changeFormAux Q B e` read as a linear
automorphism, for a vector and a bilinear form whose scalar `Q e - B e e` is a unit. The inverse is
the same operator rescaled by the inverse of that unit, since the operator squares to it
(`CliffordAlgebra.changeFormAux_changeFormAux`). -/
noncomputable def paritySwapEquiv (h : IsUnit (Q e - B e e)) :
    CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q := by
  refine LinearEquiv.ofLinearMap (changeFormAux Q B e)
    ((↑h.unit⁻¹ : R) • changeFormAux Q B e) ?_ ?_ <;>
    · ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, map_smul,
        changeFormAux_changeFormAux, smul_smul, h.val_inv_mul, one_smul, LinearMap.id_coe, id_eq]

/-- The parity-swapping automorphism is the operator it is built from. -/
@[simp]
theorem paritySwapEquiv_apply (h : IsUnit (Q e - B e e)) (x : CliffordAlgebra Q) :
    paritySwapEquiv h x = changeFormAux Q B e x := by
  rw [paritySwapEquiv, LinearEquiv.coe_ofLinearMap]

/-- The parity-swapping automorphism is the operator it is built from, as linear maps: the bridge
that lets a statement about `CliffordAlgebra.changeFormAux` be read off one about
`CliffordAlgebra.paritySwapEquiv`, and conversely. -/
theorem paritySwapEquiv_toLinearMap (h : IsUnit (Q e - B e e)) :
    (paritySwapEquiv h).toLinearMap = changeFormAux Q B e := by
  ext x
  rw [LinearEquiv.coe_coe, paritySwapEquiv_apply]

/-- The inverse of `CliffordAlgebra.paritySwapEquiv` is the same operator rescaled by the inverse
of the unit it squares to. -/
@[simp]
theorem paritySwapEquiv_symm_apply (h : IsUnit (Q e - B e e)) (x : CliffordAlgebra Q) :
    (paritySwapEquiv h).symm x = (↑h.unit⁻¹ : R) • changeFormAux Q B e x := by
  rw [paritySwapEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.smul_apply]

/-- **The parity-swapping automorphism exchanges the two halves of the grading.** The inclusion
`≤` is oddness; the reverse holds because the preimage of `y` is a scalar multiple of
`changeFormAux Q B e y`, which lies in `evenOdd Q (i + 1 + 1) = evenOdd Q i`. -/
theorem map_evenOdd_paritySwapEquiv (h : IsUnit (Q e - B e e)) (i : ZMod 2) :
    (evenOdd Q i).map (paritySwapEquiv h).toLinearMap = evenOdd Q (i + 1) := by
  have hi : i + 1 + 1 = i := by revert i; decide
  rw [paritySwapEquiv_toLinearMap]
  refine le_antisymm (map_evenOdd_changeFormAux_le Q B e i) fun y hy => ?_
  refine ⟨(paritySwapEquiv h).symm y, ?_, ?_⟩
  · rw [paritySwapEquiv_symm_apply]
    refine Submodule.smul_mem _ _ ?_
    simpa only [hi] using map_evenOdd_changeFormAux_le Q B e (i + 1) (Submodule.mem_map_of_mem hy)
  · rw [← paritySwapEquiv_apply h, (paritySwapEquiv h).apply_symm_apply]

/-- **The two halves of the `ℤ/2`-grading are isomorphic**, for a vector and a bilinear form whose
scalar `Q e - B e e` is a unit: the parity-swapping automorphism restricts to an isomorphism
between them. -/
noncomputable def evenOddEquivAddOne (h : IsUnit (Q e - B e e)) (i : ZMod 2) :
    evenOdd Q i ≃ₗ[R] evenOdd Q (i + 1) :=
  (Submodule.equivMapOfInjective _ (paritySwapEquiv h).injective _).trans
    (LinearEquiv.ofEq _ _ (map_evenOdd_paritySwapEquiv h i))

/-- The isomorphism between the two halves of the grading is the parity-swapping operator, read
inside the Clifford algebra. -/
@[simp]
theorem coe_evenOddEquivAddOne_apply (h : IsUnit (Q e - B e e)) (i : ZMod 2) (x : evenOdd Q i) :
    (evenOddEquivAddOne h i x : CliffordAlgebra Q)
      = changeFormAux Q B e (x : CliffordAlgebra Q) := by
  rw [evenOddEquivAddOne, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_coe, paritySwapEquiv_apply]

/-- The inverse of the isomorphism between the two halves of the grading is the parity-swapping
operator rescaled by the inverse of the unit it squares to, read inside the Clifford algebra. -/
@[simp]
theorem coe_evenOddEquivAddOne_symm_apply (h : IsUnit (Q e - B e e)) (i : ZMod 2)
    (y : evenOdd Q (i + 1)) :
    ((evenOddEquivAddOne h i).symm y : CliffordAlgebra Q)
      = (↑h.unit⁻¹ : R) • changeFormAux Q B e (y : CliffordAlgebra Q) := by
  have hy : changeFormAux Q B e ((evenOddEquivAddOne h i).symm y : CliffordAlgebra Q)
      = (y : CliffordAlgebra Q) := by
    rw [← coe_evenOddEquivAddOne_apply h i, (evenOddEquivAddOne h i).apply_symm_apply]
  rw [← hy, changeFormAux_changeFormAux, smul_smul, h.val_inv_mul, one_smul]

end CommRing

end CliffordAlgebra

namespace QuadraticMap

/-- **A nonzero vector space carries a parity-swapping pair, for every quadratic form.** Choose a
nonzero vector `e` and a functional `f` with `f e = 1`; the rank-one bilinear form
`B = f ⊗ (Q e - 1) • f` then has `B e e = Q e - 1`.

This is what frees `CliffordAlgebra.evenOddEquivAddOne` from any hypothesis on `Q`: the classical
choice `B = 0` needs an anisotropic vector, which an exterior algebra has none of, while here the
contraction supplies the missing unit. -/
theorem exists_sub_bilinForm_eq_one {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] [Nontrivial V] (Q : QuadraticForm K V) :
    ∃ (e : V) (B : BilinForm K V), Q e - B e e = 1 := by
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K he
  refine ⟨e, f.smulRight ((Q e - 1) • f), ?_⟩
  simp [hf]

end QuadraticMap

namespace CliffordAlgebra

/-- **Over a field the two halves of the `ℤ/2`-grading of the Clifford algebra of a nonzero space
are isomorphic**, for every quadratic form — in particular for the zero form, where the algebra is
the exterior algebra and the halves are the even and the odd exterior powers.

The isomorphism is not canonical: it depends on the parity-swapping pair chosen by
`QuadraticMap.exists_sub_bilinForm_eq_one`, so it is produced as a `Nonempty`. -/
theorem nonempty_evenOddEquivAddOne {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] [Nontrivial V] (Q : QuadraticForm K V) (i : ZMod 2) :
    Nonempty (evenOdd Q i ≃ₗ[K] evenOdd Q (i + 1)) := by
  obtain ⟨e, B, heB⟩ := Q.exists_sub_bilinForm_eq_one
  exact ⟨evenOddEquivAddOne (heB ▸ isUnit_one) i⟩

end CliffordAlgebra
