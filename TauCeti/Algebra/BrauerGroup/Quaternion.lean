/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.BrauerGroup.Splitting` is imported publicly: `TauCeti.BrauerGroup.mk` and
-- `TauCeti.CSA.of` occur in the statements below, and it supplies
-- `TauCeti.BrauerGroup.mk_eq_one_iff_finrank_eq_one`, which makes the class of `ℍ[ℝ]` nonidentity
-- and so turns the divisibility `orderOf ∣ 2` into an equality. It re-exports the whole
-- Brauer-group stack, hence `CSA`, `BrauerGroup`,
-- `TauCeti.BrauerGroup.orderOf_mk_eq_two_of_algEquiv_op` and `TauCeti.Algebra.IsSplittingField`,
-- and with the order results Mathlib's `orderOf`, which occurs in the statement of the order
-- computation below; that is why `Mathlib.GroupTheory.OrderOfElement` is not imported again here.
public import TauCeti.Algebra.BrauerGroup.Splitting
-- `TauCeti.Algebra.CentralSimple.Quaternion` is imported publicly because `ℍ[ℝ]` occurs in every
-- statement below; it re-exports `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation and
-- quaternion conjugation `Quaternion.starAe`, and `TauCeti.Quaternion.instIsCentral`, which is what
-- puts `ℍ[ℝ]` in the scope of the Brauer-group API at all.
public import TauCeti.Algebra.CentralSimple.Quaternion
-- Non-public: the base-change homomorphism and the fundamental theorem of algebra are used only by
-- the worked examples closing the file, so downstream importers do not pay for them.
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.BrauerGroup.BaseChange

/-!
# The Brauer class of the real quaternions has order two

This file applies the general Brauer-group API to the real quaternions. Quaternion conjugation
identifies `ℍ[ℝ]` with its opposite algebra, so its Brauer class is self-inverse; and `ℍ[ℝ]` is a
central division algebra of dimension `4`, so that class is not the identity
(`TauCeti.BrauerGroup.mk_eq_one_iff_finrank_eq_one`). Together these say the class has order exactly
`2`, and in particular `BrauerGroup ℝ` is not trivial. Complexification kills the class, in the two
ways `TauCeti/Algebra/BrauerGroup/BaseChange.lean` offers, so the kernel of base change to `ℂ` is
strictly larger than the trivial subgroup.

What is *not* proved here is that `[ℍ[ℝ]]` **generates** `BrauerGroup ℝ`, that is, that
`BrauerGroup ℝ ≃ ℤ/2`. That needs the classification of the finite-dimensional real division
algebras with centre `ℝ` -- only `ℝ` and `ℍ[ℝ]` occur -- which is a separate long-term target.

## Main results

* `TauCeti.Quaternion.mk_ne_one`: the Brauer class of `ℍ[ℝ]` is not the identity.
* `TauCeti.Quaternion.orderOf_mk_eq_two`: **that class has order exactly `2`**, so `BrauerGroup ℝ`
  contains a copy of `ℤ/2`; `TauCeti.Quaternion.nontrivial_brauerGroup` is the qualitative form.

## References

This is the Brauer-group half of the Hamilton-quaternion worked example of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md)
("`ℍ[ℝ] ⊗_ℝ ℍ[ℝ] ≃ M₄(ℝ)`, so `[ℍ]` has order 2"), whose algebra half is
`TauCeti/Algebra/CentralSimple/Quaternion.lean`. See P. Gille, T. Szamuely, *Central Simple Algebras
and Galois Cohomology*, CUP (2006), §1.1 and §2.4.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace Quaternion

/-- **The Brauer class of the real quaternions is not the identity.** `ℍ[ℝ]` is a central division
algebra over `ℝ` of dimension `4`, and a central division algebra has the identity class only when
it is one-dimensional, that is, only when it is the base field. -/
theorem mk_ne_one : BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ≠ 1 := fun h ↦ by
  have h4 := (BrauerGroup.mk_eq_one_iff_finrank_eq_one ℝ ℍ[ℝ]).1 h
  rw [_root_.Quaternion.finrank_eq_four] at h4
  norm_num at h4

/-- **The Brauer class of the real quaternions has order exactly `2`.**

Quaternion conjugation is an `ℝ`-algebra isomorphism `ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (Mathlib's
`Quaternion.starAe`), so the class is its own inverse and its order divides `2`; concretely that
self-inverseness is the isomorphism `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₄(ℝ)` of
`TauCeti.Quaternion.tensorSelfAlgEquivMatrix`. It is not order `1` because the class is not the
identity (`TauCeti.Quaternion.mk_ne_one`). -/
theorem orderOf_mk_eq_two : orderOf (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])) = 2 :=
  BrauerGroup.orderOf_mk_eq_two_of_algEquiv_op _root_.Quaternion.starAe mk_ne_one

/-- **The Brauer group of the reals is not trivial**, witnessed by the class of `ℍ[ℝ]`. Contrast
`TauCeti.subsingleton_brauerGroup_of_isAlgClosed` and
`TauCeti.subsingleton_brauerGroup_of_finite`: over `ℝ` there is a central division algebra other
than the base field, so the Brauer group has something in it.

The universes are pinned because `BrauerGroup.{u, v}` carries its group structure, hence its
identity element, only for `v = u`. -/
theorem nontrivial_brauerGroup : Nontrivial (BrauerGroup.{0, 0} ℝ) :=
  ⟨⟨BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]), 1, mk_ne_one⟩⟩

end Quaternion

/-! ### Worked examples -/

section Examples

/-- **The Brauer class of the real quaternions is its own inverse.** Quaternion conjugation is an
`ℝ`-algebra isomorphism `ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (Mathlib's `Quaternion.starAe`), so this is
`TauCeti.BrauerGroup.inv_mk_eq_mk_of_algEquiv_op`; concretely it is the isomorphism
`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₄(ℝ)` of `TauCeti.Quaternion.tensorSelfAlgEquivMatrix`. -/
example : (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]))⁻¹ = BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) :=
  BrauerGroup.inv_mk_eq_mk_of_algEquiv_op _root_.Quaternion.starAe

/-- **Complexification kills the Brauer class of the real quaternions**, because `ℂ` is
algebraically closed and so has trivial Brauer group.

By `TauCeti.Quaternion.mk_ne_one` this is a *nontrivial* class being killed, so the kernel of
`TauCeti.BrauerGroup.baseChange ℝ ℂ` is strictly larger than the trivial subgroup: `ℍ[ℝ]` is not
already split over `ℝ`. -/
example : BrauerGroup.baseChange ℝ ℂ (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])) = 1 := by
  rw [BrauerGroup.baseChange_eq_one_of_isAlgClosed, MonoidHom.one_apply]

/-- The same class, killed through the splitting field rather than through the triviality of
`BrauerGroup ℂ`: `TauCeti.Algebra.isSplittingField_of_isAlgClosed` says `ℂ` splits every
finite-dimensional central simple `ℝ`-algebra, and a split algebra lies in the kernel. -/
example : BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ∈ (BrauerGroup.baseChange ℝ ℂ).ker :=
  BrauerGroup.mk_mem_ker_baseChange_of_isSplittingField ℝ ℂ
    (Algebra.isSplittingField_of_isAlgClosed ℝ ℍ[ℝ] ℂ)

/-- `ℝ` does not split `ℍ[ℝ]`: the class of `ℍ[ℝ]` is not the identity, and by
`TauCeti.BrauerGroup.mk_eq_one_iff_isSplittingField` those two statements are the same one. -/
example : ¬ Algebra.IsSplittingField ℝ ℍ[ℝ] ℝ := fun h ↦
  Quaternion.mk_ne_one ((BrauerGroup.mk_eq_one_iff_isSplittingField ℝ ℍ[ℝ]).2 h)

end Examples

end TauCeti
