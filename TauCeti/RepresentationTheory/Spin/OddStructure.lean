/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.OddSplitting
public import TauCeti.RepresentationTheory.Spin.Structure
-- Non-public: the coordinate surjection out of a product, the simplicity of a matrix algebra, the
-- finite-dimensional injectivity criterion and the anisotropic orthogonal basis carrying the
-- volume element are all used only inside proofs.
import TauCeti.RingTheory.CentralIdempotent
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The structure theorem for an odd-dimensional Clifford algebra

Over a separably closed field of characteristic not two, the Clifford algebra of a nondegenerate
quadratic form on a space of dimension `2 * l + 1` is a **product of two matrix algebras**,

`CliffordAlgebra Q ≃ₐ[F] M_{2^l}(F) × M_{2^l}(F)`.

Two results already in place bracket this statement, and the file supplies what joins them. The
volume element of an orthogonal basis of odd length is central, odd, and squares to a nonzero
scalar, so after rescaling it splits the algebra as two copies of its even subalgebra
(`CliffordAlgebra.nonempty_algEquiv_even_prod_of_odd_finrank`); and the Fock action of a
polarization is onto the endomorphism algebra of the spinor module `S = ⋀·W`
(`TauCeti.spinAction_surjective`), which in dimension `2 * l + 1` has dimension `2 ^ l`. What was
missing was the identification of the even subalgebra itself with `M_{2^l}(F)`, and that is the
substance here.

The argument avoids reducing an odd-dimensional form to an even-dimensional one. Write
`A = even Q`, so that the splitting is a surjection `A × A ↠ M_{2^l}(F)` obtained by following it
with the Fock action. The image of `(1, 0)` is a central idempotent of a simple ring, hence `0` or
`1` (`TauCeti.centralIdempotents_eq_pair`), and in either case one of the two coordinate maps
`a ↦ φ (a, 0)`, `a ↦ φ (0, a)` is already a surjective algebra map `A →ₐ[F] M_{2^l}(F)`: that is
`TauCeti.exists_algHom_surjective_of_prod`. A dimension count closes it. The even subalgebra has
half the dimension of the whole (`CliffordAlgebra.finrank_even`), so
`dim A = 2 ^ (2 * l + 1 - 1) = 2 ^ l · 2 ^ l` is the dimension of the target and the surjection is
injective as well.

The splitting itself is general Clifford-algebra theory and lives with the rest of it, in
`TauCeti/LinearAlgebra/CliffordAlgebra/OddSplitting.lean`.

The isomorphisms are not canonical — they depend on a choice of orthogonal basis, of polarization,
and of a basis of the spinor module — so the statements are `Nonempty`, as the even-dimensional
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul` is.

Once a polarization *is* fixed there is a canonical isomorphism to be had, and the last section
records it. Only the basis of the spinor module was arbitrary above, so dropping it leaves the
Fock action itself: `TauCeti.evenSpinAction` is a bijection from `even Q` onto
`Module.End F (⋀·W)`. That needs neither the matrix identification nor a separably closed field.
The whole Fock action is onto (`TauCeti.spinAction_surjective`), and in odd dimension the even
half already reaches as far: the volume element `ω` is central, so its image commutes with all of
`Module.End F (⋀·W)` and is a scalar, and `ω` is odd with `ω² = c ≠ 0`, so each generator is
`ι v = c⁻¹ (ι v * ω) * ω` with `ι v * ω` even. A dimension count then makes the surjection
injective. That statement, `TauCeti.SpinPolarizationData.evenCliffordEquivEnd`, is the
odd-dimensional companion of the even `TauCeti.SpinPolarizationData.cliffordEquivEnd`, one grade
down: in even dimension the *whole* Clifford algebra is `Module.End F (⋀·W)`, in odd dimension
only its even half is, the whole algebra being two copies of that half.

## Main results

* `CliffordAlgebra.nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one`: **the even
  subalgebra is a matrix algebra** `M_{2^l}(F)` in dimension `2 * l + 1`.
* `CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one`: **the structure
  theorem in odd dimension**, `CliffordAlgebra Q ≃ₐ[F] M_{2^l}(F) × M_{2^l}(F)`.
* `TauCeti.evenSpinAction_surjective` and `TauCeti.SpinPolarizationData.evenCliffordEquivEnd`:
  **the odd structure theorem in operator form**, that the Fock action identifies `even Q` with
  `Module.End F (⋀·W)`, over any field of characteristic not two.
* `TauCeti.SpinPolarizationData.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one` and
  `TauCeti.SpinPolarizationData.finrank_even_eq_finrank_end_of_odd_finrank`: the dimension
  bookkeeping the operator form rests on.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  Theorem 4.3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Proposition 20.15
  and the discussion of the odd case following it.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The odd-dimensional case".
-/

public section

open CliffordAlgebra Module QuadraticMap

universe u v

namespace TauCeti.SpinPolarizationData

/-! ### The dimension count in odd dimension -/

section Dimension

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} (P : SpinPolarizationData Q)

/-- **The spinor module has dimension `2 ^ l`** when the polarized quadratic space has dimension
`2 * l + 1`. The isotropic summand has dimension `l` in odd dimension as well as in even
dimension, the extra dimension being taken up by the anisotropic remainder, so the two parities
give spinor modules of the same size. -/
theorem finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hV : finrank F V = 2 * l + 1) : finrank F (ExteriorAlgebra F P.W) = 2 ^ l := by
  rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, P.finrank_W_of_finrank_eq_two_mul_add_one hV]

/-- **The even Clifford subalgebra and the operator algebra of the spinor module have equal
dimension** in odd dimension: writing `finrank F V = 2 * l + 1`, that is `2 ^ (2 * l + 1 - 1)` on
the left and `(2 ^ l) ^ 2` on the right.

This is the odd-dimensional analogue of
`TauCeti.SpinPolarizationData.finrank_cliffordAlgebra_eq_finrank_end`, and the shift of one power
of two is exactly the difference between the two parities: in even dimension the *whole* Clifford
algebra matches the operator algebra of `⋀·W`, while in odd dimension only its even half does. -/
theorem finrank_even_eq_finrank_end_of_odd_finrank [Invertible (2 : F)]
    (hodd : Odd (finrank F V)) :
    finrank F ↥(CliffordAlgebra.even Q) =
      finrank F (Module.End F (ExteriorAlgebra F P.W)) := by
  obtain ⟨l, hV⟩ := hodd
  have _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hV]; omega)
  have hEnd : finrank F (Module.End F (ExteriorAlgebra F P.W)) =
      finrank F (ExteriorAlgebra F P.W) * finrank F (ExteriorAlgebra F P.W) :=
    Module.finrank_linearMap F F (ExteriorAlgebra F P.W) (ExteriorAlgebra F P.W)
  rw [CliffordAlgebra.finrank_even Q, hEnd,
    P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one hV, hV, Nat.add_sub_cancel,
    two_mul, pow_add]

end Dimension

end TauCeti.SpinPolarizationData

namespace CliffordAlgebra

open TauCeti

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-! ### The structure theorem in odd dimension -/

variable [IsSepClosed F]

/-- **The even subalgebra of an odd-dimensional Clifford algebra is a matrix algebra.** The Fock
action of a polarization is onto the endomorphism algebra of the spinor module, of dimension
`2 ^ l`; composed with the two-block splitting it becomes a surjection from a product of two copies
of `even Q`, which `TauCeti.exists_algHom_surjective_of_prod` turns into a surjection out of a
single copy. Both sides have dimension `2 ^ l · 2 ^ l` — the even subalgebra by
`CliffordAlgebra.finrank_even` — so that surjection is an isomorphism. -/
theorem nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l + 1) :
    Nonempty (↥(even Q) ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, Nat.two_pow_pos l⟩⟩
  have _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hV]; omega)
  -- The Fock action of a polarization, read in a basis of the spinor module.
  set P := SpinPolarizationData.ofNondegenerate Q hQ
  have hS : finrank F (ExteriorAlgebra F P.W) = 2 ^ l :=
    P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one hV
  set toMatrix := Algebra.endAlgEquivMatrix F (ExteriorAlgebra F P.W) hS
  set π : CliffordAlgebra Q →ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F :=
    (toMatrix : Module.End F (ExteriorAlgebra F P.W) ≃ₐ[F] _).toAlgHom.comp (spinAction Q P)
  have hπsurj : Function.Surjective π :=
    toMatrix.surjective.comp (spinAction_surjective P)
  -- Transport it along the two-block splitting and drop one block.
  obtain ⟨e⟩ := nonempty_algEquiv_even_prod_of_odd_finrank hQ (hV ▸ ⟨l, by ring⟩)
  obtain ⟨ψ, hψ⟩ := exists_algHom_surjective_of_prod (π.comp e.symm.toAlgHom)
    (hπsurj.comp e.symm.surjective)
  -- Equal dimensions upgrade the surjection to an isomorphism.
  have hdim : finrank F ↥(even Q) = finrank F (Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
    rw [finrank_even Q, hV, Module.finrank_matrix, Nat.add_sub_cancel, two_mul, pow_add]
    simp
  exact ⟨AlgEquiv.ofBijective ψ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ψ.toLinearMap) hdim).2 hψ,
      hψ⟩⟩

/-- **The structure theorem in odd dimension**: over a separably closed field of characteristic not
two, the Clifford algebra of a nondegenerate quadratic form on a space of dimension `2 * l + 1` is
the product of two copies of the matrix algebra `M_{2^l}(F)`.

This is the odd-dimensional companion of
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`, and the two blocks are not an
artefact of the proof: the product displayed here has `(1, 0)` as a central idempotent other than
`0` and `1`, so the algebra is not simple, whereas in even dimension it is
(`TauCeti.SpinPolarizationData.isSimpleRing_cliffordAlgebra`). -/
theorem nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l + 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F]
      (Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F × Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F)) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨e⟩ := nonempty_algEquiv_even_prod_of_odd_finrank hQ (hV ▸ ⟨l, by ring⟩)
  obtain ⟨f⟩ := nonempty_algEquiv_even_matrix_of_finrank_eq_two_mul_add_one hQ hV
  exact ⟨e.trans (f.prodCongr f)⟩

end CliffordAlgebra

/-! ### The odd structure theorem in operator form

The matrix identification above is not canonical: it depends on a basis of the spinor module. The
Fock action itself is canonical once a polarization is chosen, and it identifies the even
subalgebra with the operator algebra of the spinor module directly, over any field of
characteristic not two: the polarization data carries the nondegeneracy, and the volume element
does the rest without being normalized to a square root of one. -/

namespace TauCeti

open CliffordAlgebra Module

section OperatorForm

/-- An element squaring to a nonzero scalar is right-invertible, with `c⁻¹ • ω` as the inverse:
`x * ω * (c⁻¹ • ω) = x`. This is the algebraic content of the factorization
`ι v = c⁻¹ (ι v * ω) * ω` by which the volume element pulls an odd generator into the even part. -/
private theorem mul_mul_inv_smul_self_of_mul_self_eq {F : Type*} [Field F] {A : Type*}
    [Semiring A] [Algebra F A] {ω : A} {c : F} (hc : c ≠ 0)
    (hsq : ω * ω = algebraMap F A c) (x : A) : x * ω * (c⁻¹ • ω) = x :=
  calc x * ω * (c⁻¹ • ω) = c⁻¹ • (x * (ω * ω)) := by rw [mul_smul_comm, mul_assoc]
    _ = c⁻¹ • c • x := by rw [hsq, ← Algebra.commutes, ← Algebra.smul_def]
    _ = x := inv_smul_smul₀ hc x

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  (P : SpinPolarizationData Q) (hodd : Odd (finrank F V))

include hodd

/-- **The even Clifford action on the spinor module is onto in odd dimension.** The whole Fock
action is onto by `TauCeti.spinAction_surjective`, and in odd dimension the even half already
reaches everything the odd half does: the volume element `ω` of an orthogonal basis is central,
odd, and squares to a nonzero scalar, so its image is a scalar operator, and every generator
factors as `ι v = c⁻¹ (ι v * ω) * ω` with `ι v * ω` even.

This is the sharp form of the odd-dimensional structure theorem: unlike the whole Clifford
algebra, which needs both spinor modules to act faithfully, the even subalgebra already sees all
of `Module.End F (⋀·W)`. Neither nondegeneracy nor a separably closed field is assumed: the
polarization data carries the first (`TauCeti.SpinPolarizationData.nondegenerate`) and the
argument never normalizes `ω`, which is what the second was for. -/
theorem evenSpinAction_surjective : Function.Surjective (evenSpinAction Q P) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ :=
    (P.nondegenerate ((isUnit_of_invertible (2 : F)).isSMulRegular F)).exists_list_pairwise_isOrtho
  set ω : CliffordAlgebra Q := (l.map (ι Q)).prod
  set c : F := (-1 : F) ^ l.length.choose 2 * (l.map Q).prod
  have hc : c ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (List.prod_ne_zero ?_)
    rintro hmem
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp hmem
    exact hQl v hv hv0
  have hsq : ω * ω = algebraMap F (CliffordAlgebra Q) c := prod_map_ι_sq_scalar hl
  have hsqEnd : spinAction Q P ω * spinAction Q P ω =
      algebraMap F (Module.End F (ExteriorAlgebra F P.W)) c := by
    rw [← map_mul, hsq, AlgHom.commutes]
  have hωodd : ω ∈ evenOdd Q 1 := prod_map_ι_mem_evenOdd_one_of_odd_length (hlen ▸ hodd)
  -- The image of the volume element is central, hence a scalar, hence already in the range.
  have hωrange : spinAction Q P ω ∈ (evenSpinAction Q P).range := by
    have hcentre : spinAction Q P ω ∈
        Subalgebra.center F (Module.End F (ExteriorAlgebra F P.W)) := by
      rw [Subalgebra.mem_center_iff]
      intro f
      obtain ⟨x, rfl⟩ := spinAction_surjective P f
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1
        (prod_map_ι_mem_center_of_odd_length hl (hlen ▸ hodd) hspan) x]
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff F).1 hcentre
    exact ha ▸ Subalgebra.algebraMap_mem _ a
  -- Each generator is an even element times the volume element, up to the scalar `c`.
  have hgen : ∀ v : V, spinAction Q P (ι Q v) ∈ (evenSpinAction Q P).range := by
    intro v
    have hmem : ι Q v * ω ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
      have h := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q v) hωodd
      rwa [CharTwo.add_self_eq_zero] at h
    have hrw : spinAction Q P (ι Q v * ω) * (c⁻¹ • spinAction Q P ω) = spinAction Q P (ι Q v) := by
      rw [map_mul]
      exact mul_mul_inv_smul_self_of_mul_self_eq hc hsqEnd _
    exact hrw ▸ Subalgebra.mul_mem _
      ((AlgHom.mem_range _).2 ⟨⟨_, hmem⟩, evenSpinAction_apply Q P _⟩)
      (Subalgebra.smul_mem _ hωrange _)
  -- The generators generate, so the range of the even action is everything.
  have hle : Algebra.adjoin F (Set.range (ι Q)) ≤
      Subalgebra.comap (spinAction Q P) (evenSpinAction Q P).range :=
    Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hgen v)
  intro f
  obtain ⟨x, rfl⟩ := spinAction_surjective P f
  exact (AlgHom.mem_range _).1 (hle ((adjoin_range_ι (Q := Q)).ge Algebra.mem_top))

/-- **The even Clifford action on the spinor module is faithful in odd dimension.** It is onto an
algebra of the same dimension, so it is injective. -/
theorem evenSpinAction_injective : Function.Injective (evenSpinAction Q P) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (evenSpinAction Q P).toLinearMap)
    (P.finrank_even_eq_finrank_end_of_odd_finrank hodd)).2
    (evenSpinAction_surjective P hodd)

/-- **The odd structure theorem in operator form**: for a polarized quadratic space of odd
dimension over a field of characteristic not two, the Fock action is an isomorphism of
`F`-algebras from the even Clifford subalgebra onto the endomorphism algebra of the spinor module
`S = ⋀·W`.

This is the odd-dimensional companion of
`TauCeti.SpinPolarizationData.cliffordEquivEnd`, one grade down: there the *whole* algebra is
`Module.End F S`, here only its even half is, the whole algebra being two copies of it. -/
noncomputable def SpinPolarizationData.evenCliffordEquivEnd :
    ↥(even Q) ≃ₐ[F] Module.End F (ExteriorAlgebra F P.W) :=
  AlgEquiv.ofBijective (evenSpinAction Q P)
    ⟨evenSpinAction_injective P hodd, evenSpinAction_surjective P hodd⟩

/-- The operator form of the odd structure theorem is the Fock action itself. -/
@[simp]
theorem SpinPolarizationData.evenCliffordEquivEnd_apply (x : ↥(even Q)) :
    P.evenCliffordEquivEnd hodd x = spinAction Q P x :=
  (congrFun (AlgEquiv.coe_ofBijective _ _) x).trans (evenSpinAction_apply Q P x)

end OperatorForm

end TauCeti
