/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Repartition.Basic
import TauCeti.LinearAlgebra.Dimension.Tower

/-!
# The exact sequence of one step of the repartition filtration

For divisors `D ≤ E` of an algebraic function field `F / k` the two subspaces `A_F(D) + F` and
`A_F(E) + F` of the repartition space sit inside one another, and the quotient
`(A_F(E) + F) / (A_F(D) + F)` is what measures the difference between the cokernels of
`A_F(D) + F → A_F` and `A_F(E) + F → A_F`.  This file computes that quotient, by exhibiting the
exact sequence

`0 → L(E)/L(D) → A_F(E)/A_F(D) → (A_F(E) + F)/(A_F(D) + F) → 0`

as two explicit surjections and reading off ranks.  The mathematics is the first step of
Stichtenoth's proof of Theorem 1.5.4, and its input is the diagonal-intersection lemma
`TauCeti.diagonalRepartitions_inf_adeleFiltration` (`F ∩ A_F(D) = L(D)`) in the relative form
`TauCeti.adeleFiltration_inf_sup_diagonalRepartitions` (`A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)`).

The exact sequence and its rank form need no finiteness; only the two `ℓ`-valued corollaries at
the end assume `IsFunctionField k F`, for the finite-dimensionality of `L(D)` and `L(E)`.
Combined with the `k`-dimension `deg E - deg D` of `A_F(E)/A_F(D)`, the rank identity below is
the identity `dim ((A_F(E) + F)/(A_F(D) + F)) = (deg E - ℓ(E)) - (deg D - ℓ(D))` that Stichtenoth
uses to produce a divisor with `A_F = A_F(D) + F` and hence to identify the index of specialty
`i(D)` with `dim_k (A_F ⧸ (A_F(D) + F))`.

## Main definitions

* `TauCeti.riemannRochSpaceToInfSupDiagonalQuotient`: the surjection
  `L(E) → (A_F(E) ∩ (A_F(D) + F))/A_F(D)` sending a function to its constant repartition, the
  left-hand map of the exact sequence.

## Main results

* `TauCeti.riemannRochQuotientEquivInfSupDiagonalQuotient`: that surjection presented as a
  linear equivalence of relative quotients, `L(E)/L(D) ≅ (A_F(E) ∩ (A_F(D) + F))/A_F(D)`.
* `TauCeti.rank_quotient_adeleFiltration_eq_add`: the rank form of the exact sequence,
  `rank (A_F(E)/A_F(D)) = rank (L(E)/L(D)) + rank ((A_F(E) + F)/(A_F(D) + F))`.
* `TauCeti.rank_quotient_adeleFiltration_add_dim`: the same identity with `rank (L(E)/L(D))`
  replaced by `ℓ(E) - ℓ(D)`, in the subtraction-free form
  `rank (A_F(E)/A_F(D)) + ℓ(D) = rank ((A_F(E) + F)/(A_F(D) + F)) + ℓ(E)`.
* `TauCeti.finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions_iff`: the two
  repartition quotients are finite-dimensional together, since the Riemann–Roch quotient
  `L(E)/L(D)` between them is finite-dimensional for every divisor of an algebraic function
  field (`TauCeti.finiteDimensional_riemannRochSpace`).

## Implementation notes

Relative quotients are spelled `↥q ⧸ p.submoduleOf q` with Mathlib's `Submodule.submoduleOf`,
as in `TauCeti.Place.filtration`, so that they are meaningful without an inclusion `p ≤ q`.
The subspace `A_F(D) + F` is written out as `adeleFiltration D ⊔ diagonalRepartitions k F` and
not given a name of its own, since no result here needs one.

The right-hand map of the exact sequence gets no declaration: it is Noether's second isomorphism
theorem, `LinearMap.quotientInfEquivSupQuotient`, applied to `A_F(E)` and `A_F(D) + F`, whose sup
collapses to `A_F(E) + F` because `A_F(D) ≤ A_F(E)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 (the proof of Theorem 1.5.4).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {D E : Divisor k F}

/-! ### The surjection `L(E) → (A_F(E) ∩ (A_F(D) + F))/A_F(D)` -/

/-- The composite `L(E) ↪ A_F(E) ∩ (A_F(D) + F) ↠ (A_F(E) ∩ (A_F(D) + F))/A_F(D)`, the
left-hand map of the exact sequence of this file: a function is sent to the class of its
constant repartition. -/
noncomputable def riemannRochSpaceToInfSupDiagonalQuotient (D E : Divisor k F) :
    ↥(riemannRochSpace E) →ₗ[k]
      ↥(adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) ⧸
        (adeleFiltration D).submoduleOf
          (adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) :=
  ((adeleFiltration D).submoduleOf
      (adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F))).mkQ ∘ₗ
    LinearMap.codRestrict _
      ((Pi.constAlgHom k (Place k F) F).toLinearMap ∘ₗ (riemannRochSpace E).subtype)
      fun f ↦ const_mem_adeleFiltration_inf_sup_diagonalRepartitions D f.2

@[simp]
theorem riemannRochSpaceToInfSupDiagonalQuotient_apply (D E : Divisor k F)
    (f : ↥(riemannRochSpace E)) :
    riemannRochSpaceToInfSupDiagonalQuotient D E f =
      Submodule.Quotient.mk ⟨Function.const (Place k F) (f : F),
        const_mem_adeleFiltration_inf_sup_diagonalRepartitions D f.2⟩ := (rfl)

/-- Every class of `(A_F(E) ∩ (A_F(D) + F))/A_F(D)` is represented by a constant, by the relative
diagonal-intersection lemma. -/
theorem riemannRochSpaceToInfSupDiagonalQuotient_surjective (h : D ≤ E) :
    Function.Surjective (riemannRochSpaceToInfSupDiagonalQuotient (k := k) D E) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ha : (a : Place k F → F) ∈
      adeleFiltration D ⊔ (diagonalRepartitions k F ⊓ adeleFiltration E) := by
    rw [diagonalRepartitions_inf_adeleFiltration,
      ← adeleFiltration_inf_sup_diagonalRepartitions h]
    exact a.2
  obtain ⟨b, hb, c, ⟨hcd, hce⟩, hbc⟩ := Submodule.mem_sup.mp ha
  obtain ⟨f, rfl⟩ := mem_diagonalRepartitions_iff.mp hcd
  have hf : f ∈ riemannRochSpace E := const_mem_adeleFiltration_iff.mp hce
  have hval : Function.const (Place k F) f - (a : Place k F → F) = -b := by
    rw [← hbc]
    abel
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [riemannRochSpaceToInfSupDiagonalQuotient_apply, Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, hval]
  exact neg_mem hb

/-- A function of `L(E)` has constant repartition in `A_F(D)` exactly when it lies in `L(D)`, so
the left-hand map of the exact sequence has kernel `L(D)`. -/
theorem ker_riemannRochSpaceToInfSupDiagonalQuotient (D E : Divisor k F) :
    LinearMap.ker (riemannRochSpaceToInfSupDiagonalQuotient (k := k) D E) =
      (riemannRochSpace D).submoduleOf (riemannRochSpace E) := by
  ext f
  -- the map has to be unfolded before `Submodule.submoduleOf` is, since unfolding the latter in
  -- the codomain would keep `LinearMap.mem_ker` from matching
  rw [LinearMap.mem_ker, riemannRochSpaceToInfSupDiagonalQuotient_apply,
    Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    const_mem_adeleFiltration_iff]

/-- **The left-hand map of the exact sequence, as an isomorphism**: for `D ≤ E`,
`L(E)/L(D) ≅ (A_F(E) ∩ (A_F(D) + F))/A_F(D)`. -/
noncomputable def riemannRochQuotientEquivInfSupDiagonalQuotient (h : D ≤ E) :
    (↥(riemannRochSpace E) ⧸ (riemannRochSpace D).submoduleOf (riemannRochSpace E)) ≃ₗ[k]
      ↥(adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) ⧸
        (adeleFiltration D).submoduleOf
          (adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) :=
  (Submodule.quotEquivOfEq _ _ (ker_riemannRochSpaceToInfSupDiagonalQuotient D E).symm).trans
    ((riemannRochSpaceToInfSupDiagonalQuotient D E).quotKerEquivOfSurjective
      (riemannRochSpaceToInfSupDiagonalQuotient_surjective h))

@[simp]
theorem riemannRochQuotientEquivInfSupDiagonalQuotient_apply_mk (h : D ≤ E)
    (f : ↥(riemannRochSpace E)) :
    riemannRochQuotientEquivInfSupDiagonalQuotient h (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk ⟨Function.const (Place k F) (f : F),
        const_mem_adeleFiltration_inf_sup_diagonalRepartitions D f.2⟩ := (rfl)

/-! ### The rank identity -/

/-- **The exact sequence of one step of the filtration, in rank form** (Stichtenoth, first step
of the proof of Theorem 1.5.4): for `D ≤ E`,

`rank (A_F(E)/A_F(D)) = rank (L(E)/L(D)) + rank ((A_F(E) + F)/(A_F(D) + F))`.

No finiteness hypothesis is needed; the form that reads the middle term as `ℓ(E) - ℓ(D)` is
`TauCeti.rank_quotient_adeleFiltration_add_dim`. -/
theorem rank_quotient_adeleFiltration_eq_add (h : D ≤ E) :
    Module.rank k (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) =
      Module.rank k
          (↥(riemannRochSpace E) ⧸ (riemannRochSpace D).submoduleOf (riemannRochSpace E)) +
        Module.rank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
          (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
            (adeleFiltration E ⊔ diagonalRepartitions k F)) := by
  have hpq : adeleFiltration D ≤
      adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F) :=
    le_inf (adeleFiltration_mono h) le_sup_left
  -- `A_F(E) + (A_F(D) + F) = A_F(E) + F`, since `A_F(D) ≤ A_F(E)`
  have hsup : adeleFiltration E ⊔ (adeleFiltration D ⊔ diagonalRepartitions k F) =
      adeleFiltration E ⊔ diagonalRepartitions k F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleFiltration_mono h)]
  -- the top step of the tower is Noether's second isomorphism theorem
  have hiso : Module.rank k (↥(adeleFiltration E) ⧸
        (adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)).submoduleOf
          (adeleFiltration E)) =
      Module.rank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
          (adeleFiltration E ⊔ diagonalRepartitions k F)) := by
    rw [← hsup]
    simp only [Submodule.submoduleOf, Submodule.comap_inf]
    exact (LinearMap.quotientInfEquivSupQuotient (adeleFiltration E)
      (adeleFiltration D ⊔ diagonalRepartitions k F)).rank_eq
  rw [rank_quotient_submoduleOf_tower hpq inf_le_left,
    (riemannRochQuotientEquivInfSupDiagonalQuotient h).rank_eq, hiso]

/-- **The exact sequence of one step of the filtration**, with the Riemann–Roch quotient replaced
by the dimensions it computes: for `D ≤ E`,

`rank (A_F(E)/A_F(D)) + ℓ(D) = rank ((A_F(E) + F)/(A_F(D) + F)) + ℓ(E)`.

The identity is stated without subtraction because the two repartition quotients are only known
to be finite once the degree count `dim_k (A_F(E)/A_F(D)) = deg E - deg D` is available. -/
theorem rank_quotient_adeleFiltration_add_dim (hF : IsFunctionField k F) (h : D ≤ E) :
    Module.rank k (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) +
        (Divisor.dim D : Cardinal) =
      Module.rank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
          (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
            (adeleFiltration E ⊔ diagonalRepartitions k F)) + (Divisor.dim E : Cardinal) := by
  rw [rank_quotient_adeleFiltration_eq_add h, add_right_comm,
    rank_quotient_riemannRochSpace_add_dim hF h, add_comm]

/-- The two relative quotients of the exact sequence are finite-dimensional together: the
Riemann–Roch quotient `L(E)/L(D)` between them is finite-dimensional for every divisor of an
algebraic function field (`TauCeti.finiteDimensional_riemannRochSpace`). -/
theorem finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions_iff
    (hF : IsFunctionField k F) (h : D ≤ E) :
    FiniteDimensional k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
          (adeleFiltration E ⊔ diagonalRepartitions k F)) ↔
      FiniteDimensional k
        (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) := by
  have hfinE := finiteDimensional_riemannRochSpace hF E
  have hL : Module.rank k
      (↥(riemannRochSpace E) ⧸ (riemannRochSpace D).submoduleOf (riemannRochSpace E)) <
        Cardinal.aleph0 :=
    Module.rank_lt_aleph0_iff.mpr inferInstance
  have hrank := rank_quotient_adeleFiltration_eq_add h
  constructor
  · intro hfin
    refine Module.rank_lt_aleph0_iff.mp ?_
    rw [hrank]
    exact Cardinal.add_lt_aleph0 hL (Module.rank_lt_aleph0_iff.mpr hfin)
  · intro hfin
    refine Module.rank_lt_aleph0_iff.mp ?_
    have hlt := Module.rank_lt_aleph0_iff.mpr hfin
    rw [hrank] at hlt
    exact lt_of_le_of_lt le_add_self hlt

end TauCeti
