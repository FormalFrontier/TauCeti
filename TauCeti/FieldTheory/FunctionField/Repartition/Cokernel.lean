/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Repartition.Basic
public import TauCeti.LinearAlgebra.Dimension.Tower

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
`A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)`.

Everything here is stated for `Module.rank`, so no finiteness enters.  Combined with the
`k`-dimension `deg E - deg D` of `A_F(E)/A_F(D)`, the rank identity below is the identity
`dim ((A_F(E) + F)/(A_F(D) + F)) = (deg E - ℓ(E)) - (deg D - ℓ(D))` that Stichtenoth uses to
produce a divisor with `A_F = A_F(D) + F` and hence to identify the index of specialty
`i(D)` with `dim_k (A_F ⧸ (A_F(D) + F))`.

## Main definitions

* `TauCeti.adeleFiltrationToSupDiagonalQuotient`: the surjection
  `A_F(E) → (A_F(E) + F)/(A_F(D) + F)`.
* `TauCeti.riemannRochSpaceToAdeleQuotient`: the surjection
  `L(E) → (A_F(E) ∩ (A_F(D) + F))/A_F(D)` sending a function to its constant repartition.

## Main results

* `TauCeti.adeleFiltration_inf_sup_diagonalRepartitions`: `A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)`
  for `D ≤ E`.
* `TauCeti.adeleFiltrationQuotientEquivSupDiagonalQuotient` and
  `TauCeti.riemannRochQuotientEquivAdeleQuotient`: the two surjections presented as linear
  equivalences of relative quotients.
* `TauCeti.rank_quotient_adeleFiltration_eq_add`: the rank form of the exact sequence,
  `rank (A_F(E)/A_F(D)) = rank (L(E)/L(D)) + rank ((A_F(E) + F)/(A_F(D) + F))`.
* `TauCeti.rank_quotient_adeleFiltration_add_dim`: the same identity with `rank (L(E)/L(D))`
  replaced by `ℓ(E) - ℓ(D)`, in the subtraction-free form
  `rank (A_F(E)/A_F(D)) + ℓ(D) = rank ((A_F(E) + F)/(A_F(D) + F)) + ℓ(E)`.
* `TauCeti.finiteDimensional_quotient_adeleFiltrationSupDiagonal_iff`: the two relative quotients
  are finite-dimensional together, since `L(E)/L(D)` always is.

## Implementation notes

Relative quotients are spelled `↥q ⧸ p.submoduleOf q` with Mathlib's `Submodule.submoduleOf`,
as in `TauCeti.Place.filtration`, so that they are meaningful without an inclusion `p ≤ q`.
The subspace `A_F(D) + F` is written out as `adeleFiltration D ⊔ diagonalRepartitions k F` and
not given a name of its own, since no result here needs one.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 (the proof of Theorem 1.5.4).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {D E : Divisor k F}

/-- Inside `p`, the trace of `p ⊓ q` is the trace of `q`.  This lets the tower
`A_F(D) ≤ A_F(E) ⊓ (A_F(D) + F) ≤ A_F(E)` be read with the middle term replaced by
`A_F(D) + F`. -/
private lemma submoduleOf_inf_left {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) : (p ⊓ q).submoduleOf p = q.submoduleOf p := by
  simp [Submodule.submoduleOf, Submodule.comap_inf, Submodule.comap_subtype_self]

/-! ### The relative diagonal-intersection lemma -/

/-- **The relative form of `F ∩ A_F(D) = L(D)`** (Stichtenoth, in the proof of Theorem 1.5.4):
for `D ≤ E`, a repartition bounded by `E` that differs from a constant by a repartition bounded
by `D` differs from a constant of `L(E)`, so that

`A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)`.

Given `A_F(D) ≤ A_F(E)` this is the modular law for the lattice of subspaces followed by the
diagonal-intersection lemma `TauCeti.diagonalRepartitions_inf_adeleFiltration`. -/
theorem adeleFiltration_inf_sup_diagonalRepartitions (h : D ≤ E) :
    adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F) =
      adeleFiltration D ⊔
        (riemannRochSpace E).map (Pi.constAlgHom k (Place k F) F).toLinearMap := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleFiltration_mono h),
    diagonalRepartitions_inf_adeleFiltration]

/-! ### The surjection `A_F(E) → (A_F(E) + F)/(A_F(D) + F)` -/

/-- The composite `A_F(E) ↪ A_F(E) + F ↠ (A_F(E) + F)/(A_F(D) + F)`, the right-hand map of the
exact sequence of this file. -/
noncomputable def adeleFiltrationToSupDiagonalQuotient (D E : Divisor k F) :
    ↥(adeleFiltration E) →ₗ[k]
      ↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
          (adeleFiltration E ⊔ diagonalRepartitions k F) :=
  ((adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
    (adeleFiltration E ⊔ diagonalRepartitions k F)).mkQ ∘ₗ Submodule.inclusion le_sup_left

@[simp]
theorem adeleFiltrationToSupDiagonalQuotient_apply (D E : Divisor k F)
    (a : ↥(adeleFiltration E)) :
    adeleFiltrationToSupDiagonalQuotient D E a =
      Submodule.Quotient.mk ⟨(a : Place k F → F), Submodule.mem_sup_left a.2⟩ := (rfl)

/-- Every class of `(A_F(E) + F)/(A_F(D) + F)` is represented by a repartition bounded by `E`:
the constant part of a representative already lies in `A_F(D) + F`. -/
theorem adeleFiltrationToSupDiagonalQuotient_surjective (D E : Divisor k F) :
    Function.Surjective (adeleFiltrationToSupDiagonalQuotient (k := k) D E) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp a.2
  have hval : b - (a : Place k F → F) = -c := by
    rw [← hbc]
    abel
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [adeleFiltrationToSupDiagonalQuotient_apply, Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, hval]
  exact Submodule.mem_sup_right (neg_mem hc)

/-- A repartition bounded by `E` dies in `(A_F(E) + F)/(A_F(D) + F)` exactly when it lies in
`A_F(D) + F`. -/
theorem ker_adeleFiltrationToSupDiagonalQuotient (D E : Divisor k F) :
    LinearMap.ker (adeleFiltrationToSupDiagonalQuotient (k := k) D E) =
      (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (adeleFiltration E) := by
  ext a
  -- unfold the map first: `Submodule.submoduleOf` also occurs in its codomain, and unfolding it
  -- there would keep `LinearMap.mem_ker` from matching
  rw [LinearMap.mem_ker, adeleFiltrationToSupDiagonalQuotient_apply,
    Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

/-- **The right-hand map of the exact sequence, as an isomorphism**: for any two divisors,
`A_F(E) / (A_F(D) + F) ≅ (A_F(E) + F) / (A_F(D) + F)`, where the left-hand side is the quotient
of `A_F(E)` by the part of `A_F(D) + F` it contains. -/
noncomputable def adeleFiltrationQuotientEquivSupDiagonalQuotient (D E : Divisor k F) :
    (↥(adeleFiltration E) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (adeleFiltration E)) ≃ₗ[k]
      ↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
          (adeleFiltration E ⊔ diagonalRepartitions k F) :=
  (Submodule.quotEquivOfEq _ _ (ker_adeleFiltrationToSupDiagonalQuotient D E).symm).trans
    ((adeleFiltrationToSupDiagonalQuotient D E).quotKerEquivOfSurjective
      (adeleFiltrationToSupDiagonalQuotient_surjective D E))

@[simp]
theorem adeleFiltrationQuotientEquivSupDiagonalQuotient_apply_mk (D E : Divisor k F)
    (a : ↥(adeleFiltration E)) :
    adeleFiltrationQuotientEquivSupDiagonalQuotient D E (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨(a : Place k F → F), Submodule.mem_sup_left a.2⟩ := (rfl)

/-! ### The surjection `L(E) → (A_F(E) ∩ (A_F(D) + F))/A_F(D)` -/

/-- The constant repartition of a function of `L(E)` is bounded by `E`, and is a constant, so it
lies in `A_F(E) ∩ (A_F(D) + F)`. -/
theorem const_mem_adeleFiltration_inf_sup_diagonalRepartitions (D : Divisor k F)
    {E : Divisor k F} {f : F} (hf : f ∈ riemannRochSpace E) :
    Function.const (Place k F) f ∈
      adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F) :=
  ⟨const_mem_adeleFiltration_iff.mpr hf,
    Submodule.mem_sup_right (const_mem_diagonalRepartitions f)⟩

/-- The composite `L(E) ↪ A_F(E) ∩ (A_F(D) + F) ↠ (A_F(E) ∩ (A_F(D) + F))/A_F(D)`, the
left-hand map of the exact sequence of this file: a function is sent to the class of its
constant repartition. -/
noncomputable def riemannRochSpaceToAdeleQuotient (D E : Divisor k F) :
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
theorem riemannRochSpaceToAdeleQuotient_apply (D E : Divisor k F)
    (f : ↥(riemannRochSpace E)) :
    riemannRochSpaceToAdeleQuotient D E f =
      Submodule.Quotient.mk ⟨Function.const (Place k F) (f : F),
        const_mem_adeleFiltration_inf_sup_diagonalRepartitions D f.2⟩ := (rfl)

/-- Every class of `(A_F(E) ∩ (A_F(D) + F))/A_F(D)` is represented by a constant, by the relative
diagonal-intersection lemma. -/
theorem riemannRochSpaceToAdeleQuotient_surjective (h : D ≤ E) :
    Function.Surjective (riemannRochSpaceToAdeleQuotient (k := k) D E) := by
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
  rw [riemannRochSpaceToAdeleQuotient_apply, Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, hval]
  exact neg_mem hb

/-- A function of `L(E)` has constant repartition in `A_F(D)` exactly when it lies in `L(D)`, so
the left-hand map of the exact sequence has kernel `L(D)`. -/
theorem ker_riemannRochSpaceToAdeleQuotient (D E : Divisor k F) :
    LinearMap.ker (riemannRochSpaceToAdeleQuotient (k := k) D E) =
      (riemannRochSpace D).submoduleOf (riemannRochSpace E) := by
  ext f
  -- as in `TauCeti.ker_adeleFiltrationToSupDiagonalQuotient`, the map has to go before
  -- `Submodule.submoduleOf` is unfolded
  rw [LinearMap.mem_ker, riemannRochSpaceToAdeleQuotient_apply, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    const_mem_adeleFiltration_iff]

/-- **The left-hand map of the exact sequence, as an isomorphism**: for `D ≤ E`,
`L(E)/L(D) ≅ (A_F(E) ∩ (A_F(D) + F))/A_F(D)`. -/
noncomputable def riemannRochQuotientEquivAdeleQuotient (h : D ≤ E) :
    (↥(riemannRochSpace E) ⧸ (riemannRochSpace D).submoduleOf (riemannRochSpace E)) ≃ₗ[k]
      ↥(adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) ⧸
        (adeleFiltration D).submoduleOf
          (adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F)) :=
  (Submodule.quotEquivOfEq _ _ (ker_riemannRochSpaceToAdeleQuotient D E).symm).trans
    ((riemannRochSpaceToAdeleQuotient D E).quotKerEquivOfSurjective
      (riemannRochSpaceToAdeleQuotient_surjective h))

@[simp]
theorem riemannRochQuotientEquivAdeleQuotient_apply_mk (h : D ≤ E)
    (f : ↥(riemannRochSpace E)) :
    riemannRochQuotientEquivAdeleQuotient h (Submodule.Quotient.mk f) =
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
  rw [rank_quotient_submoduleOf_tower hpq inf_le_left,
    (riemannRochQuotientEquivAdeleQuotient h).rank_eq, submoduleOf_inf_left,
    (adeleFiltrationQuotientEquivSupDiagonalQuotient D E).rank_eq]

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
  have hfinE := finiteDimensional_riemannRochSpace hF E
  have hfinD := finiteDimensional_riemannRochSpace hF D
  have hsub : Module.rank k ((riemannRochSpace D).submoduleOf (riemannRochSpace E)) =
      (Divisor.dim D : Cardinal) := by
    rw [(Submodule.submoduleOfEquivOfLe (riemannRochSpace_mono h)).rank_eq, Divisor.dim_def,
      Module.finrank_eq_rank]
  have hdimE : (Divisor.dim E : Cardinal) = Module.rank k (riemannRochSpace E) := by
    rw [Divisor.dim_def, Module.finrank_eq_rank]
  have hquot := Submodule.rank_quotient_add_rank
    ((riemannRochSpace D).submoduleOf (riemannRochSpace E))
  rw [hsub, ← hdimE] at hquot
  rw [rank_quotient_adeleFiltration_eq_add h, add_right_comm, hquot, add_comm]

/-- The two relative quotients of the exact sequence are finite-dimensional together: the
Riemann–Roch quotient `L(E)/L(D)` between them always is. -/
theorem finiteDimensional_quotient_adeleFiltrationSupDiagonal_iff (hF : IsFunctionField k F)
    (h : D ≤ E) :
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
