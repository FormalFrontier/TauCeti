/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Repartition.Cokernel
public import TauCeti.FieldTheory.FunctionField.Repartition.Quotient
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# The index of specialty is the dimension of a repartition cokernel

For a divisor `D` of an algebraic function field `F / k` with exact constant field, the index of
specialty `i(D) = ℓ(D) - deg D - 1 + g` counts exactly how far the repartitions bounded by `D`
together with the constants fall short of all repartitions:

`i(D) = dim_k (A_F ⧸ (A_F(D) + F))`.

This is Stichtenoth's Theorem 1.5.4, the linear-algebra summit that turns the index of specialty
into a `k`-dimension.  It is the input to Lemma 1.5.7, `dim_k Ω_F(D) = i(D)`, which is what makes
the space of Weil differentials nonzero and eventually one-dimensional over `F`.  Its case `D = 0`
is Corollary 1.5.5, `g = dim_k (A_F ⧸ (A_F(0) + F))`, which reads the genus off the same quotient.

The two ingredients are already on `main`: the exact sequence of one step of the filtration
(`TauCeti.rank_quotient_adeleFiltration_add_dim`, in `Repartition/Cokernel.lean`) and the degree
count `dim_k (A_F(E)/A_F(D)) = deg E - deg D` (`TauCeti.rank_quotient_adeleFiltration`, in
`Repartition/Quotient.lean`).  Together they say that one step of the filtration of cokernels has
dimension `i(D) - i(E)`; the work here is Stichtenoth's observation that this vanishes as soon as
`D` and `E` have the same index of specialty, so that the filtration of `A_F` by the subspaces
`A_F(D) + F` becomes *constant* in large degree — and therefore reaches `A_F` itself, since every
repartition is bounded by some divisor.

## Main results

* `TauCeti.finrank_quotient_adeleFiltration_sup_diagonalRepartitions`: one step of the filtration
  of cokernels, `dim_k ((A_F(E) + F)/(A_F(D) + F)) = i(D) - i(E)` for `D ≤ E`.
* `TauCeti.exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace`: every divisor `D`
  is dominated by a divisor `E` with `A_F(E) + F = A_F` (Stichtenoth, in the proof of
  Theorem 1.5.4).
* `TauCeti.finrank_quotient_repartitionSpace`: **Stichtenoth, Theorem 1.5.4**,
  `i(D) = dim_k (A_F ⧸ (A_F(D) + F))`.
* `TauCeti.finrank_quotient_repartitionSpace_zero`: **Stichtenoth, Corollary 1.5.5**,
  `g = dim_k (A_F ⧸ (A_F(0) + F))`.
* `TauCeti.adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff`: the divisors with
  `A_F(D) + F = A_F` are exactly the nonspecial ones.

## Implementation notes

Relative quotients are spelled `↥q ⧸ p.submoduleOf q` with Mathlib's `Submodule.submoduleOf`, and
the subspace `A_F(D) + F` is written out as `adeleFiltration D ⊔ diagonalRepartitions k F`, both as
in `Repartition/Cokernel.lean`.  The cokernel `A_F ⧸ (A_F(D) + F)` is therefore the relative
quotient of `repartitionSpace k F` by `adeleFiltration D ⊔ diagonalRepartitions k F`; it gets no
name of its own here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 (Theorem 1.5.4 and Corollary 1.5.5).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {D E : Divisor k F}

variable (hF : IsFunctionField k F)
include hF

/-! ### One step of the filtration of cokernels -/

/-- For `D ≤ E` the quotient `(A_F(E) + F)/(A_F(D) + F)` is finite-dimensional: the exact sequence
of `TauCeti.finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions_iff` compares it
with `A_F(E)/A_F(D)`, which has dimension `deg E - deg D`. -/
theorem finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions (h : D ≤ E) :
    FiniteDimensional k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
      (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
        (adeleFiltration E ⊔ diagonalRepartitions k F)) :=
  (finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions_iff hF h).mpr
    (finiteDimensional_quotient_adeleFiltration hF h)

/-- **One step of the filtration of cokernels** (Stichtenoth, in the proof of Theorem 1.5.4): for
`D ≤ E`,

`dim_k ((A_F(E) + F)/(A_F(D) + F)) = i(D) - i(E)`.

This is the exact sequence `TauCeti.rank_quotient_adeleFiltration_add_dim` read together with the
degree count `TauCeti.rank_quotient_adeleFiltration`; the genus cancels between the two indices of
specialty, so no hypothesis on the constant field is needed. -/
theorem finrank_quotient_adeleFiltration_sup_diagonalRepartitions (h : D ≤ E) :
    (Module.finrank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
          (adeleFiltration E ⊔ diagonalRepartitions k F)) : ℤ) =
      Divisor.indexOfSpecialty D - Divisor.indexOfSpecialty E := by
  have hfin := finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions hF h
  have hrank := rank_quotient_adeleFiltration_add_dim hF h
  rw [rank_quotient_adeleFiltration hF h, ← Module.finrank_eq_rank] at hrank
  -- every cardinal in sight is now a natural number, so the identity is a numeric one
  have hnat : (Divisor.degree E - Divisor.degree D).toNat + Divisor.dim D =
      Module.finrank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
          (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
            (adeleFiltration E ⊔ diagonalRepartitions k F)) + Divisor.dim E := by
    exact_mod_cast hrank
  have hdeg : Divisor.degree D ≤ Divisor.degree E := Divisor.degree_le_of_le h
  simp only [Divisor.indexOfSpecialty_def]
  omega

/-! ### The filtration of cokernels is constant in large degree -/

/-- Two divisors `D ≤ E` with the same index of specialty give the same subspace `A_F(D) + F` of
the repartition space: the step between them has dimension `i(D) - i(E) = 0`. -/
theorem adeleFiltration_sup_diagonalRepartitions_eq_of_indexOfSpecialty_eq (h : D ≤ E)
    (hi : Divisor.indexOfSpecialty D = Divisor.indexOfSpecialty E) :
    adeleFiltration D ⊔ diagonalRepartitions k F =
      adeleFiltration E ⊔ diagonalRepartitions k F := by
  have hfin := finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions hF h
  have hzero : Module.finrank k (↥(adeleFiltration E ⊔ diagonalRepartitions k F) ⧸
      (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf
        (adeleFiltration E ⊔ diagonalRepartitions k F)) = 0 := by
    have := finrank_quotient_adeleFiltration_sup_diagonalRepartitions hF h
    omega
  refine le_antisymm (sup_le_sup_right (adeleFiltration_mono h) _) ?_
  exact Submodule.submoduleOf_eq_top.mp
    (Submodule.Quotient.subsingleton_iff.mp (Module.finrank_zero_iff.mp hzero))

/-- **Every divisor is dominated by one whose repartitions and constants exhaust `A_F`**
(Stichtenoth, in the proof of Theorem 1.5.4): for every `D` there is `E ≥ D` with `i(E) = 0` and
`A_F(E) + F = A_F`.

Riemann's theorem provides an `E ≥ D` of large enough degree to be nonspecial; every further
enlargement of `E` is nonspecial too, so by
`TauCeti.adeleFiltration_sup_diagonalRepartitions_eq_of_indexOfSpecialty_eq` it does not enlarge
`A_F(E) + F`, while every single repartition is bounded by some divisor. -/
theorem exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace
    (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    ∃ E : Divisor k F, D ≤ E ∧ Divisor.indexOfSpecialty E = 0 ∧
      adeleFiltration E ⊔ diagonalRepartitions k F = repartitionSpace k F := by
  obtain ⟨c, hc⟩ := exists_forall_indexOfSpecialty_eq_zero hF hex
  obtain ⟨P⟩ := Place.nonempty hF
  -- enlarge `D` at the place `P` until the degree passes the nonspeciality threshold `c`
  set n := (c - Divisor.degree D).toNat with hn
  have hDE : D ≤ D + n • WeilDivisor.ofPoint P := le_add_of_nonneg_right
    (nsmul_nonneg (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) n)
  have hdeg : c ≤ Divisor.degree (D + n • WeilDivisor.ofPoint P) := by
    have hP : (1 : ℤ) ≤ P.degree := by exact_mod_cast P.one_le_degree_of_isFunctionField hF
    have hmul : (n : ℤ) ≤ (n : ℤ) * P.degree := le_mul_of_one_le_right (by positivity) hP
    rw [Divisor.degree_add, map_nsmul, Divisor.degree_ofPoint, nsmul_eq_mul]
    omega
  set E := D + n • WeilDivisor.ofPoint P
  refine ⟨E, hDE, hc E hdeg, le_antisymm (adeleFiltration_sup_diagonalRepartitions_le hF E)
    fun a ha ↦ ?_⟩
  -- a repartition is bounded by some divisor `E'`, and `E ⊔ E'` is nonspecial along with `E`
  obtain ⟨E', hE'⟩ := exists_mem_adeleFiltration ha
  have hsup : Divisor.indexOfSpecialty (E ⊔ E') = 0 :=
    hc _ (hdeg.trans (Divisor.degree_le_of_le le_sup_left))
  rw [adeleFiltration_sup_diagonalRepartitions_eq_of_indexOfSpecialty_eq hF
    (le_sup_left : E ≤ E ⊔ E') (by rw [hc E hdeg, hsup])]
  exact Submodule.mem_sup_left (adeleFiltration_mono le_sup_right hE')

/-! ### Theorem 1.5.4 -/

/-- The cokernel `A_F ⧸ (A_F(D) + F)` is finite-dimensional over `k`. -/
theorem finiteDimensional_quotient_repartitionSpace (hex : IsIntegrallyClosedIn k F)
    (D : Divisor k F) :
    FiniteDimensional k (↥(repartitionSpace k F) ⧸
      (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (repartitionSpace k F)) := by
  obtain ⟨E, hDE, -, hEeq⟩ :=
    exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace hF hex D
  have h := finiteDimensional_quotient_adeleFiltration_sup_diagonalRepartitions hF hDE
  rwa [hEeq] at h

/-- **The index of specialty as a dimension** (Stichtenoth, Theorem 1.5.4):

`i(D) = dim_k (A_F ⧸ (A_F(D) + F))`

for every divisor `D` of an algebraic function field with exact constant field. -/
theorem finrank_quotient_repartitionSpace (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    (Module.finrank k (↥(repartitionSpace k F) ⧸
        (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (repartitionSpace k F)) : ℤ) =
      Divisor.indexOfSpecialty D := by
  obtain ⟨E, hDE, hiE, hEeq⟩ :=
    exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace hF hex D
  have h := finrank_quotient_adeleFiltration_sup_diagonalRepartitions hF hDE
  rwa [hEeq, hiE, sub_zero] at h

/-- **The genus as a dimension** (Stichtenoth, Corollary 1.5.5):
`g = dim_k (A_F ⧸ (A_F(0) + F))`, the case `D = 0` of Theorem 1.5.4, where `ℓ(0) = 1` because the
constant field is exact. -/
theorem finrank_quotient_repartitionSpace_zero (hex : IsIntegrallyClosedIn k F) :
    Module.finrank k (↥(repartitionSpace k F) ⧸
        (adeleFiltration (0 : Divisor k F) ⊔ diagonalRepartitions k F).submoduleOf
          (repartitionSpace k F)) = genus k F := by
  have h := finrank_quotient_repartitionSpace hF hex (0 : Divisor k F)
  rw [Divisor.indexOfSpecialty_def, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex,
    Divisor.degree_zero] at h
  omega

/-- **The divisors whose repartitions and constants exhaust `A_F` are exactly the nonspecial
ones**: `A_F(D) + F = A_F` iff `i(D) = 0`. -/
theorem adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff
    (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    adeleFiltration D ⊔ diagonalRepartitions k F = repartitionSpace k F ↔
      Divisor.indexOfSpecialty D = 0 := by
  refine ⟨fun hD ↦ ?_, fun hD ↦ ?_⟩
  · have h := finrank_quotient_repartitionSpace hF hex D
    rw [hD, Submodule.submoduleOf_self] at h
    have : Subsingleton (↥(repartitionSpace k F) ⧸ (⊤ : Submodule k ↥(repartitionSpace k F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [Module.finrank_zero_of_subsingleton] at h
    omega
  · obtain ⟨E, hDE, hiE, hEeq⟩ :=
      exists_adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace hF hex D
    rw [← hEeq]
    exact adeleFiltration_sup_diagonalRepartitions_eq_of_indexOfSpecialty_eq hF hDE (by omega)

end TauCeti
