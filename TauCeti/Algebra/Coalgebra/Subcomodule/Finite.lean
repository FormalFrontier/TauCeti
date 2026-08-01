/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Finite subcomodules

This file proves that, when the coalgebra is free as a module over a commutative
semiring, every element of a right comodule is contained in a finitely generated
subcomodule. The carrier is the span of the finitely many coefficients occurring
when the element's coaction is expanded in a basis of the coalgebra. The counit
shows that the original element lies in this span, and coordinate slices of
coassociativity show that the span is stable under the coaction.

No flatness or noetherian hypothesis is needed.

## Main declarations

* `TauCeti.Subcomodule.exists_finite_subcomodule_mem`: every element belongs to a
  subcomodule whose underlying module is finite.

## References

See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

private theorem coeff_rTensor_coact
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C) (x : M ⊗[R] C) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b
        ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C x) i =
      Comodule.coact (R := R) (C := C) (M := M)
        (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => simp [hx, hy]

omit [Coalgebra R C] [Comodule R C M] in
private theorem coeff_assoc_symm_tmul
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C)
    (m : M) (x : C ⊗[R] C) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b
        ((TensorProduct.assoc R M C C).symm (m ⊗ₜ[R] x)) i =
      m ⊗ₜ[R]
        TensorProduct.rid R C ((b.coord i).lTensor C x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c d => simp
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hx, hy]

/-- If a coalgebra is free as a module over a commutative semiring, every element
of a right comodule belongs to a subcomodule that is finitely generated as a
module. -/
theorem exists_finite_subcomodule_mem [Module.Free R C] (m : M) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N := by
  classical
  let b := Module.Free.chooseBasis R C
  let a := TensorProduct.equivFinsuppOfBasisRight b
    (Comodule.coact (R := R) (C := C) (M := M) m)
  let N := Submodule.span R (Set.range a)
  have ha_mem (i : Module.Free.ChooseBasisIndex R C) : a i ∈ N :=
    Submodule.subset_span (Set.mem_range_self i)
  have hstable :
      ∀ n ∈ N,
        Comodule.coact (R := R) (C := C) (M := M) n ∈
          LinearMap.range
            (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C)) := by
    intro n hn
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hn
    · rintro _ ⟨i, rfl⟩
      have hcoassoc :
          (Comodule.coact (R := R) (C := C) (M := M)).rTensor C
              (Comodule.coact (R := R) (C := C) (M := M) m) =
            (TensorProduct.assoc R M C C).symm
              (Coalgebra.comul.lTensor M
                (Comodule.coact (R := R) (C := C) (M := M) m)) := by
        apply (TensorProduct.assoc R M C C).injective
        simp
      have hcoeff := congrArg
        (fun x : (M ⊗[R] C) ⊗[R] C =>
          TensorProduct.equivFinsuppOfBasisRight b x i) hcoassoc
      rw [coeff_rTensor_coact] at hcoeff
      rw [hcoeff]
      rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply
        (Comodule.coact (R := R) (C := C) (M := M) m)]
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
      simp only [Finsupp.sum, map_sum]
      rw [Finsupp.finsetSum_apply]
      apply Submodule.sum_mem
      intro j _
      refine ⟨(⟨a j, ha_mem j⟩ : N) ⊗ₜ[R]
        TensorProduct.rid R C
          ((b.coord i).lTensor C (Coalgebra.comul (b j))), ?_⟩
      simp [a, coeff_assoc_symm_tmul]
    · intro x y _ _ hx hy
      simpa only [map_add] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).add_mem hx hy
    · intro r x _ hx
      simpa only [map_smul] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).smul_mem r hx
  let S := ofSubmodule (R := R) (C := C) (M := M) N hstable
  refine ⟨S, ?_, ?_⟩
  · have hSN : S.toSubmodule = N := by
      rw [toSubmodule_carrier]
      exact ofSubmodule_carrier N hstable
    rw [hSN]
    exact Module.Finite.span_of_finite R a.finite_range
  · apply mem_ofSubmodule.mpr
    have hcounit := Comodule.lTensor_counit_coact (R := R) (C := C) (M := M) m
    rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply
      (Comodule.coact (R := R) (C := C) (M := M) m)] at hcounit
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hcounit
    apply_fun TensorProduct.rid R M at hcounit
    simp only [Finsupp.sum, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      one_smul] at hcounit
    rw [← hcounit]
    exact Submodule.sum_mem N fun i _ => N.smul_mem _ (ha_mem i)

end Subcomodule

end TauCeti
