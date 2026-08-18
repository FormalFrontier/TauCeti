/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Unipotent
public import Mathlib.RepresentationTheory.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.Trace.Nondegenerate
import TauCeti.RepresentationTheory.Irreducible

/-!
# Kolchin's common fixed vector theorem

This file proves the linear-algebraic core of Kolchin's theorem: a group acting by unipotent
automorphisms on a nonzero finite-dimensional vector space over a field has a common nonzero fixed
vector. No commutativity or finiteness assumption is made on the group.

Over an algebraically closed field, the proof chooses a minimal nonzero invariant subspace and uses
Burnside density together with the nondegenerate trace pairing to show that every group element is
the identity there. Over an arbitrary field, extend scalars to an algebraic closure and descend a
fixed tensor by applying a base-field linear functional to its scalar coefficients.

## Main results

* `TauCeti.exists_common_fixed_vector_of_forall_isUnipotent`: Kolchin's common fixed vector
  theorem.
* `TauCeti.exists_fixed_submodule_finrank_eq_one_of_forall_isUnipotent`: the equivalent fixed-line
  form.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra TensorProduct

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [Group G] [AddCommGroup V] [Module K V]

private theorem exists_common_fixed_vector_of_forall_isUnipotent_of_isAlgClosed
    [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K G V)
    (hunipotent : ∀ g, LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  obtain ⟨S, hS, hSirr⟩ := Representation.exists_isIrreducible_subrepresentation ρ
  have hSne : S.toSubmodule ≠ ⊥ := fun h ↦
    hS (Subrepresentation.toSubmodule_injective
      (h.trans Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSne
  have hsurjective :=
    _root_.Representation.asAlgebraHom_surjective_of_isIrreducible S.toRepresentation hSirr
  have hSUnipotent (g : G) :
      LinearMap.GeneralLinearGroup.IsUnipotent (S.toRepresentation.asGroupHom g) :=
    TauCeti.GeneralLinearGroup.IsUnipotent.subrepresentation S g (hunipotent g)
  have htrivial (g : G) : S.toRepresentation g = 1 := by
    apply sub_eq_zero.mp
    apply LinearMap.eq_zero_of_trace_mul_eq_zero
    intro T
    obtain ⟨a, rfl⟩ := hsurjective T
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [mul_add, map_add] using congrArg₂ (fun x y ↦ x + y) ha hb
    | single h r =>
        rw [Representation.asAlgebraHom_single, mul_smul_comm, map_smul, smul_eq_mul]
        rw [sub_mul, one_mul, ← map_mul, map_sub]
        have hgh := TauCeti.GeneralLinearGroup.IsUnipotent.trace_eq_finrank
          (hSUnipotent (g * h))
        have hh := TauCeti.GeneralLinearGroup.IsUnipotent.trace_eq_finrank (hSUnipotent h)
        rw [Representation.asGroupHom_apply] at hgh hh
        rw [hgh, hh, sub_self, mul_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
  refine ⟨x, fun h ↦ hx (Subtype.ext h), fun g ↦ ?_⟩
  have hfixed := LinearMap.congr_fun (htrivial g) x
  exact congrArg Subtype.val hfixed

/-- **Kolchin's common fixed vector theorem.** If every element of a group acts unipotently on a
nonzero finite-dimensional vector space over a field, then the group fixes a nonzero vector. -/
theorem exists_common_fixed_vector_of_forall_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K G V)
    (hunipotent : ∀ g, LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  let A := AlgebraicClosure K
  let W := A ⊗[K] V
  let _ : Nontrivial W := Module.nontrivial_of_finrank_pos (by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos)
  let ρA : Representation A G W :=
    { toFun := fun g ↦ (ρ g).baseChange A
      map_one' := by simp only [map_one, LinearMap.baseChange_one]
      map_mul' := fun g h ↦ by
        rw [map_mul]
        exact LinearMap.baseChange_mul (ρ g) (ρ h) }
  have hunipotentA (g : G) :
      LinearMap.GeneralLinearGroup.IsUnipotent (ρA.asGroupHom g) := by
    rw [LinearMap.GeneralLinearGroup.isUnipotent_def, Representation.asGroupHom_apply]
    change IsNilpotent ((ρ g).baseChange A - 1)
    have hg : IsNilpotent (ρ g - 1) := by
      simpa only [LinearMap.GeneralLinearGroup.isUnipotent_def,
        Representation.asGroupHom_apply] using hunipotent g
    rw [← LinearMap.baseChange_one (A := A) K V, ← LinearMap.baseChange_sub]
    exact hg.map (Module.End.baseChangeHom K A V)
  obtain ⟨w, hw, hfixed⟩ :=
    exists_common_fixed_vector_of_forall_isUnipotent_of_isAlgClosed ρA hunipotentA
  let b := Module.Free.chooseBasis K V
  have hwrepr : (b.baseChange A).repr w ≠ 0 := fun h ↦
    hw ((b.baseChange A).repr.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hwrepr
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_ne_zero K hi
  let descend : W →ₗ[K] V := TensorProduct.lift ((LinearMap.lsmul K V).comp phi)
  have descend_repr (x : W) (j) :
      b.repr (descend x) j = phi ((b.baseChange A).repr x j) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        change b.repr (phi a • x) j = _
        simp [mul_comm]
    | add x y hx hy => simp [hx, hy]
  have descend_baseChange (f : Module.End K V) (x : W) :
      descend (f.baseChange A x) = f (descend x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        change phi a • f x = f (phi a • x)
        simp
    | add x y hx hy => simp [hx, hy]
  refine ⟨descend w, ?_, fun g ↦ ?_⟩
  · intro hzero
    apply hphi
    rw [← descend_repr w i, hzero]
    simp
  · rw [← descend_baseChange]
    change descend (ρA g w) = descend w
    rw [hfixed]

/-- Under Kolchin's hypotheses, the common fixed vectors contain a one-dimensional subspace. -/
theorem exists_fixed_submodule_finrank_eq_one_of_forall_isUnipotent
    [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V)
    (hunipotent : ∀ g, LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧ ∀ g, ∀ x ∈ p, ρ g x = x := by
  obtain ⟨v, hv, hfixed⟩ :=
    exists_common_fixed_vector_of_forall_isUnipotent ρ hunipotent
  refine ⟨K ∙ v, finrank_span_singleton hv, fun g x hx ↦ ?_⟩
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp [hfixed]

end

end TauCeti
