/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
import TauCeti.LinearAlgebra.Trace.Nondegenerate
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Irreducible

/-!
# Kolchin's common fixed vector theorem

This file proves the linear-algebraic core of Kolchin's theorem: a monoid acting by unipotent
automorphisms on a nonzero finite-dimensional vector space over a field has a common nonzero fixed
vector. No commutativity or finiteness assumption is made on the monoid.

Over an algebraically closed field, the proof chooses a minimal nonzero invariant subspace and uses
Burnside density together with the nondegenerate trace pairing to show that every monoid element is
the identity there. Over an arbitrary field, extend scalars to an algebraic closure and descend a
fixed tensor by applying a base-field linear functional to its scalar coefficients.

## Main results

* `Representation.exists_common_fixed_vector_of_isUnipotent`: Kolchin's common fixed vector
  theorem.
* `Representation.exists_fixed_submodule_finrank_eq_one_of_isUnipotent`: the equivalent
  fixed-line form.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti.Representation

open scoped MonoidAlgebra TensorProduct

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [Monoid G] [AddCommGroup V] [Module K V]

private theorem _root_.Representation.exists_common_fixed_vector_of_isUnipotent_of_isAlgClosed
    [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V]
    (ρ : _root_.Representation K G V)
    (hunipotent : ∀ g, IsNilpotent (ρ g - 1)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  obtain ⟨S, hS, hSirr⟩ := exists_isIrreducible_subrepresentation ρ
  have hSne : S.toSubmodule ≠ ⊥ := fun h ↦
    hS (Subrepresentation.toSubmodule_injective
      (h.trans Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSne
  have hsurjective :=
    _root_.Representation.asAlgebraHom_surjective_of_isIrreducible S.toRepresentation hSirr
  have hSUnipotent (g : G) : IsNilpotent (S.toRepresentation g - 1) := by
    have hρ : Set.MapsTo (ρ g) S.toSubmodule S.toSubmodule :=
      S.apply_mem_toSubmodule g
    have h1 : Set.MapsTo (1 : Module.End K V) S.toSubmodule S.toSubmodule :=
      fun _ hx ↦ hx
    have hsub : Set.MapsTo ((ρ g : Module.End K V) - (1 : Module.End K V))
        S.toSubmodule S.toSubmodule :=
      fun _ hx ↦ S.toSubmodule.sub_mem (hρ hx) (h1 hx)
    have hrestrict := Module.End.isNilpotent.restrict hsub (hunipotent g)
    rw [Subrepresentation.toRepresentation_apply]
    have hone : (1 : Module.End K S.toSubmodule) =
        (1 : Module.End K V).restrict h1 := by
      simpa using (LinearMap.restrict_smul_one (p := S.toSubmodule) (1 : K)).symm
    rw [hone, LinearMap.restrict_sub hρ h1 hsub]
    exact hrestrict
  have htrace (g : G) :
      LinearMap.trace K S.toSubmodule (S.toRepresentation g) =
        (Module.finrank K S.toSubmodule : K) := by
    have hnil := LinearMap.isNilpotent_trace_of_isNilpotent (hSUnipotent g)
    rw [map_sub, LinearMap.trace_one] at hnil
    exact sub_eq_zero.mp hnil.eq_zero
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
        have hgh := htrace (g * h)
        have hh := htrace h
        rw [hgh, hh, sub_self, mul_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
  refine ⟨x, fun h ↦ hx (Subtype.ext h), fun g ↦ ?_⟩
  have hfixed := LinearMap.congr_fun (htrivial g) x
  exact congrArg Subtype.val hfixed

/-- **Kolchin's common fixed vector theorem.** If every element of a monoid acts unipotently on a
nonzero finite-dimensional vector space over a field, then the monoid fixes a nonzero vector. -/
theorem _root_.Representation.exists_common_fixed_vector_of_isUnipotent
    [FiniteDimensional K V] [Nontrivial V]
    (ρ : _root_.Representation K G V)
    (hunipotent : ∀ g, IsNilpotent (ρ g - 1)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  let A := AlgebraicClosure K
  let W := A ⊗[K] V
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos)
  let ρA := _root_.Representation.baseChange A ρ
  have hunipotentA (g : G) : IsNilpotent (ρA g - 1) := by
    simp only [ρA, _root_.Representation.baseChange_apply]
    have hbase (f : Module.End K V) :
        (Module.End.baseChangeHom K A V) f = f.baseChange A := rfl
    have h := (hunipotent g).map (Module.End.baseChangeHom K A V)
    rw [map_sub, map_one, hbase] at h
    exact h
  obtain ⟨w, hw, hfixed⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent_of_isAlgClosed
      ρA hunipotentA
  apply _root_.Representation.exists_common_fixed_vector_of_baseChange ρ hw
  simpa only [ρA] using hfixed

/-- Under Kolchin's hypotheses, the common fixed vectors contain a one-dimensional subspace. -/
theorem _root_.Representation.exists_fixed_submodule_finrank_eq_one_of_isUnipotent
    [FiniteDimensional K V] [Nontrivial V] (ρ : _root_.Representation K G V)
    (hunipotent : ∀ g, IsNilpotent (ρ g - 1)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧ ∀ g, ∀ x ∈ p, ρ g x = x := by
  apply TauCeti.exists_fixed_submodule_finrank_eq_one_of_exists_common_fixed_vector ρ
  exact _root_.Representation.exists_common_fixed_vector_of_isUnipotent ρ hunipotent

end

end TauCeti.Representation
