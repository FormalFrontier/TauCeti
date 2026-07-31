/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: none of these appears in the type of an exported declaration. The centralizer
-- subalgebra is used only inside the proof of `forall_commute_tmul_one_iff`, and freeness of a
-- vector space and injectivity of `Algebra.TensorProduct.includeRight` only inside the proof of
-- the centrality instance.
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# The tensor product of two central algebras is central

Mathlib's `Mathlib/Algebra/Central/TensorProduct.lean` has the two *converse* statements
(`Algebra.IsCentral.left_of_tensor_of_field` and `Algebra.IsCentral.right_of_tensor_of_field`), but
not the forward one. This file supplies it, over a field, together with the elementwise centralizer
computation it rests on.

## Main results

* `TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff`: for `A` central over `K`, the
  centralizer of `A ⊗ 1` in `A ⊗[K] B` is exactly `1 ⊗ B`. This is Mathlib's
  `Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct` specialized to
  `Z(A) = K` and phrased elementwise. It is stated over a commutative base ring with `B` free, the
  hypotheses that theorem needs; the case of a field is picked up by typeclass inference.
* `TauCeti.Algebra.IsCentral.tensorProduct`: `A ⊗[K] B` is central when both factors are.

The companion simplicity statement, `TauCeti.IsSimpleRing.tensorProduct`, is in
`TauCeti/Algebra/CentralSimple/TensorProduct.lean`; together the two say that central simple
`K`-algebras are closed under `⊗[K]`. That closure is what lets the tensor product descend to a
multiplication on Brauer classes, and it is also the step behind base change.

## References

This is part of the **Tensor product of central simple is central simple** bullet of Layer 4 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and P. Gille, T. Szamuely, *Central
Simple Algebras and Galois Cohomology*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Algebra.TensorProduct

variable {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]

/-- **The centralizer of `A ⊗ 1` in `A ⊗[K] B` is `1 ⊗ B`**, for `A` a central `K`-algebra and `B`
free: an element of `A ⊗[K] B` commutes with every `a ⊗ₜ 1` exactly when it is of the form
`1 ⊗ₜ b`.

This is Mathlib's `Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct`, which
computes that centralizer as `Z(A) ⊗ B`, specialized to `Z(A) = K` and repackaged as a statement
about elements. Centrality of `A` is what shrinks the centralizer to `1 ⊗ B`; without it `Z(A) ⊗ B`
can be strictly larger. -/
theorem forall_commute_tmul_one_iff [Module.Free K B] [Algebra.IsCentral K A] {x : A ⊗[K] B} :
    (∀ a : A, Commute (a ⊗ₜ[K] (1 : B)) x) ↔ ∃ b : B, x = 1 ⊗ₜ[K] b := by
  refine ⟨fun h => ?_, ?_⟩
  · have hx : x ∈ Subalgebra.centralizer K
        ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).range : Set (A ⊗[K] B)) := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      simpa using (h a).eq
    rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct,
      Algebra.IsCentral.center_eq_bot] at hx
    obtain ⟨y, rfl⟩ := hx
    clear h
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp a.2
      exact ⟨k • b, by
        simp [← hk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
    | add y z hy hz =>
      obtain ⟨b, hb⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨b + c, by rw [map_add, hb, hc, TensorProduct.tmul_add]⟩
  · rintro ⟨b, rfl⟩ a
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]

end Algebra.TensorProduct

namespace Algebra.IsCentral

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

variable (K A B) in
/-- **The tensor product of two central `K`-algebras is central.** Mathlib has the two converses
(`Algebra.IsCentral.left_of_tensor_of_field` and `Algebra.IsCentral.right_of_tensor_of_field`);
this is the forward implication. -/
instance tensorProduct [Algebra.IsCentral K A] [Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) where
  out x hx := by
    rcases subsingleton_or_nontrivial A with _ | _
    -- If `A` is trivial then so is `A ⊗[K] B`, and every element of a trivial algebra is in `⊥`.
    · have : Subsingleton (A ⊗[K] B) :=
        subsingleton_of_zero_eq_one <| by
          rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, TensorProduct.zero_tmul]
      rw [Algebra.mem_bot]
      exact ⟨0, Subsingleton.elim _ _⟩
    rw [Subalgebra.mem_center_iff] at hx
    obtain ⟨b, rfl⟩ := Algebra.TensorProduct.forall_commute_tmul_one_iff.mp fun a => hx _
    have hbc : b ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro c
      have h := hx ((1 : A) ⊗ₜ[K] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
      exact Algebra.TensorProduct.includeRight_injective
        (FaithfulSMul.algebraMap_injective K A) h
    obtain ⟨k, rfl⟩ := (Algebra.IsCentral.mem_center_iff K).mp hbc
    rw [Algebra.mem_bot]
    exact ⟨k, by simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]⟩

end Algebra.IsCentral

end TauCeti
