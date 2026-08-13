/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Separation by algebraically closed points

Let `A` be a commutative algebra of finite type over a field `k`, and let `K` be an
algebraically closed extension of `k`. An element of `A` vanishes under every `k`-algebra
homomorphism `A →ₐ[k] K` exactly when it is nilpotent. In particular, when `A` is reduced,
its `K`-valued points separate elements of `A`.

The proof is the weak Nullstellensatz in intrinsic form. A finite-type algebra over a field is a
Jacobson ring, so a non-nilpotent element is avoided by some maximal ideal. The residue field at
that ideal is finite over `k` by Zariski's lemma and therefore embeds into `K`.

## Main declarations

* `TauCeti.exists_algHom_apply_ne_zero_of_notMem_radical`: an element outside the radical of an
  ideal is nonzero at some algebraically closed point annihilating the ideal.
* `TauCeti.mem_radical_iff_forall_algHom_apply_eq_zero`: the intrinsic affine
  Nullstellensatz for finite-type algebras.
* `TauCeti.exists_algHom_apply_ne_zero_of_not_isNilpotent`: a non-nilpotent element is nonzero at
  some algebraically closed point.
* `TauCeti.forall_algHom_apply_eq_zero_iff_isNilpotent`: the common kernel of all algebraically
  closed points is the nilradical.
* `TauCeti.exists_algHom_apply_ne_of_ne`: points of a reduced finite-type algebra distinguish
  distinct elements.
* `TauCeti.eq_of_forall_algHom_apply_eq`: the corresponding point-separation principle.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Chapter 4.
* The Stacks Project, Tag 00FV, *Hilbert Nullstellensatz*.

This is the reduced finite-type point-separation prerequisite for Layer 5, "Unipotent groups",
of `TauCetiRoadmap/ReductiveGroups/README.md`. It turns pointwise identities over an algebraic
closure into identities in a smooth affine group's coordinate algebra.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {A : Type v} {K : Type w}
  [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  [Field K] [Algebra k K] [IsAlgClosed K]

/-- An element outside the radical of an ideal in a finite-type algebra over a field is nonzero
at some algebraically closed point annihilating that ideal. -/
theorem exists_algHom_apply_ne_zero_of_notMem_radical (I : Ideal A) {x : A}
    (hx : x ∉ I.radical) :
    ∃ f : A →ₐ[k] K, I ≤ RingHom.ker f.toRingHom ∧ f x ≠ 0 := by
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : I.radical.jacobson = I.radical :=
    IsJacobsonRing.out (R := A) (by infer_instance) (Ideal.radical_isRadical I)
  obtain ⟨m, ⟨hIm, hm⟩, hxm⟩ :=
    (Ideal.eq_jacobson_iff_notMem.mp hjac) x hx
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let ι : A ⧸ m →ₐ[k] K := IsAlgClosed.lift
  let f : A →ₐ[k] K := ι.comp (Ideal.Quotient.mkₐ k m)
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    rw [RingHom.mem_ker]
    simp [f, Ideal.Quotient.eq_zero_iff_mem.mpr (hIm (Ideal.le_radical hy))]
  · intro hxzero
    apply hxm
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact ι.injective (by simpa [f] using hxzero)

/-- The intrinsic affine Nullstellensatz for a finite-type algebra over a field: an element lies
in the radical of an ideal exactly when every algebraically closed point annihilating the ideal
also annihilates the element. -/
theorem mem_radical_iff_forall_algHom_apply_eq_zero (I : Ideal A) (x : A) :
    x ∈ I.radical ↔
      ∀ f : A →ₐ[k] K, I ≤ RingHom.ker f.toRingHom → f x = 0 := by
  constructor
  · intro hx f hIf
    rw [← RingHom.mem_ker]
    exact ((RingHom.ker_isPrime f.toRingHom).radical_le_iff.mpr hIf) hx
  · intro h
    by_contra hx
    obtain ⟨f, hIf, hf⟩ :=
      exists_algHom_apply_ne_zero_of_notMem_radical (k := k) (K := K) I hx
    exact hf (h f hIf)

/-- A non-nilpotent element of a finite-type algebra over a field is nonzero at some point valued
in any algebraically closed extension of the ground field. -/
theorem exists_algHom_apply_ne_zero_of_not_isNilpotent {x : A} (hx : ¬ IsNilpotent x) :
    ∃ f : A →ₐ[k] K, f x ≠ 0 := by
  have hxrad : x ∉ nilradical A := by
    rwa [mem_nilradical]
  obtain ⟨f, _, hf⟩ :=
    exists_algHom_apply_ne_zero_of_notMem_radical (k := k) (K := K) ⊥ hxrad
  exact ⟨f, hf⟩

/-- An element of a finite-type algebra over a field vanishes at every point valued in an
algebraically closed extension exactly when it is nilpotent. Equivalently, the common kernel of
all such points is the nilradical. -/
theorem forall_algHom_apply_eq_zero_iff_isNilpotent (x : A) :
    (∀ f : A →ₐ[k] K, f x = 0) ↔ IsNilpotent x := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨f, hf⟩ :=
      exists_algHom_apply_ne_zero_of_not_isNilpotent (k := k) (A := A) (K := K) hx
    exact hf (h f)
  · intro hx f
    exact isNilpotent_iff_eq_zero.mp (hx.map f)

variable [IsReduced A]

/-- A nonzero element of a reduced finite-type algebra over a field is nonzero at some point
valued in any algebraically closed extension of the ground field. -/
theorem exists_algHom_apply_ne_zero_of_ne_zero {x : A} (hx : x ≠ 0) :
    ∃ f : A →ₐ[k] K, f x ≠ 0 :=
  exists_algHom_apply_ne_zero_of_not_isNilpotent (k := k) (A := A) (K := K) <| by
    simpa [isReduced_iff] using hx

/-- Two elements of a reduced finite-type algebra over a field are distinguished by a point
valued in any algebraically closed extension whenever they are distinct. -/
theorem exists_algHom_apply_ne_of_ne {x y : A} (hxy : x ≠ y) :
    ∃ f : A →ₐ[k] K, f x ≠ f y := by
  obtain ⟨f, hf⟩ :=
    exists_algHom_apply_ne_zero_of_ne_zero (k := k) (A := A) (K := K) (sub_ne_zero.mpr hxy)
  exact ⟨f, sub_ne_zero.mp (by simpa using hf)⟩

/-- Algebraically closed points separate the elements of a reduced finite-type algebra over a
field. -/
theorem eq_of_forall_algHom_apply_eq {x y : A} (h : ∀ f : A →ₐ[k] K, f x = f y) :
    x = y := by
  by_contra hxy
  obtain ⟨f, hf⟩ := exists_algHom_apply_ne_of_ne (k := k) (A := A) (K := K) hxy
  exact hf (h f)

/-- Evaluation on all algebraically closed points is injective for a reduced finite-type algebra
over a field. -/
theorem algHom_evaluation_injective :
    Function.Injective (fun x : A ↦ fun f : A →ₐ[k] K ↦ f x) := by
  intro x y h
  exact eq_of_forall_algHom_apply_eq (k := k) (A := A) (K := K) fun f ↦ congrFun h f

end TauCeti
