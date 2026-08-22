/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Idempotents

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
* `TauCeti.eq_one_of_isIdempotentElem_of_forall_algHom_apply_eq_one`: an idempotent evaluating to
  one at every algebraically closed point is one.
* `TauCeti.eq_of_isIdempotentElem_of_forall_algHom_apply_eq`: two idempotents that agree at every
  algebraically closed point are equal.
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

/-- An idempotent in a finite-type algebra that evaluates to one at every algebraically closed
point is one. -/
theorem eq_one_of_isIdempotentElem_of_forall_algHom_apply_eq_one {a : A}
    (ha : IsIdempotentElem a) (h : ∀ f : A →ₐ[k] K, f a = 1) : a = 1 := by
  apply _root_.eq_of_isNilpotent_sub_of_isIdempotentElem ha IsIdempotentElem.one
  rw [← forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := K)]
  intro f
  rw [map_sub, map_one, sub_eq_zero]
  exact h f

/-- Two idempotents in a finite-type algebra are equal when they have the same value at every
point valued in an algebraically closed extension of the ground field. No reducedness assumption
is needed: idempotents are already insensitive to nilpotents. -/
theorem eq_of_isIdempotentElem_of_forall_algHom_apply_eq {a b : A}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : ∀ f : A →ₐ[k] K, f a = f b) : a = b := by
  let x := a * b
  let y := (1 - a) * (1 - b)
  let c := x + y
  have hc : IsIdempotentElem c := by
    have hx : IsIdempotentElem x := ha.mul hb
    have hy : IsIdempotentElem y := ha.one_sub.mul hb.one_sub
    have hxy : x * y = 0 := by
      dsimp only [x, y]
      calc
        a * b * ((1 - a) * (1 - b)) = (a * (1 - a)) * (b * (1 - b)) := by ring
        _ = 0 := by rw [mul_sub, mul_one, ha.eq, sub_self, zero_mul]
    dsimp only [c, IsIdempotentElem]
    rw [add_mul, mul_add, mul_add, hxy, mul_comm y x, hxy, hx.eq, hy.eq]
    simp
  have hc_one : c = 1 := by
    apply eq_one_of_isIdempotentElem_of_forall_algHom_apply_eq_one
      (k := k) (A := A) (K := K) hc
    intro (f : A →ₐ[k] K)
    dsimp only [c, x, y]
    calc
      f (a * b + (1 - a) * (1 - b)) =
          f (a * b) + f ((1 - a) * (1 - b)) := f.map_add _ _
      _ = f a * f b + f (1 - a) * f (1 - b) :=
        congrArg₂ (fun p q ↦ p + q) (f.map_mul _ _) (f.map_mul _ _)
      _ = f a * f b + (1 - f a) * (1 - f b) := by
        rw [map_sub, map_one, map_sub, map_one]
      _ = f b * f b + (1 - f b) * (1 - f b) := by rw [h f]
      _ = 1 - 2 * f b + 2 * (f b * f b) := by ring
      _ = 1 := by rw [(hb.map f).eq]; ring
  calc
    a = a * c := by rw [hc_one, mul_one]
    _ = a * b := by
      dsimp only [c, x, y]
      calc
        a * (a * b + (1 - a) * (1 - b)) =
            (a * a) * b + (a - a * a) * (1 - b) := by ring
        _ = a * b := by rw [ha.eq]; ring
    _ = b * c := by
      symm
      dsimp only [c, x, y]
      calc
        b * (a * b + (1 - a) * (1 - b)) =
            a * (b * b) + (1 - a) * (b - b * b) := by ring
        _ = a * b := by rw [hb.eq]; ring
    _ = b := by rw [hc_one, mul_one]

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
