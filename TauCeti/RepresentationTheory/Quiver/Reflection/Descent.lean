/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.RepresentationTheory.Quiver.Reflection.Coxeter

/-!
# The Coxeter transformation drives a dimension vector out of the positive cone

Let `Q` be a finite quiver whose Tits form is positive definite, the numerical side of the ADE
condition in Gabriel's theorem. This file proves that the Coxeter transformation `c`, the
composite of the simple reflections along a repetition-free word running over every vertex, moves
every nonzero dimension vector out of the positive cone: for every `d ≠ 0` some iterate `cᴺ d` has
a negative coordinate (`TauCeti.exists_vertexPreReflectionList_pow_apply_neg`).

This is the descent that the Bernstein-Gelfand-Ponomarev proof of Gabriel's theorem runs on the
representation side. A finite-dimensional representation has a nonnegative dimension vector, and
`TauCeti.indecomposable_and_dimVector_coxeterFunctor_or_isZero` says that a pass of the Coxeter
functor over an indecomposable either applies `c` to its dimension vector or annihilates it. Since
`c` cannot keep a nonzero dimension vector nonnegative forever, some pass must annihilate the
representation, that is, must meet the vertex simple at the sink it is reflecting; iterating that
observation is the induction that carries an indecomposable down to a vertex simple, and its
dimension vector down to a simple root.

## Main results

* `TauCeti.isEmpty_hom_self_of_titsForm_posDef`: a positive definite Tits form forces every vertex
  to be loopless, so the reflection identities are available without a separate hypothesis.
* `TauCeti.exists_vertexPreReflectionList_pow_apply_neg`: **the descent.** No nonzero dimension
  vector stays nonnegative under all iterates of the Coxeter transformation.

## Implementation notes

The proof is the finite-orbit argument, and it needs no root-system combinatorics. The iterates
`cᴺ d` all have the same Tits value, and a positive definite integral quadratic form takes each
value only finitely often
(`QuadraticMap.PosDef.finite_setOf_apply_eq`), so the orbit repeats: `cᵖ x = x` for some
`x = cᴺ d` and some `p > 0`. Were every iterate nonnegative, the sum `x + c x + ⋯ + cᵖ⁻¹ x` over one
period would be a nonzero vector fixed by `c`, which
`TauCeti.vertexPreReflectionList_eq_self_iff_of_anisotropic` forbids.

The word is an explicit argument rather than a chosen sink-admissible ordering, matching
`TauCeti.vertexPreReflectionList` and `TauCeti.coxeterFunctor`: the transformation depends on the
ordering, so a consumer that names one must be able to pass it.

## References

This is the "descent by height" milestone of the reflection induction in Layer 5, Gabriel's
theorem, of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

universe u v

section Orbit

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : Module.End R M)

/-- An orbit contained in a finite set returns to one of its own points. -/
private theorem exists_pos_pow_apply_eq (v : M) {s : Set M} (hs : s.Finite)
    (hmem : ∀ N : ℕ, (f ^ N) v ∈ s) :
    ∃ N p : ℕ, 0 < p ∧ (f ^ p) ((f ^ N) v) = (f ^ N) v := by
  have := hs.to_subtype
  have key : ∀ m n : ℕ, m < n → (f ^ m) v = (f ^ n) v →
      ∃ N p : ℕ, 0 < p ∧ (f ^ p) ((f ^ N) v) = (f ^ N) v := fun m n hmn hv ↦
    ⟨m, n - m, by omega, by
      rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hmn)]
      exact hv.symm⟩
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun N : ℕ ↦ (⟨(f ^ N) v, hmem N⟩ : s)
  have heq' : (f ^ a) v = (f ^ b) v := congrArg Subtype.val heq
  rcases hab.lt_or_gt with h | h
  · exact key a b h heq'
  · exact key b a h heq'.symm

/-- The sum of an orbit over one period is fixed. -/
private theorem apply_sum_range_pow {x : M} {p : ℕ} (hfix : (f ^ p) x = x) :
    f (∑ j ∈ Finset.range p, (f ^ j) x) = ∑ j ∈ Finset.range p, (f ^ j) x := by
  rw [map_sum, Finset.sum_congr rfl fun j _ ↦ (by rw [pow_succ', Module.End.mul_apply] :
    f ((f ^ j) x) = (f ^ (j + 1)) x)]
  have h1 := Finset.sum_range_succ' (fun j ↦ (f ^ j) x) p
  have h2 := Finset.sum_range_succ (fun j ↦ (f ^ j) x) p
  simp only [pow_zero, Module.End.one_apply] at h1
  rw [hfix] at h2
  exact add_right_cancel (h1.symm.trans h2)

end Orbit

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

variable [DecidableEq Q]

/-- **The Coxeter transformation drives every nonzero dimension vector out of the positive cone.**
For a quiver with positive definite Tits form and a repetition-free word `l` running over all the
vertices, no nonzero `d` has all of its iterates under the reflection product along `l`
nonnegative. Nonnegativity of `d` itself is not assumed: at `N = 0` the conclusion is just that `d`
has a negative coordinate.

On the representation side this is the descent of the Bernstein-Gelfand-Ponomarev induction: a
dimension vector is nonnegative, so an indecomposable representation cannot survive arbitrarily
many passes of the Coxeter functor, and the pass that kills it meets a vertex simple. -/
theorem exists_vertexPreReflectionList_pow_apply_neg (hpd : (titsForm Q).PosDef) {l : List Q}
    (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l) {d : Q → ℤ} (hd0 : d ≠ 0) :
    ∃ (N : ℕ) (i : Q), (vertexPreReflectionList Q l ^ N) d i < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hloop : ∀ i ∈ l, IsEmpty (i ⟶ i) := fun i _ ↦ isEmpty_hom_self_of_titsForm_posDef Q hpd i
  set c := vertexPreReflectionList Q l with hc
  have hnn : ∀ N : ℕ, 0 ≤ (c ^ N) d := fun N ↦ Pi.le_def.mpr fun i ↦ hcon N i
  -- Every iterate has the same Tits value, so the orbit lies in a level set.
  have hc_preserves (y : Q → ℤ) : titsForm Q (c y) = titsForm Q y := by
    rw [hc]
    exact titsForm_vertexPreReflectionList Q hloop y
  have hlevel : ∀ N : ℕ, titsForm Q ((c ^ N) d) = titsForm Q d := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ', Module.End.mul_apply, hc_preserves, ih]
  -- The level set is finite, so the orbit returns to one of its own points.
  have hfin : {x : Q → ℤ | titsForm Q x = titsForm Q d}.Finite :=
    QuadraticMap.PosDef.finite_setOf_apply_eq hpd _
  obtain ⟨N, p, hp, hfix⟩ := exists_pos_pow_apply_eq c d hfin hlevel
  set x := (c ^ N) d with hx
  have hxnn : ∀ j : ℕ, 0 ≤ (c ^ j) x := by
    intro j
    rw [hx, ← Module.End.mul_apply, ← pow_add]
    exact hnn (j + N)
  have hx0 : x ≠ 0 := by
    have hinj : Function.Injective ⇑(c ^ N) := by
      rw [Module.End.coe_pow]
      exact ((vertexPreReflectionList_bijective Q hloop).1).iterate N
    rw [hx]
    intro h
    exact hd0 (hinj (by rw [h, map_zero]))
  -- The sum over one period is a vector fixed by the Coxeter transformation, hence zero.
  have hy0 : (∑ j ∈ Finset.range p, (c ^ j) x) = 0 :=
    (vertexPreReflectionList_eq_self_iff_of_anisotropic Q hpd.anisotropic hnd hmem _).mp
      (apply_sum_range_pow c hfix)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  have hxi : 0 < x i := lt_of_le_of_ne (by simpa using Pi.le_def.mp (hnn N) i) (Ne.symm hi)
  have hsum : ∑ j ∈ Finset.range p, ((c ^ j) x) i = 0 := by
    simpa using congrFun hy0 i
  have hpos : 0 < ∑ j ∈ Finset.range p, ((c ^ j) x) i :=
    Finset.sum_pos' (fun j _ ↦ by simpa using Pi.le_def.mp (hxnn j) i)
      ⟨0, Finset.mem_range.mpr hp, by simpa using hxi⟩
  exact hpos.ne' hsum

end TauCeti
