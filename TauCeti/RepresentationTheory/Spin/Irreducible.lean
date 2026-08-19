/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Dimension
public import TauCeti.RepresentationTheory.Spin.Structure
-- Private: `Submodule.projectionOnto` and its evaluation lemmas are used only inside proofs.
import Mathlib.LinearAlgebra.Projection
-- Private: `IsSimpleModule.toSpanSingleton_surjective` is used only inside proofs.
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The spinor module is simple, and its two halves are simple and inequivalent

The Fock model makes the exterior algebra `S = ⋀·W` of the isotropic summand of a polarization a
module over `CliffordAlgebra Q` (`TauCeti.spinAction`), and that action is onto the full
endomorphism algebra as soon as `W` is finite free (`TauCeti.spinAction_surjective`). A module on
which every endomorphism is realized has no proper nonzero submodule at all, so **the spinor module
is simple**, in every dimension and without any nondegeneracy hypothesis: this is
`TauCeti.exists_spinAction_eq`, that a nonzero spinor is carried to every other one, and
`TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`, its lattice form.

That is not yet the irreducibility the spin representation is named for, because in even dimension
`S` visibly splits, into the two half-spin summands `S⁺` and `S⁻` of `TauCeti.spinPlus` and
`TauCeti.spinMinus`. The splitting is invariant not under the whole Clifford algebra but under its
even subalgebra, and the theorem the splitting deserves is that the even subalgebra sees exactly
those two pieces and nothing finer:

`TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd :`
`  even Q ≃ₐ[K] Module.End K S⁺ × Module.End K S⁻`.

The proof does not count dimensions a second time. Surjectivity onto the *product* is the substance,
and it comes from the full structure theorem `TauCeti.spinAction_bijective` together with the
parity bookkeeping of `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`: an endomorphism of `S`
preserving both summands is `spinAction x` for a unique `x`, whose odd component acts both
parity-preservingly and parity-reversingly, hence acts as zero, hence vanishes. That is
`TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`, and everything else follows from it: the
two half-spin summands are simple over the even subalgebra
(`TauCeti.eq_bot_or_eq_top_of_map_spinPlusAction_le`) because each factor is a full endomorphism
algebra, and they are **inequivalent** (`TauCeti.not_exists_equiv_spinPlus_spinMinus`) because the
element of `even Q` acting as the identity on `S⁺` and as zero on `S⁻` kills any map that
intertwines them.

Simplicity is stated in its lattice form, as "an invariant subspace is `⊥` or everything", rather
than as `IsSimpleModule`: `S⁺` and `S⁻` carry no `Module (even Q)` instance, and manufacturing one
would mean a type synonym for a statement that reads no better through it.

The hypothesis `P.line = ⊥` is the even-dimensional case, and it is exactly what makes the parity
splitting a splitting of modules at all;
`TauCeti.SpinPolarizationData.even_finrank_of_line_eq_bot` turns it into the evenness the structure
theorem is stated with, so no separate parity hypothesis is carried. Simplicity of `S⁻` carries the
further hypothesis `W ≠ ⊥`, which rules out only the zero-dimensional quadratic space: there
`S = K` is entirely even, `S⁻` is zero, and there is nothing to be simple. `S⁺` always contains the
scalars, so it needs no such hypothesis, and neither does the inequivalence.

What is *not* proved here is irreducibility of the group representation `TauCeti.spinRep`, which
asks more: that the `K`-span of `spinGroup Q` inside `even Q` is all of it. Nor is the
odd-dimensional splitting of `CliffordAlgebra Q` into its two central summands, for which the
results here are the even-dimensional half.

## Main definitions

* `TauCeti.spinPlusAction` and `TauCeti.spinMinusAction`: the actions of the even Clifford
  subalgebra on the two half-spin summands, as algebra homomorphisms.
* `TauCeti.evenSpinAction`: the two of them together.
* `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`: **the even structure theorem**, that
  `even Q` is the product of the endomorphism algebras of the two half-spin summands.

## Main results

* `TauCeti.exists_spinAction_eq` and `TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`: **the spinor
  module is a simple Clifford module.**
* `TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`: a Clifford element whose action
  preserves both half-spin summands is even.
* `TauCeti.eq_bot_or_eq_top_of_map_spinPlusAction_le` and
  `TauCeti.eq_bot_or_eq_top_of_map_spinMinusAction_le`: **the half-spin summands are simple** over
  the even Clifford subalgebra.
* `TauCeti.not_exists_equiv_spinPlus_spinMinus`: **the half-spin summands are inequivalent.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the Clifford algebra of an even-dimensional space is the endomorphism algebra
  of `⋀·W`, its even subalgebra is the product of the endomorphism algebras of the two halves, and
  the two half-spin modules are irreducible and inequivalent.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The even-dimensional case", and Layer 4, "Irreducibility".
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

/-! ### The spinor module is a simple Clifford module

Nothing here needs an even dimension, a nondegenerate form, or an invertible `2`: the Fock action
is onto `Module.End K S` for every polarization whose isotropic summand is finite-dimensional, and
a vector space is a simple module over its own endomorphism ring. -/

section Simple

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [FiniteDimensional K P.W]

/-- **A nonzero spinor generates the spinor module**: some Clifford element carries it to any
prescribed spinor. The Fock action realizes every endomorphism of `S = ⋀·W`, and a vector space is
a simple module over its endomorphism ring. -/
theorem exists_spinAction_eq {s : ExteriorAlgebra K P.W} (hs : s ≠ 0)
    (t : ExteriorAlgebra K P.W) : ∃ x : CliffordAlgebra Q, spinAction Q P x s = t := by
  obtain ⟨f, hf⟩ := IsSimpleModule.toSpanSingleton_surjective
    (Module.End K (ExteriorAlgebra K P.W)) hs t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hf
  obtain ⟨x, rfl⟩ := spinAction_surjective P f
  exact ⟨x, hf⟩

/-- **The spinor module is a simple Clifford module**: a submodule of `S = ⋀·W` invariant under
every Clifford element is `⊥` or the whole of `S`. -/
theorem eq_bot_or_eq_top_of_map_spinAction_le (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ x : CliffordAlgebra Q, N.map (spinAction Q P x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨x, hx⟩ := exists_spinAction_eq P hs0 t
  exact hx ▸ hN x ⟨s, hs, rfl⟩

end Simple

/-! ### The even subalgebra acting on the two half-spin summands

A polarization without a line summand makes an even Clifford element act by a parity-preserving
operator, so it restricts to each of `S⁺` and `S⁻`. These restrictions are algebra homomorphisms,
defined here over the commutative ring the polarization lives over; that they are jointly bijective
is the even-dimensional statement of the next section. -/

section Restrict

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- **The action of the even Clifford subalgebra on the even half-spin summand** `S⁺`, for a
polarization without a line summand: an even element preserves exterior parity, so the Fock action
restricts to `S⁺`. -/
noncomputable def spinPlusAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (spinPlus Q P) where
  toFun x := (spinAction Q P x).restrict fun s hs => by
    rw [spinPlus_def] at hs ⊢
    exact spinAction_mem_evenOdd_of_mem_even P hline x.2 hs
  map_one' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_mul' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_zero' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_add' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  commutes' _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp

/-- **The action of the even Clifford subalgebra on the odd half-spin summand** `S⁻`. -/
noncomputable def spinMinusAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (spinMinus Q P) where
  toFun x := (spinAction Q P x).restrict fun s hs => by
    rw [spinMinus_def] at hs ⊢
    exact spinAction_mem_evenOdd_of_mem_even P hline x.2 hs
  map_one' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_mul' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_zero' := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  map_add' _ _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp
  commutes' _ := by refine LinearMap.ext fun s => Subtype.ext ?_; simp

variable (P : SpinPolarizationData Q)

/-- The action of an even Clifford element on `S⁺` is the Fock action. -/
@[simp]
theorem coe_spinPlusAction_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q)
    (s : spinPlus Q P) :
    (spinPlusAction Q P hline x s : ExteriorAlgebra K P.W) = spinAction Q P x s :=
  -- `(rfl)`, not `rfl`: the body of `spinPlusAction` is not `@[expose]`d.
  (rfl)

/-- The action of an even Clifford element on `S⁻` is the Fock action. -/
@[simp]
theorem coe_spinMinusAction_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q)
    (s : spinMinus Q P) :
    (spinMinusAction Q P hline x s : ExteriorAlgebra K P.W) = spinAction Q P x s :=
  -- `(rfl)`, not `rfl`: the body of `spinMinusAction` is not `@[expose]`d.
  (rfl)

/-- **The action of the even Clifford subalgebra on the two half-spin summands together.** -/
noncomputable def evenSpinAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (hline : P.line = ⊥) :
    CliffordAlgebra.even Q →ₐ[K]
      Module.End K (spinPlus Q P) × Module.End K (spinMinus Q P) :=
  (spinPlusAction Q P hline).prod (spinMinusAction Q P hline)

@[simp]
theorem evenSpinAction_apply (hline : P.line = ⊥) (x : CliffordAlgebra.even Q) :
    evenSpinAction Q P hline x =
      (spinPlusAction Q P hline x, spinMinusAction Q P hline x) :=
  -- `(rfl)`, not `rfl`: the body of `evenSpinAction` is not `@[expose]`d.
  (rfl)

end Restrict

/-! ### The even structure theorem

For an even-dimensional polarized quadratic space the Fock action is an isomorphism
`CliffordAlgebra Q ≃ₐ[K] Module.End K S`. Under it the even subalgebra is carried onto the
endomorphisms preserving the parity splitting `S = S⁺ ⊕ S⁻`, which is the product of the two
endomorphism algebras; that is the content of this section. -/

section Even

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

/-- **A Clifford element whose action preserves both half-spin summands is even.** Splitting it
into an even and an odd part, the odd part acts by an operator that both preserves and reverses
exterior parity, so it acts by zero; in even dimension the Fock action is faithful, so the odd part
itself vanishes. -/
theorem mem_even_of_map_spinPlus_le_of_map_spinMinus_le (hline : P.line = ⊥)
    {x : CliffordAlgebra Q}
    (hplus : (spinPlus Q P).map (spinAction Q P x) ≤ spinPlus Q P)
    (hminus : (spinMinus Q P).map (spinAction Q P x) ≤ spinMinus Q P) :
    x ∈ CliffordAlgebra.even Q := by
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1
    (show x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 by
      rw [codisjoint_iff.1 (CliffordAlgebra.evenOdd_isCompl (Q := Q)).codisjoint]; trivial)
  have hx₀even : x₀ ∈ CliffordAlgebra.even Q := by
    rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
    exact hx₀
  -- The odd part acts by zero on each summand, so by zero.
  have hsplit : ∀ s : ExteriorAlgebra K P.W,
      spinAction Q P x₁ s = spinAction Q P (x₀ + x₁) s - spinAction Q P x₀ s := by
    intro s
    rw [map_add]
    simp
  have hzeroplus : ∀ s ∈ spinPlus Q P, spinAction Q P x₁ s = 0 := by
    intro s hs
    have h₁ : spinAction Q P x₁ s ∈ spinMinus Q P :=
      map_spinAction_spinPlus_le_spinMinus P hline hx₁ ⟨s, hs, rfl⟩
    have h₂ : spinAction Q P x₁ s ∈ spinPlus Q P := by
      rw [hsplit s]
      refine Submodule.sub_mem _ (hplus ⟨s, hs, rfl⟩) ?_
      rw [spinPlus_def] at hs ⊢
      exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs
    have : spinAction Q P x₁ s ∈ (⊥ : Submodule K (ExteriorAlgebra K P.W)) := by
      rw [← spinPlus_inf_spinMinus P]; exact ⟨h₂, h₁⟩
    simpa using this
  have hzerominus : ∀ s ∈ spinMinus Q P, spinAction Q P x₁ s = 0 := by
    intro s hs
    have h₁ : spinAction Q P x₁ s ∈ spinPlus Q P :=
      map_spinAction_spinMinus_le_spinPlus P hline hx₁ ⟨s, hs, rfl⟩
    have h₂ : spinAction Q P x₁ s ∈ spinMinus Q P := by
      rw [hsplit s]
      refine Submodule.sub_mem _ (hminus ⟨s, hs, rfl⟩) ?_
      rw [spinMinus_def] at hs ⊢
      exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs
    have : spinAction Q P x₁ s ∈ (⊥ : Submodule K (ExteriorAlgebra K P.W)) := by
      rw [← spinPlus_inf_spinMinus P]; exact ⟨h₁, h₂⟩
    simpa using this
  have hzero : spinAction Q P x₁ = 0 := by
    refine LinearMap.ext fun s => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
      (show s ∈ spinPlus Q P ⊔ spinMinus Q P by rw [spinPlus_sup_spinMinus P]; trivial)
    rw [map_add, hzeroplus a ha, hzerominus b hb, add_zero, LinearMap.zero_apply]
  have hx₁zero : x₁ = 0 :=
    spinAction_injective P (P.even_finrank_of_line_eq_bot hline) (by rw [hzero, map_zero])
  rw [hx₁zero, add_zero]
  exact hx₀even

/-- **An endomorphism of the spinor module preserving both half-spin summands is the action of an
even Clifford element.** -/
theorem exists_mem_even_spinAction_eq (hline : P.line = ⊥)
    (f : Module.End K (ExteriorAlgebra K P.W))
    (hplus : (spinPlus Q P).map f ≤ spinPlus Q P)
    (hminus : (spinMinus Q P).map f ≤ spinMinus Q P) :
    ∃ x : CliffordAlgebra.even Q, spinAction Q P x = f := by
  obtain ⟨y, rfl⟩ := spinAction_surjective P f
  exact ⟨⟨y, mem_even_of_map_spinPlus_le_of_map_spinMinus_le P hline hplus hminus⟩, rfl⟩

/-- **The even subalgebra acts faithfully on the pair of half-spin summands.** An even element
acting by zero on both acts by zero on their sum, which is all of `S`, and in even dimension the
Fock action is faithful. -/
theorem evenSpinAction_injective (hline : P.line = ⊥) :
    Function.Injective (evenSpinAction Q P hline) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [evenSpinAction_apply, Prod.mk_eq_zero] at hx
  have hzero : spinAction Q P x = 0 := by
    refine LinearMap.ext fun s => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
      (show s ∈ spinPlus Q P ⊔ spinMinus Q P by rw [spinPlus_sup_spinMinus P]; trivial)
    have h₁ : spinAction Q P x a = 0 := by
      have := congrArg (fun g : Module.End K (spinPlus Q P) => (g ⟨a, ha⟩ : ExteriorAlgebra K P.W))
        hx.1
      simpa using this
    have h₂ : spinAction Q P x b = 0 := by
      have := congrArg (fun g : Module.End K (spinMinus Q P) => (g ⟨b, hb⟩ : ExteriorAlgebra K P.W))
        hx.2
      simpa using this
    rw [map_add, h₁, h₂, add_zero, LinearMap.zero_apply]
  exact Subtype.ext
    (spinAction_injective P (P.even_finrank_of_line_eq_bot hline) (by simp [hzero]))

/-- **The even subalgebra exhausts the pair of endomorphism algebras.** A pair of endomorphisms of
the two summands assembles, along the splitting `S = S⁺ ⊕ S⁻`, into a parity-preserving
endomorphism of `S`, and those are exactly the actions of even Clifford elements. -/
theorem evenSpinAction_surjective (hline : P.line = ⊥) :
    Function.Surjective (evenSpinAction Q P hline) := by
  rintro ⟨g₁, g₂⟩
  have hc := isCompl_spinPlus_spinMinus P
  set f : Module.End K (ExteriorAlgebra K P.W) :=
    (spinPlus Q P).subtype ∘ₗ g₁ ∘ₗ (spinPlus Q P).projectionOnto (spinMinus Q P) hc +
      (spinMinus Q P).subtype ∘ₗ g₂ ∘ₗ (spinMinus Q P).projectionOnto (spinPlus Q P) hc.symm
    with hfdef
  have hfplus : ∀ (s : ExteriorAlgebra K P.W) (hs : s ∈ spinPlus Q P),
      f s = (g₁ ⟨s, hs⟩ : ExteriorAlgebra K P.W) := by
    intro s hs
    rw [hfdef]
    simp [Submodule.projectionOnto_apply_of_mem_left hc hs,
      Submodule.projectionOnto_apply_of_mem_right hc.symm hs]
  have hfminus : ∀ (s : ExteriorAlgebra K P.W) (hs : s ∈ spinMinus Q P),
      f s = (g₂ ⟨s, hs⟩ : ExteriorAlgebra K P.W) := by
    intro s hs
    rw [hfdef]
    simp [Submodule.projectionOnto_apply_of_mem_left hc.symm hs,
      Submodule.projectionOnto_apply_of_mem_right hc hs]
  obtain ⟨x, hx⟩ := exists_mem_even_spinAction_eq P hline f
    (by rintro _ ⟨s, hs, rfl⟩; rw [hfplus s hs]; exact (g₁ ⟨s, hs⟩).2)
    (by rintro _ ⟨s, hs, rfl⟩; rw [hfminus s hs]; exact (g₂ ⟨s, hs⟩).2)
  refine ⟨x, ?_⟩
  rw [evenSpinAction_apply, Prod.mk.injEq]
  constructor
  · refine LinearMap.ext fun s => Subtype.ext ?_
    rw [coe_spinPlusAction_apply, hx, hfplus s s.2]
  · refine LinearMap.ext fun s => Subtype.ext ?_
    rw [coe_spinMinusAction_apply, hx, hfminus s s.2]

/-- **The even structure theorem**: for an even-dimensional polarized quadratic space the even
Clifford subalgebra is the product of the endomorphism algebras of the two half-spin summands.

This is the even-subalgebra companion of `TauCeti.SpinPolarizationData.cliffordEquivEnd`, and it
is the reason the two half-spin summands are simple and inequivalent rather than merely
complementary. -/
noncomputable def SpinPolarizationData.evenCliffordEquivProdEnd (hline : P.line = ⊥) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K (spinPlus Q P) × Module.End K (spinMinus Q P) :=
  AlgEquiv.ofBijective (evenSpinAction Q P hline)
    ⟨evenSpinAction_injective P hline, evenSpinAction_surjective P hline⟩

@[simp]
theorem SpinPolarizationData.evenCliffordEquivProdEnd_apply (hline : P.line = ⊥)
    (x : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdEnd hline x = evenSpinAction Q P hline x := by
  rw [evenCliffordEquivProdEnd]
  exact congrFun (AlgEquiv.coe_ofBijective _ _) x

/-! ### Simplicity and inequivalence of the two half-spin summands -/

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- **The even half-spin summand is never zero**: it contains the scalar `1`, of exterior degree
zero. Unlike `TauCeti.nontrivial_spinMinus` this needs no hypothesis on the isotropic summand. -/
theorem nontrivial_spinPlus : Nontrivial (spinPlus Q P) :=
  ⟨⟨1, by rw [spinPlus_def]; exact SetLike.one_mem_graded _⟩, 0,
    fun h => one_ne_zero (congrArg Subtype.val h)⟩

omit [Invertible (2 : K)] in
/-- **The odd half-spin summand is nonzero** as soon as the isotropic summand is: it has dimension
`2 ^ (dim W - 1)`. For `W = ⊥` the spinor module is the ground field, entirely even, and this
fails. -/
theorem nontrivial_spinMinus (hW : P.W ≠ ⊥) : Nontrivial (spinMinus Q P) :=
  nontrivial_of_finrank_pos (R := K) (by rw [finrank_spinMinus P hW]; positivity)

/-- **The even half-spin summand is a simple module over the even Clifford subalgebra**: a subspace
of `S⁺` invariant under every even Clifford element is `⊥` or all of `S⁺`. The even subalgebra acts
through the full endomorphism algebra of `S⁺`, so a nonzero spinor of `S⁺` is carried to every
other one. -/
theorem eq_bot_or_eq_top_of_map_spinPlusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinPlus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinPlusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ := by
  have := nontrivial_spinPlus P
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective
    (Module.End K (spinPlus Q P)) hs0 t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  obtain ⟨x, hx⟩ := evenSpinAction_surjective P hline (g, 0)
  rw [evenSpinAction_apply, Prod.mk.injEq] at hx
  exact hg ▸ hx.1 ▸ hN x ⟨s, hs, rfl⟩

/-- **The odd half-spin summand is a simple module over the even Clifford subalgebra.** -/
theorem eq_bot_or_eq_top_of_map_spinMinusAction_le (hline : P.line = ⊥) (hW : P.W ≠ ⊥)
    (N : Submodule K (spinMinus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinMinusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ := by
  have := nontrivial_spinMinus P hW
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective
    (Module.End K (spinMinus Q P)) hs0 t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  obtain ⟨x, hx⟩ := evenSpinAction_surjective P hline (0, g)
  rw [evenSpinAction_apply, Prod.mk.injEq] at hx
  exact hg ▸ hx.2 ▸ hN x ⟨s, hs, rfl⟩

/-- **A map intertwining the two half-spin actions is zero.** The even subalgebra contains an
element acting as the identity on `S⁺` and as zero on `S⁻`, and an intertwiner turns the first
statement into the second. -/
theorem eq_zero_of_intertwines_spinPlusAction (hline : P.line = ⊥)
    (φ : spinPlus Q P →ₗ[K] spinMinus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
      φ (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinAction_surjective P hline (1, 0)
  rw [evenSpinAction_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **The two half-spin summands are inequivalent.** There is no isomorphism of modules over the
even Clifford subalgebra between `S⁺` and `S⁻`, even though in even dimension the two have the same
dimension `2 ^ (dim W - 1)`. -/
theorem not_exists_equiv_spinPlus_spinMinus (hline : P.line = ⊥) :
    ¬ ∃ e : spinPlus Q P ≃ₗ[K] spinMinus Q P,
      ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
        e (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (e s) := by
  rintro ⟨e, he⟩
  have hzero : (e : spinPlus Q P →ₗ[K] spinMinus Q P) = 0 :=
    eq_zero_of_intertwines_spinPlusAction P hline _ he
  have := nontrivial_spinPlus P
  obtain ⟨s, hs⟩ := exists_ne (0 : spinPlus Q P)
  exact hs (e.injective (by rw [show e s = (e : spinPlus Q P →ₗ[K] spinMinus Q P) s from rfl,
    hzero, LinearMap.zero_apply, map_zero]))

end Even

end TauCeti
