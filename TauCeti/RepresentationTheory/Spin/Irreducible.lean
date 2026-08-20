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
`TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`, and everything else follows from it: each
half-spin summand has no proper nonzero invariant subspace because its factor is a full
endomorphism algebra, and they are **inequivalent**
(`TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`) because the
element of `even Q` acting as the identity on `S⁺` and as zero on `S⁻` kills any map that
intertwines them.

The invariant-subspace conclusions are stated in lattice form, as "an invariant subspace is `⊥`
or everything", rather than as `IsSimpleModule`: `S⁺` and `S⁻` carry no `Module (even Q)` instance,
and manufacturing one would mean a type synonym for a statement that reads no better through it.

The actions themselves — `TauCeti.spinPlusAction`, `TauCeti.spinMinusAction` and their pair
`TauCeti.evenSpinActionProd` — are defined in
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean`, beside the bundling of the same two summands as
subrepresentations of `spinRep` that the same invariance gives; this file only proves theorems
about them.

The hypothesis `P.line = ⊥` is the even-dimensional case, and it is exactly what makes the parity
splitting a splitting of modules at all;
`TauCeti.SpinPolarizationData.even_finrank_of_line_eq_bot` turns it into the evenness the structure
theorem is stated with, so no separate parity hypothesis is carried. The lattice dichotomy for
`S⁻` needs no further hypothesis, since it also holds vacuously when `S⁻ = 0`. To conclude that
`S⁻` is simple, combine it with `TauCeti.nontrivial_spinMinus`, whose hypothesis `W ≠ ⊥` rules out
only the zero-dimensional quadratic space: there `S = K` is entirely even and `S⁻` is zero. `S⁺`
always contains the scalars, so it needs no such hypothesis, and neither does the inequivalence.

What is *not* proved here is irreducibility of the group representation `TauCeti.spinRep`, which
asks more: that the `K`-span of `spinGroup Q` inside `even Q` is all of it. Nor is the
odd-dimensional splitting of `CliffordAlgebra Q` into its two central summands, for which the
results here are the even-dimensional half.

## Main definitions

* `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`: **the even structure theorem**, that
  `even Q` is the product of the endomorphism algebras of the two half-spin summands.
* `TauCeti.SpinPolarizationData.evenCliffordEquivProdMatrix`: its matrix-algebra form.

## Main results

* `TauCeti.exists_spinAction_eq` and `TauCeti.eq_bot_or_eq_top_of_map_spinAction_le`: **the spinor
  module is a simple Clifford module.**
* `TauCeti.mem_even_of_map_spinPlus_le_of_map_spinMinus_le`: a Clifford element whose action
  preserves both half-spin summands is even.
* `TauCeti.eq_bot_or_eq_top_of_map_spinPlusAction_le` and
  `TauCeti.eq_bot_or_eq_top_of_map_spinMinusAction_le`: the two half-spin summands have no proper
  nonzero invariant subspace. Together with `TauCeti.nontrivial_spinPlus` and
  `TauCeti.nontrivial_spinMinus`, respectively, these say that the summands are simple.
* `TauCeti.eq_zero_of_intertwines_spinPlusAction_spinMinusAction` and
  `TauCeti.eq_zero_of_intertwines_spinMinusAction_spinPlusAction`: there is no nonzero map either
  way intertwining the two actions, and hence
  `TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`: **the half-spin summands
  are inequivalent.**

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

private theorem eq_bot_or_eq_top_of_surjective_action {K : Type u} [Field K]
    {A M : Type*} [AddCommGroup M] [Module K M] (F : A → Module.End K M)
    (hF : Function.Surjective F) (N : Submodule K M)
    (hN : ∀ a : A, N.map (F a) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨s, hs, hs0⟩ := N.exists_mem_ne_zero_of_ne_bot hbot
  let _ : Nontrivial M := ⟨s, 0, hs0⟩
  obtain ⟨g, hg⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End K M) hs0 t
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hg
  obtain ⟨a, rfl⟩ := hF g
  exact hg ▸ hN a ⟨s, hs, rfl⟩

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

/-- **The invariant-subspace dichotomy for the spinor module**: a submodule of `S = ⋀·W`
invariant under every Clifford element is `⊥` or the whole of `S`. The spinor module is nonzero,
so this is its simplicity statement for the Clifford action. -/
theorem eq_bot_or_eq_top_of_map_spinAction_le (N : Submodule K (ExteriorAlgebra K P.W))
    (hN : ∀ x : CliffordAlgebra Q, N.map (spinAction Q P x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  exact eq_bot_or_eq_top_of_surjective_action (spinAction Q P) (spinAction_surjective P) N hN

end Simple

/-! ### The even structure theorem

For an even-dimensional polarized quadratic space the Fock action is an isomorphism
`CliffordAlgebra Q ≃ₐ[K] Module.End K S`. Under it the even subalgebra is carried onto the
endomorphisms preserving the parity splitting `S = S⁺ ⊕ S⁻`, which is the product of the two
endomorphism algebras; that is the content of this section. -/

section Even

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
private theorem spinAction_eq_zero_on_of_maps_le
    (M N : Submodule K (ExteriorAlgebra K P.W)) (hMN : Disjoint M N)
    {x₀ x₁ : CliffordAlgebra Q} (heven : M.map (spinAction Q P x₀) ≤ M)
    (hodd : M.map (spinAction Q P x₁) ≤ N)
    (hmap : M.map (spinAction Q P (x₀ + x₁)) ≤ M) :
    Set.EqOn (spinAction Q P x₁) 0 M := by
  intro s hs
  have hN : spinAction Q P x₁ s ∈ N := hodd ⟨s, hs, rfl⟩
  have hM : spinAction Q P x₁ s ∈ M := by
    rw [map_add] at hmap
    have hadd := hmap ⟨s, hs, rfl⟩
    rw [LinearMap.add_apply] at hadd
    simpa only [add_sub_cancel_left] using M.sub_mem hadd (heven ⟨s, hs, rfl⟩)
  have : spinAction Q P x₁ s ∈ (⊥ : Submodule K (ExteriorAlgebra K P.W)) := by
    rw [← disjoint_iff.1 hMN]
    exact ⟨hM, hN⟩
  simpa using this

/-- **A Clifford element whose action preserves both half-spin summands is even.** Splitting it
into an even and an odd part, the odd part acts by an operator that both preserves and reverses
exterior parity, so it acts by zero; in even dimension the Fock action is faithful, so the odd part
itself vanishes. -/
theorem mem_even_of_map_spinPlus_le_of_map_spinMinus_le (hline : P.line = ⊥)
    {x : CliffordAlgebra Q}
    (hplus : (spinPlus Q P).map (spinAction Q P x) ≤ spinPlus Q P)
    (hminus : (spinMinus Q P).map (spinAction Q P x) ≤ spinMinus Q P) :
    x ∈ CliffordAlgebra.even Q := by
  have hxsplit : x ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [codisjoint_iff.1 (CliffordAlgebra.evenOdd_isCompl (Q := Q)).codisjoint]
    trivial
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1 hxsplit
  have hx₀even : x₀ ∈ CliffordAlgebra.even Q := by
    rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
    exact hx₀
  -- The odd part acts by zero on each summand, so by zero.
  have hzeroplus : Set.EqOn (spinAction Q P x₁) 0 (spinPlus Q P) :=
    spinAction_eq_zero_on_of_maps_le P (spinPlus Q P) (spinMinus Q P)
      (isCompl_spinPlus_spinMinus P).disjoint
      (by rintro _ ⟨s, hs, rfl⟩; rw [spinPlus_def] at hs ⊢
          exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs)
      (map_spinAction_spinPlus_le_spinMinus P hline hx₁) hplus
  have hzerominus : Set.EqOn (spinAction Q P x₁) 0 (spinMinus Q P) :=
    spinAction_eq_zero_on_of_maps_le P (spinMinus Q P) (spinPlus Q P)
      (isCompl_spinPlus_spinMinus P).symm.disjoint
      (by rintro _ ⟨s, hs, rfl⟩; rw [spinMinus_def] at hs ⊢
          exact spinAction_mem_evenOdd_of_mem_even P hline hx₀even hs)
      (map_spinAction_spinMinus_le_spinPlus P hline hx₁) hminus
  have hzero : spinAction Q P x₁ = 0 :=
    LinearMap.ext_on_codisjoint (isCompl_spinPlus_spinMinus P).codisjoint
      hzeroplus hzerominus
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
theorem evenSpinActionProd_injective (hline : P.line = ⊥) :
    Function.Injective (evenSpinActionProd Q P hline) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  rw [evenSpinActionProd_apply, Prod.mk_eq_zero] at hx
  have hzeroplus : Set.EqOn (spinAction Q P x) 0 (spinPlus Q P) := by
    intro s hs
    have := congrArg
      (fun g : Module.End K (spinPlus Q P) => (g ⟨s, hs⟩ : ExteriorAlgebra K P.W)) hx.1
    simpa using this
  have hzerominus : Set.EqOn (spinAction Q P x) 0 (spinMinus Q P) := by
    intro s hs
    have := congrArg
      (fun g : Module.End K (spinMinus Q P) => (g ⟨s, hs⟩ : ExteriorAlgebra K P.W)) hx.2
    simpa using this
  have hzero : spinAction Q P x = 0 :=
    LinearMap.ext_on_codisjoint (isCompl_spinPlus_spinMinus P).codisjoint
      hzeroplus hzerominus
  exact Subtype.ext
    (spinAction_injective P (P.even_finrank_of_line_eq_bot hline) (by simp [hzero]))

/-- **The even subalgebra exhausts the pair of endomorphism algebras.** A pair of endomorphisms of
the two summands assembles, along the splitting `S = S⁺ ⊕ S⁻`, into a parity-preserving
endomorphism of `S`, and those are exactly the actions of even Clifford elements. -/
theorem evenSpinActionProd_surjective (hline : P.line = ⊥) :
    Function.Surjective (evenSpinActionProd Q P hline) := by
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
  rw [evenSpinActionProd_apply, Prod.mk.injEq]
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
  AlgEquiv.ofBijective (evenSpinActionProd Q P hline)
    ⟨evenSpinActionProd_injective P hline, evenSpinActionProd_surjective P hline⟩

@[simp]
theorem SpinPolarizationData.evenCliffordEquivProdEnd_apply (hline : P.line = ⊥)
    (x : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdEnd hline x = evenSpinActionProd Q P hline x := by
  rw [evenCliffordEquivProdEnd]
  exact congrFun (AlgEquiv.coe_ofBijective _ _) x

/-- **The matrix form of the even structure theorem**: in dimension `2 * l`, the even Clifford
subalgebra is a product of two matrix algebras of size `2 ^ (l - 1)`. -/
noncomputable def SpinPolarizationData.evenCliffordEquivProdMatrix {l : ℕ}
    (hW : P.W ≠ ⊥) (hV : finrank K V = 2 * l) :
    CliffordAlgebra.even Q ≃ₐ[K]
      Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) K ×
        Matrix (Fin (2 ^ (l - 1))) (Fin (2 ^ (l - 1))) K := by
  have hline := P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)
  have hWfin := P.finrank_W_of_finrank_eq_two_mul hV
  have hplus : finrank K (spinPlus Q P) = 2 ^ (l - 1) := by
    rw [finrank_spinPlus P hW, hWfin]
  have hminus : finrank K (spinMinus Q P) = 2 ^ (l - 1) := by
    rw [finrank_spinMinus P hW, hWfin]
  exact (P.evenCliffordEquivProdEnd hline).trans
    ((Algebra.endAlgEquivMatrix K _ hplus).prodCongr
      (Algebra.endAlgEquivMatrix K _ hminus))

/-- The matrix form of the even structure theorem is the pair of half-spin actions, followed by
the chosen-basis identifications of their endomorphism algebras with matrix algebras. -/
@[simp]
theorem SpinPolarizationData.evenCliffordEquivProdMatrix_apply {l : ℕ}
    (hW : P.W ≠ ⊥) (hV : finrank K V = 2 * l) (x : CliffordAlgebra.even Q) :
    P.evenCliffordEquivProdMatrix hW hV x =
      (Algebra.endAlgEquivMatrix K (spinPlus Q P)
          (by rw [finrank_spinPlus P hW, P.finrank_W_of_finrank_eq_two_mul hV])
          (spinPlusAction Q P (P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)) x),
        Algebra.endAlgEquivMatrix K (spinMinus Q P)
          (by rw [finrank_spinMinus P hW, P.finrank_W_of_finrank_eq_two_mul hV])
          (spinMinusAction Q P (P.line_eq_bot_of_even_finrank (hV ▸ even_two_mul l)) x)) := by
  rw [evenCliffordEquivProdMatrix, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply,
    Equiv.prodCongr_apply, Prod.map_apply, evenCliffordEquivProdEnd_apply,
    evenSpinActionProd_apply]
  rfl

/-! ### Simplicity and inequivalence of the two half-spin summands -/

/-- The even Clifford action on `S⁺` is onto its full endomorphism algebra. -/
theorem spinPlusAction_surjective (hline : P.line = ⊥) :
    Function.Surjective (spinPlusAction Q P hline) := fun g => by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (g, 0)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  exact ⟨x, hx.1⟩

/-- The even Clifford action on `S⁻` is onto its full endomorphism algebra. -/
theorem spinMinusAction_surjective (hline : P.line = ⊥) :
    Function.Surjective (spinMinusAction Q P hline) := fun g => by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (0, g)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  exact ⟨x, hx.2⟩

/-- **The invariant-subspace dichotomy for the even half-spin summand**: every subspace of `S⁺`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁺`. Combine this with
`TauCeti.nontrivial_spinPlus` to obtain simplicity. -/
theorem eq_bot_or_eq_top_of_map_spinPlusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinPlus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinPlusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinPlusAction Q P hline)
    (spinPlusAction_surjective P hline) N hN

/-- **The invariant-subspace dichotomy for the odd half-spin summand**: every subspace of `S⁻`
invariant under the even Clifford subalgebra is `⊥` or all of `S⁻`. This remains true when `S⁻` is
zero; combine it with `TauCeti.nontrivial_spinMinus` to obtain simplicity when `P.W ≠ ⊥`. -/
theorem eq_bot_or_eq_top_of_map_spinMinusAction_le (hline : P.line = ⊥)
    (N : Submodule K (spinMinus Q P))
    (hN : ∀ x : CliffordAlgebra.even Q, N.map (spinMinusAction Q P hline x) ≤ N) :
    N = ⊥ ∨ N = ⊤ :=
  eq_bot_or_eq_top_of_surjective_action (spinMinusAction Q P hline)
    (spinMinusAction_surjective P hline) N hN

/-- **A map intertwining the two half-spin actions is zero.** The even subalgebra contains an
element acting as the identity on `S⁺` and as zero on `S⁻`, and an intertwiner turns the first
statement into the second. -/
theorem eq_zero_of_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥)
    (φ : spinPlus Q P →ₗ[K] spinMinus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
      φ (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (1, 0)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **A map intertwining the odd and even half-spin actions is zero.** -/
theorem eq_zero_of_intertwines_spinMinusAction_spinPlusAction (hline : P.line = ⊥)
    (φ : spinMinus Q P →ₗ[K] spinPlus Q P)
    (hφ : ∀ (x : CliffordAlgebra.even Q) (s : spinMinus Q P),
      φ (spinMinusAction Q P hline x s) = spinPlusAction Q P hline x (φ s)) :
    φ = 0 := by
  obtain ⟨x, hx⟩ := evenSpinActionProd_surjective P hline (0, 1)
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hx
  refine LinearMap.ext fun s => ?_
  have h := hφ x s
  rw [hx.1, hx.2] at h
  simpa using h

/-- **The two half-spin summands are inequivalent.** There is no linear equivalence intertwining
the two actions of the even Clifford subalgebra. -/
theorem not_exists_equiv_intertwines_spinPlusAction_spinMinusAction (hline : P.line = ⊥) :
    ¬ ∃ e : spinPlus Q P ≃ₗ[K] spinMinus Q P,
      ∀ (x : CliffordAlgebra.even Q) (s : spinPlus Q P),
        e (spinPlusAction Q P hline x s) = spinMinusAction Q P hline x (e s) := by
  rintro ⟨e, he⟩
  have hzero : (e : spinPlus Q P →ₗ[K] spinMinus Q P) = 0 :=
    eq_zero_of_intertwines_spinPlusAction_spinMinusAction P hline _ he
  have := nontrivial_spinPlus P
  obtain ⟨s, hs⟩ := exists_ne (0 : spinPlus Q P)
  have hes : e s = 0 := by simpa using LinearMap.congr_fun hzero s
  exact hs (e.injective (hes.trans (map_zero e).symm))

end Even

end TauCeti
