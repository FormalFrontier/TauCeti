/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure
public import TauCeti.RepresentationTheory.Irreducible
-- Private: `IsSimpleModule.toSpanSingleton_surjective` is used only inside proofs.
import Mathlib.RingTheory.SimpleModule.Basic
-- Private: the span theorem is used only to pass from group invariance to even-Clifford invariance.
import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift

/-!
# Invariant subspaces and intertwiners for the spinor and half-spin actions

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

The proof of that structure theorem does not count dimensions a second time. Surjectivity onto the
*product* comes from the full structure theorem `TauCeti.spinAction_bijective` together with the
parity bookkeeping of `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`. This file records its
representation-theoretic consequences: each half-spin summand has no proper nonzero invariant
subspace because its factor is a full endomorphism algebra, and the two even-Clifford actions are
**inequivalent**
(`TauCeti.not_exists_equiv_intertwines_spinPlusAction_spinMinusAction`) because the
element of `even Q` acting as the identity on `S⁺` and as zero on `S⁻` kills any map that
intertwines them.

The invariant-subspace conclusions for the even Clifford algebra are stated in lattice form, as
"an invariant subspace is `⊥` or everything", rather than as `IsSimpleModule`: `S⁺` and `S⁻`
carry no `Module (even Q)` instance, and manufacturing one would mean a type synonym for a
statement that reads no better through it. Over a separably closed field, the Spin group linearly
spans the even Clifford algebra when the quadratic form is nondegenerate and the characteristic
is not two. The same dichotomies therefore prove that the even half-spin subrepresentation is
irreducible, that the odd half is irreducible when `P.W ≠ ⊥`, and that the two are inequivalent.

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

The odd-dimensional case is the opposite of all this, and the last section records it. There the
even subalgebra is a *single* block rather than a product, so the Fock action already carries it
onto all of `Module.End K S` (`TauCeti.evenSpinAction_surjective`), and the whole spinor module —
not a half of it — is the irreducible object: `TauCeti.spinRep_isIrreducible_of_odd`.
As soon as `P.W ≠ ⊥`, exterior parity still splits `S` as a vector space but no longer as a
representation, which `TauCeti.not_forall_map_spinRep_spinPlus_le` and
`TauCeti.not_forall_map_spinRep_spinMinus_le` record: neither half is `⊥` or everything, so
irreducibility alone forbids either from being invariant. The `P.line = ⊥` carried by every
statement of the even-dimensional half is precisely what fails. Dimension one is the exception:
there `W = ⊥` and `S = K` is entirely even, so `S⁺ = S` and `S⁻ = 0` are both invariant, for want
of anything to split.

The two parities are separated by exactly one hypothesis, the surjectivity of
`TauCeti.evenSpinAction`, and `TauCeti.isIrreducible_spinRep_of_span_of_surjective` is stated
against it rather than against a dimension, so the dichotomy is visible in the statement. It fails
in even dimension except for the zero-dimensional quadratic space, where `S = K` is
one-dimensional and there is no room for it to fail.

What is not proved here is the odd-dimensional splitting of `CliffordAlgebra Q` into its two
central summands, for which the results here are the even-dimensional half; it is
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one`.

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
* `TauCeti.isIrreducible_spinPlusSubrep_of_span` and
  `TauCeti.isIrreducible_spinMinusSubrep_of_span`: **the two half-spin group representations are
  irreducible** when the Spin group spans the even Clifford algebra, with `P.W ≠ ⊥` required for
  the odd half. The `_of_isSquare` and suffix-free versions give progressively stronger sufficient
  hypotheses.
* `TauCeti.isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_span`: **the two half-spin group
  representations are inequivalent** under the same spanning hypothesis, with analogous
  corollaries.
* `TauCeti.isIrreducible_spinRep_of_span_of_surjective`: the spin representation is irreducible
  once the Spin group spans the even subalgebra and that subalgebra exhausts the endomorphisms of
  the spinor module.
* `TauCeti.isIrreducible_spinRep_of_isSquare` and `TauCeti.spinRep_isIrreducible_of_odd`: **the
  spin representation is irreducible in odd dimension**, the type `Bₗ` half of Layer 4, under the
  square normalization and over a separably closed field respectively.
* `TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible` and
  `TauCeti.not_forall_map_spinRep_spinMinus_le_of_isIrreducible`: **an irreducible spinor module
  does not split along exterior parity**, provided `P.W ≠ ⊥`, which rules out only dimension one;
  `TauCeti.not_forall_map_spinRep_spinPlus_le` and
  `TauCeti.not_forall_map_spinRep_spinMinus_le` are their odd-dimensional specializations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the Clifford algebra of an even-dimensional space is the endomorphism algebra
  of `⋀·W`, its even subalgebra is the product of the endomorphism algebras of the two halves, and
  the two half-spin modules are irreducible and inequivalent; §20.2 for the odd-dimensional spin
  representation, which does not split.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §5: the complex spinor representations and their irreducibility in both parities.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layers 1 and 4, "the structure theorem" and "the spin and half-spin representations".
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

private def spinGroupRepresentation {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {M : Type*} [AddCommGroup M] [Module K M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M) : Representation K (spinGroup Q) M :=
  F.toMonoidHom.comp (spinGroupToEven Q)

private theorem spinGroupRepresentation_apply {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {M : Type*} [AddCommGroup M] [Module K M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M) (g : spinGroup Q) :
    spinGroupRepresentation F g = F (spinGroupToEven Q g) := rfl

/-- The same, with the even element spelled out in the coordinates the half-spin lemmas of
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean` are stated in. Only the coercion lemma
`TauCeti.coe_spinGroupToEven_apply` is used, not the definition of the inclusion. -/
private theorem spinGroupRepresentation_apply_mk {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {M : Type*} [AddCommGroup M] [Module K M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M) (g : spinGroup Q) :
    spinGroupRepresentation F g = F ⟨g, spinGroup.mem_even g.2⟩ := by
  rw [spinGroupRepresentation_apply]
  exact congrArg F (Subtype.ext (coe_spinGroupToEven_apply Q g))

private noncomputable def spinGroupAlgebraHom {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} :
    MonoidAlgebra K (spinGroup Q) →ₐ[K] CliffordAlgebra.even Q :=
  MonoidAlgebra.lift K (CliffordAlgebra.even Q) (spinGroup Q) (spinGroupToEven Q)

/-- The range of the Spin-group inclusion, with its values spelled out as the subtype elements
`⟨g, _⟩` that `Submodule.span_range_subtype_eq_top_iff` consumes. As for
`TauCeti.spinGroupRepresentation_apply_mk`, only the coercion lemma
`TauCeti.coe_spinGroupToEven_apply` is used, not the definition of the inclusion. -/
private theorem range_spinGroupToEven {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    Set.range ⇑(spinGroupToEven Q) =
      Set.range fun g : spinGroup Q ↦
        (⟨g, spinGroup.mem_even g.2⟩ : CliffordAlgebra.even Q) :=
  congrArg Set.range (funext fun g ↦ Subtype.ext (coe_spinGroupToEven_apply Q g))

private theorem spinGroupAlgebraHom_surjective {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V}
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule) :
    Function.Surjective (spinGroupAlgebraHom (K := K) (Q := Q)) := by
  -- Expose the algebra homomorphism's underlying linear map so its range can be calculated.
  change Function.Surjective (spinGroupAlgebraHom (K := K) (Q := Q)).toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [show (spinGroupAlgebraHom (K := K) (Q := Q)).toLinearMap =
      (Finsupp.linearCombination K (spinGroupToEven Q)).comp
        (MonoidAlgebra.coeffLinearEquiv K).toLinearMap by
    ext g
    simp [spinGroupAlgebraHom]]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Finsupp.range_linearCombination]
  rw [range_spinGroupToEven]
  apply (Submodule.span_range_subtype_eq_top_iff
    (CliffordAlgebra.even Q).toSubmodule
      (fun g : spinGroup Q ↦ spinGroup.mem_even g.2)).2
  -- Return to the ambient Clifford algebra, where `hspan` states the spanning result.
  change Submodule.span K
    (Set.range (Subtype.val : spinGroup Q → CliffordAlgebra Q)) = _
  rw [Subtype.range_val]
  exact hspan

private theorem asAlgebraHom_spinGroupRepresentation {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {M : Type*} [AddCommGroup M] [Module K M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M) :
    (spinGroupRepresentation F).asAlgebraHom =
      F.comp (spinGroupAlgebraHom (K := K) (Q := Q)) := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    simp [spinGroupRepresentation, spinGroupAlgebraHom]
  · ext

private theorem isIrreducible_spinGroupRepresentation {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V}
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    {M : Type*} [AddCommGroup M] [Module K M] [Nontrivial M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M)
    (hF : Function.Surjective F) : (spinGroupRepresentation F).IsIrreducible := by
  apply Representation.isIrreducible_of_asAlgebraHom_surjective
  rw [asAlgebraHom_spinGroupRepresentation]
  exact hF.comp (spinGroupAlgebraHom_surjective hspan)

private theorem intertwines_even_of_intertwines_spinGroup {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V}
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M)
    (G : CliffordAlgebra.even Q →ₐ[K] Module.End K N) (φ : M →ₗ[K] N)
    (hφ : ∀ (g : spinGroup Q) (m : M),
      φ (F ⟨g, spinGroup.mem_even g.2⟩ m) = G ⟨g, spinGroup.mem_even g.2⟩ (φ m))
    (x : CliffordAlgebra.even Q) (m : M) : φ (F x m) = G x (φ m) := by
  obtain ⟨a, rfl⟩ := spinGroupAlgebraHom_surjective hspan x
  let φ' : (spinGroupRepresentation F).IntertwiningMap (spinGroupRepresentation G) :=
    ⟨φ, fun g => LinearMap.ext fun m => by
      simpa only [LinearMap.comp_apply, spinGroupRepresentation_apply_mk] using hφ g m⟩
  have h := (Representation.IntertwiningMap.equivLinearMapAsModule
    (spinGroupRepresentation F) (spinGroupRepresentation G) φ').map_smul' a m
  -- The module equivalence is definitionally the identity on carriers. Expose the algebra
  -- actions so the two `asAlgebraHom_spinGroupRepresentation` rewrites can be applied.
  change φ ((spinGroupRepresentation F).asAlgebraHom a m) =
    (spinGroupRepresentation G).asAlgebraHom a (φ m) at h
  simpa only [asAlgebraHom_spinGroupRepresentation, AlgHom.comp_apply] using h

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

/-! ### Consequences of the even structure theorem -/

section Even

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)] [FiniteDimensional K V]


/-! ### Invariant-subspace dichotomies and inequivalence of the two half-spin actions -/

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

/-! ### Irreducibility of the half-spin group representations -/

section SpinGroup

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [Invertible (2 : K)] [FiniteDimensional K V] (P : SpinPolarizationData Q)

/-- **The even half-spin representation of the Spin group is irreducible** when the Spin group
linearly spans the even Clifford algebra. -/
theorem isIrreducible_spinPlusSubrep_of_span
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toRepresentation.IsIrreducible := by
  let _ : Nontrivial (spinPlus Q P) := nontrivial_spinPlus P
  have hρ : (spinGroupRepresentation (spinPlusAction Q P hline)).IsIrreducible :=
    isIrreducible_spinGroupRepresentation hspan (spinPlusAction Q P hline)
      (spinPlusAction_surjective P hline)
  let e : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  refine Representation.isIrreducible_of_linearEquiv e ?_ hρ
  intro g s
  rw [spinGroupRepresentation_apply_mk]
  apply Subtype.ext
  exact coe_spinPlusAction_spinGroup_apply P hline g s

/-- **The odd half-spin representation of the Spin group is irreducible** when the odd summand is
nonzero and the Spin group linearly spans the even Clifford algebra. -/
theorem isIrreducible_spinMinusSubrep_of_span
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) : (spinMinusSubrep P hline).toRepresentation.IsIrreducible := by
  let _ : Nontrivial (spinMinus Q P) := nontrivial_spinMinus P hW
  have hρ : (spinGroupRepresentation (spinMinusAction Q P hline)).IsIrreducible :=
    isIrreducible_spinGroupRepresentation hspan (spinMinusAction Q P hline)
      (spinMinusAction_surjective P hline)
  let e : spinMinus Q P ≃ₗ[K] (spinMinusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinMinusSubrep P hline).symm
  refine Representation.isIrreducible_of_linearEquiv e ?_ hρ
  intro g s
  rw [spinGroupRepresentation_apply_mk]
  apply Subtype.ext
  exact coe_spinMinusAction_spinGroup_apply P hline g s

/-- **The two half-spin representations of the Spin group are inequivalent** when the Spin group
linearly spans the even Clifford algebra. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_span
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hline : P.line = ⊥) :
    IsEmpty ((spinPlusSubrep P hline).toRepresentation.Equiv
      (spinMinusSubrep P hline).toRepresentation) := by
  refine ⟨fun e => ?_⟩
  let ePlus : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  let eMinus : spinMinus Q P ≃ₗ[K] (spinMinusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinMinusSubrep P hline).symm
  let f : spinPlus Q P ≃ₗ[K] spinMinus Q P :=
    ePlus.trans (e.toLinearEquiv.trans eMinus.symm)
  apply not_exists_equiv_intertwines_spinPlusAction_spinMinusAction P hline
  refine ⟨f, fun x s => intertwines_even_of_intertwines_spinGroup hspan
    (spinPlusAction Q P hline) (spinMinusAction Q P hline) f.toLinearMap ?_ x s⟩
  intro g s
  rw [← spinGroupRepresentation_apply_mk (spinPlusAction Q P hline) g,
    ← spinGroupRepresentation_apply_mk (spinMinusAction Q P hline) g]
  have hPlus : ePlus ((spinGroupRepresentation (spinPlusAction Q P hline)) g s) =
      (spinPlusSubrep P hline).toRepresentation g (ePlus s) := by
    rw [spinGroupRepresentation_apply_mk]
    apply Subtype.ext
    exact coe_spinPlusAction_spinGroup_apply P hline g s
  have hMinus (t : spinMinus Q P) :
      eMinus ((spinGroupRepresentation (spinMinusAction Q P hline)) g t) =
        (spinMinusSubrep P hline).toRepresentation g (eMinus t) := by
    rw [spinGroupRepresentation_apply_mk]
    apply Subtype.ext
    exact coe_spinMinusAction_spinGroup_apply P hline g t
  have hef (t : spinPlus Q P) : e.toIntertwiningMap (ePlus t) = eMinus (f t) := by
    rw [← e.toLinearEquiv_apply]
    simp only [f, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply eMinus.injective
  calc
    eMinus (f ((spinGroupRepresentation (spinPlusAction Q P hline)) g s)) =
        e.toIntertwiningMap
          (ePlus ((spinGroupRepresentation (spinPlusAction Q P hline)) g s)) :=
      (hef _).symm
    _ = e.toIntertwiningMap
        ((spinPlusSubrep P hline).toRepresentation g (ePlus s)) :=
      congrArg e.toIntertwiningMap hPlus
    _ = (spinMinusSubrep P hline).toRepresentation g
        (e.toIntertwiningMap (ePlus s)) :=
      Representation.IntertwiningMap.isIntertwining
        (spinPlusSubrep P hline).toRepresentation
        (spinMinusSubrep P hline).toRepresentation e.toIntertwiningMap g (ePlus s)
    _ = (spinMinusSubrep P hline).toRepresentation g (eMinus (f s)) :=
      congrArg ((spinMinusSubrep P hline).toRepresentation g) (hef s)
    _ = eMinus ((spinGroupRepresentation (spinMinusAction Q P hline)) g (f s)) :=
      (hMinus (f s)).symm

/-- **The even half-spin representation of the Spin group is irreducible** when anisotropic pairs
admit the square normalization needed to span the even Clifford algebra. -/
theorem isIrreducible_spinPlusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinPlusSubrep_of_span P
    (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
      (P.nondegenerate_of_line_eq_bot hline) hsq) hline

/-- **The odd half-spin representation of the Spin group is irreducible** when the odd summand is
nonzero and anisotropic pairs admit the required square normalization. -/
theorem isIrreducible_spinMinusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) : (spinMinusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinMinusSubrep_of_span P
    (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
      (P.nondegenerate_of_line_eq_bot hline) hsq) hline hW

/-- **The two half-spin representations of the Spin group are inequivalent** when anisotropic
pairs admit the square normalization needed to span the even Clifford algebra. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hline : P.line = ⊥) :
    IsEmpty ((spinPlusSubrep P hline).toRepresentation.Equiv
      (spinMinusSubrep P hline).toRepresentation) :=
  isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_span P
    (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
      (P.nondegenerate_of_line_eq_bot hline) hsq) hline

/-- **The even half-spin representation of the Spin group is irreducible** over a separably
closed field for polarization data without a line remainder. -/
theorem isIrreducible_spinPlusSubrep [IsSepClosed K] (hline : P.line = ⊥) :
    (spinPlusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinPlusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.exists_eq_mul_self ((Q v)⁻¹ * (Q w)⁻¹)) hline

/-- **The odd half-spin representation of the Spin group is irreducible** over a separably closed
field when the odd summand is nonzero. -/
theorem isIrreducible_spinMinusSubrep [IsSepClosed K] (hline : P.line = ⊥)
    (hW : P.W ≠ ⊥) : (spinMinusSubrep P hline).toRepresentation.IsIrreducible :=
  isIrreducible_spinMinusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.exists_eq_mul_self ((Q v)⁻¹ * (Q w)⁻¹)) hline hW

/-- **The two half-spin representations of the Spin group are inequivalent** over a separably
closed field. -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep [IsSepClosed K]
    (hline : P.line = ⊥) :
    IsEmpty ((spinPlusSubrep P hline).toRepresentation.Equiv
      (spinMinusSubrep P hline).toRepresentation) :=
  isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.exists_eq_mul_self ((Q v)⁻¹ * (Q w)⁻¹)) hline

end SpinGroup

/-! ### Irreducibility of the spin representation in odd dimension -/

section Odd

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q)

/-- **The whole spin representation is irreducible** as soon as the Spin group linearly spans the
even Clifford subalgebra and that subalgebra already exhausts the endomorphisms of the spinor
module.

The second hypothesis is exactly what separates the two parities of `finrank K V`. In *positive*
even dimension it fails — the even subalgebra is the *product* of the two half-spin endomorphism
algebras, by `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd`, and `S` visibly splits — and
in odd dimension it holds, by `TauCeti.evenSpinAction_surjective`. Dimension zero is the exception
on the even side: there `W = ⊥`, the odd block is zero, `S = K` is one-dimensional and the even
subalgebra is already all of `Module.End K S`. -/
theorem isIrreducible_spinRep_of_span_of_surjective
    (hspan : Submodule.span K (spinGroup Q : Set (CliffordAlgebra Q)) =
      (CliffordAlgebra.even Q).toSubmodule)
    (hsurj : Function.Surjective (evenSpinAction Q P)) : (spinRep Q P).IsIrreducible := by
  have hEq : spinGroupRepresentation (evenSpinAction Q P) = spinRep Q P :=
    DFunLike.ext _ _ fun g => by
      rw [spinGroupRepresentation_apply, evenSpinAction_apply, coe_spinGroupToEven_apply,
        spinRep_apply]
  exact hEq ▸ isIrreducible_spinGroupRepresentation hspan (evenSpinAction Q P) hsurj

/-- A subspace of the spinor module that is neither zero nor everything is not invariant under the
Spin group once the spin representation is irreducible, since invariance would make it a
subrepresentation. -/
private theorem not_forall_map_spinRep_le (hirr : (spinRep Q P).IsIrreducible)
    {N : Submodule K (ExteriorAlgebra K P.W)} (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    ¬ ∀ g : spinGroup Q, N.map (spinRep Q P g) ≤ N := by
  intro hinv
  have _ : (spinRep Q P).IsIrreducible := hirr
  let σ : Subrepresentation (spinRep Q P) :=
    { toSubmodule := N
      apply_mem_toSubmodule := fun g _ hv => hinv g ⟨_, hv, rfl⟩ }
  rcases IsSimpleOrder.eq_bot_or_eq_top σ with h | h
  · exact hbot (congrArg Subrepresentation.toSubmodule h)
  · exact htop (congrArg Subrepresentation.toSubmodule h)

/-- **An irreducible spinor module does not split along exterior parity.** The even part `S⁺` is
not invariant under the Spin group, so it is not a subrepresentation of `spinRep`.

Nothing about the anisotropic remainder is computed: the proof is by irreducibility, `S⁺` being
neither `⊥` (it contains the scalars) nor everything (it misses the nonzero `S⁻`). The hypothesis
`P.W ≠ ⊥` is what excludes `finrank K V = 1`, where `S = K` is entirely even, `S⁺ = S` is trivially
invariant and there is nothing to split. In even dimension the same subspace *is* invariant, by
`TauCeti.spinPlus_invariant`, and `spinRep` is correspondingly reducible. -/
theorem not_forall_map_spinRep_spinPlus_le_of_isIrreducible (hirr : (spinRep Q P).IsIrreducible)
    (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P :=
  not_forall_map_spinRep_le P hirr
    (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinPlus P))
    ((isCompl_spinPlus_spinMinus P).symm.disjoint.ne_top_of_ne_bot
      (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinMinus P hW)))

/-- **The odd half of an irreducible spinor module is not invariant either.** The companion of
`TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible` for the other parity: `S⁻` is nonzero
when `P.W ≠ ⊥` and is not everything, `S⁺` containing the scalars, so irreducibility forbids it
from being a subrepresentation of `spinRep`. -/
theorem not_forall_map_spinRep_spinMinus_le_of_isIrreducible (hirr : (spinRep Q P).IsIrreducible)
    (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinMinus Q P).map (spinRep Q P g) ≤ spinMinus Q P :=
  not_forall_map_spinRep_le P hirr
    (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinMinus P hW))
    ((isCompl_spinPlus_spinMinus P).disjoint.ne_top_of_ne_bot
      (Submodule.nontrivial_iff_ne_bot.1 (nontrivial_spinPlus P)))

variable [NeZero (2 : K)] [FiniteDimensional K V]

/-- **The spin representation is irreducible in odd dimension** when anisotropic pairs admit the
square normalization needed to span the even Clifford algebra.

This is the generality of the even-dimensional `TauCeti.isIrreducible_spinPlusSubrep_of_isSquare`:
no separably closed field, and no nondegeneracy hypothesis, the polarization data already carrying
it by `TauCeti.SpinPolarizationData.nondegenerate`. The square normalization is only what lifts a
product of two reflections to the Spin group, and it is the sole remaining hypothesis of this
argument. -/
theorem isIrreducible_spinRep_of_isSquare
    (hsq : ∀ v w, Q v ≠ 0 → Q w ≠ 0 → IsSquare ((Q v)⁻¹ * (Q w)⁻¹))
    (hodd : Odd (finrank K V)) : (spinRep Q P).IsIrreducible := by
  have _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  exact isIrreducible_spinRep_of_span_of_surjective P
    (CliffordAlgebra.span_spinGroup_eq_even_of_isSquare Q
      (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)) hsq)
    (evenSpinAction_surjective P hodd)

variable [IsSepClosed K]

/-- **The spin representation is irreducible in odd dimension.** For a polarized quadratic space of
dimension `2 * l + 1` over a separably closed field of characteristic not two, the Spin group acts
irreducibly on the whole spinor module `S = ⋀·W`.

This is the type `Bₗ` half of the Layer-4 irreducibility statement, in the shape the roadmap pins.
Nondegeneracy of `Q` is not assumed: the polarization data already carries it, by
`TauCeti.SpinPolarizationData.nondegenerate`. Except in dimension one, where `W = ⊥` and `S = K` is
entirely even, the exterior parity splitting `S = S⁺ ⊕ S⁻` is *not* a splitting of representations
here: see `TauCeti.not_forall_map_spinRep_spinPlus_le`. The even-dimensional counterpart is the
pair `TauCeti.isIrreducible_spinPlusSubrep`, `TauCeti.isIrreducible_spinMinusSubrep`, where `S`
itself is reducible unless it is the zero-dimensional quadratic space. -/
theorem spinRep_isIrreducible_of_odd (l : ℕ) (hV : finrank K V = 2 * l + 1) :
    (spinRep Q P).IsIrreducible :=
  isIrreducible_spinRep_of_isSquare P
    (fun v w _ _ ↦ IsSepClosed.exists_eq_mul_self ((Q v)⁻¹ * (Q w)⁻¹)) ⟨l, hV⟩

/-- **In odd dimension the spinor module does not split along exterior parity.** The
separably closed specialization of
`TauCeti.not_forall_map_spinRep_spinPlus_le_of_isIrreducible`, where
`TauCeti.spinRep_isIrreducible_of_odd` supplies the irreducibility. Unlike in positive even
dimension, `S⁺` is not a subrepresentation of `spinRep`; the hypothesis `P.line = ⊥` carried by
`TauCeti.spinPlus_invariant` is what an odd-dimensional polarization cannot satisfy. -/
theorem not_forall_map_spinRep_spinPlus_le (l : ℕ) (hV : finrank K V = 2 * l + 1) (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P :=
  not_forall_map_spinRep_spinPlus_le_of_isIrreducible P (spinRep_isIrreducible_of_odd P l hV) hW

/-- **In odd dimension the odd half of the spinor module is not invariant either.** The companion
of `TauCeti.not_forall_map_spinRep_spinPlus_le` for the other parity, the separably closed
specialization of `TauCeti.not_forall_map_spinRep_spinMinus_le_of_isIrreducible`. -/
theorem not_forall_map_spinRep_spinMinus_le (l : ℕ) (hV : finrank K V = 2 * l + 1) (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinMinus Q P).map (spinRep Q P g) ≤ spinMinus Q P :=
  not_forall_map_spinRep_spinMinus_le_of_isIrreducible P (spinRep_isIrreducible_of_odd P l hV) hW

end Odd

end TauCeti
