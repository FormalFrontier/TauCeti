/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Structure
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

What is not proved here is the odd-dimensional splitting of `CliffordAlgebra Q` into its two
central summands, for which the results here are the even-dimensional half.

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

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Lemma 20.9 and
  Proposition 20.15: the Clifford algebra of an even-dimensional space is the endomorphism algebra
  of `⋀·W`, its even subalgebra is the product of the endomorphism algebras of the two halves, and
  the two half-spin modules are irreducible and inequivalent.
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

private def spinGroupToEven {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} :
    spinGroup Q →* CliffordAlgebra.even Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_even hx

private def spinGroupRepresentation {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {M : Type*} [AddCommGroup M] [Module K M]
    (F : CliffordAlgebra.even Q →ₐ[K] Module.End K M) : Representation K (spinGroup Q) M :=
  F.toMonoidHom.comp spinGroupToEven

private noncomputable def spinGroupAlgebraHom {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} :
    MonoidAlgebra K (spinGroup Q) →ₐ[K] CliffordAlgebra.even Q :=
  MonoidAlgebra.lift K (CliffordAlgebra.even Q) (spinGroup Q) spinGroupToEven

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
      (Finsupp.linearCombination K spinGroupToEven).comp
        (MonoidAlgebra.coeffLinearEquiv K).toLinearMap by
    ext g
    simp [spinGroupAlgebraHom, spinGroupToEven]]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Finsupp.range_linearCombination]
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
    ⟨φ, fun g => LinearMap.ext fun m => hφ g m⟩
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
  have hPlus : ePlus ((spinGroupRepresentation (spinPlusAction Q P hline)) g s) =
      (spinPlusSubrep P hline).toRepresentation g (ePlus s) := by
    apply Subtype.ext
    exact coe_spinPlusAction_spinGroup_apply P hline g s
  have hMinus (t : spinMinus Q P) :
      eMinus ((spinGroupRepresentation (spinMinusAction Q P hline)) g t) =
        (spinMinusSubrep P hline).toRepresentation g (eMinus t) := by
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

end TauCeti
