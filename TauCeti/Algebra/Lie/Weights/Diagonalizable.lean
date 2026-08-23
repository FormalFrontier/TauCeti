/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import TauCeti.Algebra.Lie.Sl2.Spectrum
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple

public section

/-!
# The Cartan subalgebra acts diagonalizably, and weight spaces are honest

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra, and let `M` be a
finite-dimensional `L`-module. This file proves that **every `x : H` acts on `M` by a semisimple
endomorphism**, so that Mathlib's *generalized* weight spaces `LieModule.genWeightSpace M χ` are
the *honest* simultaneous eigenspaces `LieModule.weightSpace M χ`, and `M` is their internal direct
sum.

The route is the rank-one reduction, not the abstract Jordan decomposition. A nonzero root `α`
carries an `sl₂` triple whose Cartan element is the coroot `α^∨`, and the `sl₂` engine already
knows that such an element acts diagonalizably
(`TauCeti.iSup_eigenspace_toEnd_eq_top`); over an algebraically closed field diagonalizable means
semisimple (`TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`). The coroots span `H`, and `H` is
abelian, so the operators they give are commuting semisimple endomorphisms, and semisimplicity
passes to their span (`Module.End.IsSemisimple.add_of_commute`,
`Module.End.IsSemisimple.of_mem_adjoin_singleton`).

In particular the proof uses only complete reducibility **for `sl₂`**, which is where
`TauCeti.iSup_eigenspace_toEnd_eq_top` comes from, and not Weyl's complete reducibility for `L`.
That is what keeps the highest-weight theory free of circularity: the honest weight-space
decomposition is available before Weyl's theorem, whose usual proof consumes it.

That every finite-dimensional module is triangularizable over `H` needs no work here: it is
Mathlib's `LieModule.instIsTriangularizableOfIsAlgClosed`, which is what makes the generalized
weight spaces exhaust `M` in the first place. The content below is the refinement from generalized
to honest.

## Main results

* `TauCeti.nonempty_weight`: a nonzero finite-dimensional triangularizable module has a weight.
* `TauCeti.isInternal_genWeightSpace`: a finite-dimensional triangularizable module is the internal
  direct sum of its *generalized* weight spaces. This needs no diagonalizability and is the form
  the dimension counts consume; the honest-weight-space refinement is below.
* `TauCeti.isSemisimple_toEnd_coroot`: a coroot acts semisimply on a finite-dimensional module.
* `TauCeti.isSemisimple_toEnd_cartan`: **every element of the Cartan subalgebra acts semisimply.**
* `TauCeti.genWeightSpace_eq_weightSpace`: **the generalized weight spaces are honest weight
  spaces**, with `TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul` the pointwise form: membership
  is the eigenvector equation `⁅x, m⁆ = χ x • m` for every `x : H`.
* `TauCeti.iSup_weightSpace_eq_top` and `TauCeti.isInternal_weightSpace`: the honest weight spaces
  span `M`, and `M` is their internal direct sum, so `χ ↦ finrank (weightSpace M χ)` counts honest
  multiplicities.

## References

This is the "honest weight spaces (the diagonalizability theorem)" item of Layer 2 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose target signature
`isSemisimple_toEnd_cartan` is `TauCeti.isSemisimple_toEnd_cartan`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.4 and §20.1.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

/-! ### Existence of a weight -/

section Triangularizable

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]

/-- A nonzero finite-dimensional triangularizable module has at least one weight: the *generalized*
weight spaces span it (`LieModule.iSup_genWeightSpace_eq_top'`), and an empty supremum is `⊥`.
`LieModule.Weight` is by definition indexed by the linear forms whose generalized weight space is
nonzero, so no honest-weight-space hypothesis is available or needed here; nilpotency of `L` is
carried only because `LieModule.Weight` demands it.

Mathlib performs this step inside the proof of
`LieModule.exists_nontrivial_weightSpace_of_isNilpotent` rather than naming it. -/
theorem nonempty_weight [IsTriangularizable K L M] [Nontrivial M] : Nonempty (Weight K L M) := by
  by_contra! contra
  simpa only [iSup_of_empty, bot_ne_top] using iSup_genWeightSpace_eq_top' K L M

/-! ### The generalized weight-space decomposition -/

/-- **The generalized weight-space decomposition.** A finite-dimensional triangularizable module is
the internal direct sum of its generalized weight spaces, indexed by all of its weights. This is
Mathlib's `LieModule.iSupIndep_genWeightSpace'` and `LieModule.iSup_genWeightSpace_eq_top'`
packaged as a `DirectSum.IsInternal`, which is the form the dimension counts consume. -/
theorem isInternal_genWeightSpace [IsTriangularizable K L M] [DecidableEq (Weight K L M)] :
    DirectSum.IsInternal fun χ : Weight K L M ↦ (genWeightSpace M (χ : L → K)).toSubmodule := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [LieSubmodule.iSupIndep_toSubmodule]
    exact iSupIndep_genWeightSpace' K L M
  · rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top' K L M]
    simp

end Triangularizable

/-! ### Semisimplicity of the Cartan action -/

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- **A coroot acts semisimply.** The coroot `α^∨` of a weight `α` of `L` acts on a
finite-dimensional module by a semisimple endomorphism.

For a nonzero `α` this is the `sl₂` engine: `α^∨` is the Cartan element of an `sl₂` triple, whose
eigenspaces span (`TauCeti.iSup_eigenspace_toEnd_eq_top`), and a diagonalizable endomorphism is
semisimple. The coroot of a zero weight is zero. -/
theorem isSemisimple_toEnd_coroot (α : Weight K H L) :
    (toEnd K H M (IsKilling.coroot α)).IsSemisimple := by
  by_cases hα : α.IsNonZero
  · obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
    refine isSemisimple_of_iSup_eigenspace_eq_top ?_
    have hsup := iSup_eigenspace_toEnd_eq_top (K := K) (M := M) ht
    rw [ht.h_eq_coroot hα he hf] at hsup
    exact hsup
  · rw [IsKilling.coroot_eq_zero_iff.2 (not_not.1 hα)]
    simp

/-- **The Cartan subalgebra acts semisimply.** Every element of a Cartan subalgebra of a
Killing-semisimple Lie algebra acts on a finite-dimensional module by a semisimple endomorphism.

The coroots span the Cartan subalgebra (`RootPairing.IsRootSystem.span_coroot_eq_top` for
`LieAlgebra.IsKilling.rootSystem H`) and act semisimply by
`TauCeti.isSemisimple_toEnd_coroot`; the Cartan subalgebra is abelian, so the endomorphisms they
give commute, and both a sum of commuting semisimple endomorphisms and a scalar multiple of one are
again semisimple. -/
theorem isSemisimple_toEnd_cartan (x : H) : (toEnd K H M x).IsSemisimple := by
  have hcomm : ∀ y z : H, Commute (toEnd K H M y) (toEnd K H M z) := fun y z ↦
    LieModule.commute_toEnd_of_mem_center_left M
      (by rw [(LieAlgebra.isLieAbelian_iff_center_eq_top K H).1 inferInstance]; trivial) z
  have hx : x ∈ Submodule.span K (Set.range (IsKilling.rootSystem H).coroot) := by
    rw [RootPairing.IsRootSystem.span_coroot_eq_top]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, rfl⟩ := hy
    exact isSemisimple_toEnd_coroot α.1
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Module.End.IsSemisimple.add_of_commute (hcomm y z) hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact hy.of_mem_adjoin_singleton
      (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton _ _) c)

/-! ### Honest weight spaces -/

/-- The generalized eigenspace of `x : H` at a scalar is an honest eigenspace. -/
@[simp]
theorem genWeightSpaceOf_eq_eigenspace (μ : K) (x : H) :
    (genWeightSpaceOf M μ x).toSubmodule = (toEnd K H M x).eigenspace μ :=
  (isSemisimple_toEnd_cartan (M := M) x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

/-- **The generalized weight spaces are honest weight spaces.** For a finite-dimensional module over
a Killing-semisimple Lie algebra, `LieModule.genWeightSpace M χ` is the simultaneous eigenspace
`LieModule.weightSpace M χ`.

Mathlib's `LieModule.weightSpace_le_genWeightSpace` is the inclusion that holds always; this is the
reverse one, and it is exactly the diagonalizability of the Cartan action. -/
@[simp]
theorem genWeightSpace_eq_weightSpace (χ : H → K) : genWeightSpace M χ = weightSpace M χ := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [genWeightSpace, LieSubmodule.iInf_toSubmodule]
  simp only [genWeightSpaceOf_eq_eigenspace]
  rfl

/-- **Membership of a weight space is the eigenvector equation.** An element of a
finite-dimensional module lies in the `χ`-weight space exactly when every `x : H` acts on it by the
scalar `χ x`.

This is deliberately not a `simp` lemma: `TauCeti.genWeightSpace_eq_weightSpace` already rewrites
the left-hand side to `m ∈ LieModule.weightSpace M χ`, so tagging it would leave it in
non-simp-normal form. -/
theorem mem_genWeightSpace_iff_forall_lie_eq_smul {χ : H → K} {m : M} :
    m ∈ genWeightSpace M χ ↔ ∀ x : H, ⁅(x : L), m⁆ = χ x • m := by
  rw [genWeightSpace_eq_weightSpace, mem_weightSpace]
  simp

variable (K H M) in
/-- **The honest weight spaces span.** A finite-dimensional module over a Killing-semisimple Lie
algebra is spanned by the simultaneous eigenspaces of its Cartan subalgebra. -/
theorem iSup_weightSpace_eq_top : ⨆ χ : Weight K H M, weightSpace M (χ : H → K) = ⊤ := by
  simpa only [genWeightSpace_eq_weightSpace] using iSup_genWeightSpace_eq_top' K H M

variable (K H M) in
open scoped Classical in
/-- **The honest weight-space decomposition.** A finite-dimensional module over a
Killing-semisimple Lie algebra is the internal direct sum of the simultaneous eigenspaces of its
Cartan subalgebra, so `χ ↦ finrank (weightSpace M χ)` counts honest multiplicities. -/
theorem isInternal_weightSpace :
    DirectSum.IsInternal fun χ : Weight K H M ↦ (weightSpace M (χ : H → K)).toSubmodule := by
  simpa only [genWeightSpace_eq_weightSpace] using isInternal_genWeightSpace K H M

end TauCeti
