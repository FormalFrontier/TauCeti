/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Cartan

public section

/-!
# Spans of generalized weight spaces

A nilpotent Lie algebra `H` acting on a module `M` cuts `M` into the generalized weight spaces
`LieModule.genWeightSpace M χ`, indexed by the scalar-valued functions `χ` on `H`. This file
records the `H`-submodule spanned by the weight spaces indexed by a set `S` of such functions,
together with its universal property, and the one fact about the bracket that a span of weight
spaces obeys: a root vector shifts it by the corresponding root.

## Main definitions

* `TauCeti.genWeightSpaceSpan H M S`: the `H`-submodule of `M` spanned by the weight spaces indexed
  by a set `S` of scalar-valued functions on `H`.

## Main results

* `TauCeti.genWeightSpace_le_genWeightSpaceSpan` and `TauCeti.genWeightSpaceSpan_le_iff` are the
  universal property of the span: it is contained in a given submodule exactly when each of the
  weight spaces it is spanned by is. `TauCeti.genWeightSpaceSpan_mono` is the resulting monotonicity
  in the indexing set.
* `TauCeti.genWeightSpaceSpan_eq_iSup` exhibits the span as a supremum, so that a member can be
  taken apart by `LieSubmodule.iSup_induction` without unfolding the definition.
* `TauCeti.lie_mem_genWeightSpaceSpan`: for a nilpotent subalgebra `H` of a Lie algebra `L` acting
  on `M`, a vector in the root space of `α` carries the span of a set `S` of weight spaces into the
  span of any set containing `α + S`.

## Implementation notes

The span is valued in `LieSubmodule R H M` rather than in `Submodule R M`: the weight spaces are
`H`-submodules by construction, so this records for free that `⁅H, -⁆` preserves the span.

The bracket lemma is the only place an ambient Lie algebra `L` appears; everything else is stated
for an abstract nilpotent `H` acting on `M`.

## References

This file is the elementary weight-space infrastructure that the "Borel and the nilradicals" item
of Layer 3 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` and the highest
weight modules above it are built from: `TauCeti.rootSpaceSpan`, hence the two nilradicals, is its
instance at `M = L`.
-/

namespace TauCeti

open LieAlgebra LieModule

universe u v w

/-! ### The span of a set of weight spaces -/

section Span

variable {R : Type u} {H : Type v} [CommRing R] [LieRing H] [LieAlgebra R H]
  [LieRing.IsNilpotent H]
  {M : Type w} [AddCommGroup M] [Module R M] [LieRingModule H M] [LieModule R H M]

variable (H M) in
/-- The `H`-submodule of a module `M` spanned by the weight spaces indexed by a set `S` of
scalar-valued functions on the nilpotent Lie algebra `H`. -/
def genWeightSpaceSpan (S : Set (H → R)) : LieSubmodule R H M :=
  ⨆ chi : S, genWeightSpace M (chi : H → R)

/-- A weight space indexed by a member of `S` lies in the span of `S`. -/
theorem genWeightSpace_le_genWeightSpaceSpan {S : Set (H → R)} {chi : H → R} (h : chi ∈ S) :
    genWeightSpace M chi ≤ genWeightSpaceSpan H M S :=
  le_iSup (fun psi : S => genWeightSpace M (psi : H → R)) ⟨chi, h⟩

/-- Spans of weight spaces are monotone in the indexing set. -/
theorem genWeightSpaceSpan_mono {S T : Set (H → R)} (h : S ⊆ T) :
    genWeightSpaceSpan H M S ≤ genWeightSpaceSpan H M T :=
  iSup_le fun chi => genWeightSpace_le_genWeightSpaceSpan (h chi.2)

/-- The span of the weight spaces indexed by `S` is contained in an `H`-submodule exactly when each
of the weight spaces it is spanned by is. -/
theorem genWeightSpaceSpan_le_iff {S : Set (H → R)} {N : LieSubmodule R H M} :
    genWeightSpaceSpan H M S ≤ N ↔ ∀ chi ∈ S, genWeightSpace M chi ≤ N :=
  ⟨fun h _ hchi => (genWeightSpace_le_genWeightSpaceSpan hchi).trans h,
    fun h => iSup_le fun chi => h chi chi.2⟩

variable (H M) in
/-- The span of the weight spaces indexed by `S`, written as the supremum of those weight spaces,
so that a member of the span can be taken apart by `LieSubmodule.iSup_induction`. -/
theorem genWeightSpaceSpan_eq_iSup (S : Set (H → R)) :
    genWeightSpaceSpan H M S = ⨆ chi : S, genWeightSpace M (chi : H → R) :=
  le_antisymm (genWeightSpaceSpan_le_iff.mpr fun chi hchi =>
      le_iSup (fun psi : S => genWeightSpace M (psi : H → R)) ⟨chi, hchi⟩)
    (iSup_le fun chi => genWeightSpace_le_genWeightSpaceSpan chi.2)

end Span

/-! ### The action of a root vector on a span of weight spaces -/

section Root

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} [LieRing.IsNilpotent H]
  {M : Type w} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **A root vector moves the span of a set of weight spaces to the span of the shifted set**: a
vector in the root space of `alpha` carries the weight space at `chi` into the weight space at
`alpha + chi`. -/
theorem lie_mem_genWeightSpaceSpan {S T : Set (H → R)} {alpha : H → R} {x : L}
    (hx : x ∈ rootSpace H alpha) (hST : ∀ chi ∈ S, alpha + chi ∈ T)
    {m : M} (hm : m ∈ genWeightSpaceSpan H M S) : ⁅x, m⁆ ∈ genWeightSpaceSpan H M T := by
  rw [genWeightSpaceSpan_eq_iSup] at hm
  refine LieSubmodule.iSup_induction (fun chi : S => genWeightSpace M (chi : H → R))
    (motive := fun m => ⁅x, m⁆ ∈ genWeightSpaceSpan H M T) hm (fun chi y hy => ?_) (by simp)
    (fun y z hy hz => by rw [lie_add]; exact add_mem hy hz)
  exact genWeightSpace_le_genWeightSpaceSpan (hST _ chi.2)
    (lie_mem_genWeightSpace_of_mem_genWeightSpace (M := M) hx hy)

end Root

end TauCeti
