/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Bases

/-!
# A group with countably generated neighbourhoods of the identity is first countable

`FirstCountableTopology` asks every point's neighbourhood filter to be countably generated. In a
group whose multiplication is separately continuous it is enough to ask it at the identity: left
translation is a homeomorphism, so `𝓝 a` is the image of `𝓝 1` under it, and the image of a
countably generated filter is countably generated.

This matters because countable generation at the identity is what the *proofs* in this area
assume — Henkel's open mapping theorem and
`NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup` both state it that way — whereas
`FirstCountableTopology` is the class **Mathlib's own instances are keyed on**. Without the bridge
the two do not meet. For a countable index type `ι`, countable generation of `𝓝 (0 : ι → G)`
is a mathematical *consequence* of countable generation at `0` in `G` — but it does not
**synthesize**: `𝓝` on a `Pi` type is not syntactically a `Filter.pi`, so
`Filter.pi.isCountablyGenerated` never fires on the goal as stated. The obstruction there is
purely one of instance search. With this instance that product, and the subtype and
additive-quotient forms, all resolve.

Countability of the index set is a real hypothesis there and not merely a syntactic one: an
uncountable product of nontrivial groups is not first countable at all, which is why Mathlib's `Pi`
instance carries `[Countable ι]`.

Mathlib's own route into the class for groups runs through the uniformity —
`IsUniformGroup.uniformity_countably_generated` derives `(𝓤 G).IsCountablyGenerated` from
`[(𝓝 (1 : G)).IsCountablyGenerated]`, and `UniformSpace.firstCountableTopology` turns that into
the class. That route is a theorem rather than an instance and needs a `UniformSpace` structure on
`G`; the instance below covers a plain topological group and makes the synthesis automatic.
`Mathlib/Topology/Bases.lean` carries a standing "more fine grained instances for
`FirstCountableTopology`" note where this would sit.

## Main results

* `SeparatelyContinuousMul.toFirstCountableTopology`, with its additive form
  `SeparatelyContinuousAdd.toFirstCountableTopology`.
-/

namespace TauCeti

open Filter Topology

public section

/-- **A group whose identity has countably generated neighbourhoods is first countable.** Left
translation by `a` is a homeomorphism carrying `𝓝 1` to `𝓝 a`, and `Filter.map` preserves
countable generation.

Only the identity is assumed, because that is the form the surrounding theory states — see the
module docstring. Only separate continuity of multiplication is needed: the argument runs through
left translation alone and never uses continuity of inversion. -/
@[to_additive SeparatelyContinuousAdd.toFirstCountableTopology]
-- see Note [lower instance priority]
instance (priority := 100) SeparatelyContinuousMul.toFirstCountableTopology {G : Type*} [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [(𝓝 (1 : G)).IsCountablyGenerated] :
    FirstCountableTopology G :=
  ⟨fun a ↦ by
    have h : 𝓝 a = Filter.map (a * ·) (𝓝 (1 : G)) := by
      simpa using ((Homeomorph.mulLeft a).map_nhds_eq (1 : G)).symm
    rw [h]
    infer_instance⟩

end

end TauCeti
