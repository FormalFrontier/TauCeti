/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.UniformRing

/-!
# The completion of a complete separated ring is itself

`UniformSpace.Completion.completeRingEquivSelf`: for a complete Hausdorff topological ring
`S`, the extension of the identity is a ring isomorphism `UniformSpace.Completion S ≃+* S`.
The ring homomorphism is `UniformSpace.Completion.extensionHom`; its underlying function is
that of the uniform bijection `UniformCompletion.completeEquivSelf` — the equality is
recorded as `coe_extensionHom_id` — which supplies bijectivity. The name follows
`UniformCompletion.completeEquivSelf`.

The declarations live in the root `UniformSpace.Completion` namespace they extend, following
this repository's convention for lemmas about external types.
-/

public section

namespace UniformSpace.Completion

variable (S : Type*) [Ring S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S]
  [CompleteSpace S] [T0Space S]

/-- The extension of the identity ring homomorphism and the uniform bijection
`UniformCompletion.completeEquivSelf` are the same function: both are
`UniformSpace.Completion.extension id`. -/
private theorem coe_extensionHom_id :
    ⇑(extensionHom (RingHom.id S) continuous_id) =
      ⇑(UniformCompletion.completeEquivSelf (α := S)) := (rfl)

/-- For a complete Hausdorff topological ring, the extension of the identity is a ring
isomorphism from the completion. -/
noncomputable def completeRingEquivSelf : UniformSpace.Completion S ≃+* S :=
  RingEquiv.ofBijective (extensionHom (RingHom.id S) continuous_id)
    (coe_extensionHom_id S ▸ (UniformCompletion.completeEquivSelf (α := S)).bijective)

@[simp]
theorem completeRingEquivSelf_coe (a : S) :
    completeRingEquivSelf S (a : UniformSpace.Completion S) = a :=
  extensionHom_coe (RingHom.id S) continuous_id a

@[simp]
theorem completeRingEquivSelf_symm_apply (a : S) :
    (completeRingEquivSelf S).symm a = (a : UniformSpace.Completion S) :=
  (RingEquiv.symm_apply_eq _).mpr (completeRingEquivSelf_coe S a).symm

end UniformSpace.Completion
