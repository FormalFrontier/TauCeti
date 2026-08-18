/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.UniformRing

/-!
# Ring homomorphisms out of a completion

Two results about `UniformSpace.Completion` as a *ring*, both in the root
`UniformSpace.Completion` namespace they extend.

`UniformSpace.Completion.ringHom_ext_of_continuous` is `UniformSpace.Completion.ext` for ring
homomorphisms: two continuous ring homomorphisms out of `Completion R` that agree after composing
with the coercion from `R` are equal. `R` is a topological ring carrying a compatible uniform
additive-group structure, and nothing more: neither `CompleteSpace` nor `T0Space` is required, and
`R` need not be commutative. It lives here because it is a statement about the completion functor
rather than about any ring being completed, and it is what lets
consumers state uniqueness on the base ring instead of on the completion.

## The completion of a complete separated ring is itself

`UniformSpace.Completion.completeRingEquivSelf`: for a complete Hausdorff topological ring
`S`, the extension of the identity is a ring isomorphism `UniformSpace.Completion S ≃+* S`.
The ring homomorphism is `UniformSpace.Completion.extensionHom`; its underlying function is
that of the uniform bijection `UniformCompletion.completeEquivSelf` — the equality is
recorded as `coe_extensionHom_id` — which supplies bijectivity. The name follows
`UniformCompletion.completeEquivSelf`.

The rest of the self-equivalence material is read off that identification. The isomorphism
is uniformly continuous
because `UniformCompletion.completeEquivSelf` is a uniform equivalence, and its inverse is
uniformly continuous because it *is* the canonical map into the completion. Over a base ring
`R` acting by *uniformly continuous* scalar multiplication the same map is `R`-linear, giving
`UniformSpace.Completion.completeAlgEquivSelf`. Uniform continuity of the action is not a
convenience: it is what makes the completion an `R`-algebra in the first place, since that is
what `UniformSpace.Completion.algebra` requires.

The declarations live in the root `UniformSpace.Completion` namespace they extend, following
this repository's convention for lemmas about external types.

## Main definitions

* `UniformSpace.Completion.completeRingEquivSelf`: the ring isomorphism
  `UniformSpace.Completion S ≃+* S`.
* `UniformSpace.Completion.completeAlgEquivSelf`: the same map as an `R`-algebra equivalence,
  for a complete Hausdorff topological `R`-algebra `S` whose scalar multiplication by `R` is
  uniformly continuous (`UniformContinuousConstSMul R S`).

## Main results

* `UniformSpace.Completion.ringHom_ext_of_continuous`: two continuous ring homomorphisms out of
  a completion that agree on the image of the coercion are equal.
* `UniformSpace.Completion.coe_completeRingEquivSelf` and
  `UniformSpace.Completion.coe_completeRingEquivSelf_symm`: the isomorphism is
  `UniformCompletion.completeEquivSelf` and its inverse is the coercion into the completion.
* `UniformSpace.Completion.uniformContinuous_completeRingEquivSelf` and
  `UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm`: both directions are
  uniformly continuous, hence continuous by `UniformContinuous.continuous`.
-/

public section

namespace UniformSpace.Completion

section Ext

variable {R : Type*} [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R]
  {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]

/-- **Maps out of a completion are determined on the image of the coercion.** Two continuous
ring homomorphisms `R̂ → B` into a semiring carrying a Hausdorff topology that agree after composing
with `coeRingHom` are equal.

This is `UniformSpace.Completion.ext` packaged for ring homomorphisms: composing with
`coeRingHom` is restriction along the coercion, and density of the image does the rest. Nothing
is asked of `B` beyond a semiring structure and a Hausdorff topology — no compatibility between
the two is used — and `R` need not be commutative. -/
theorem ringHom_ext_of_continuous {g h : Completion R →+* B} (hg : Continuous g)
    (hh : Continuous h) (hcomp : g.comp coeRingHom = h.comp coeRingHom) : g = h :=
  DFunLike.ext' (ext hg hh fun x ↦ congrArg (fun k : R →+* B ↦ k x) hcomp)

end Ext

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

/-- The isomorphism undoes the canonical inclusion: on an element of `S` regarded as an
element of the completion, it returns that element. -/
@[simp]
theorem completeRingEquivSelf_coe (a : S) :
    completeRingEquivSelf S (a : UniformSpace.Completion S) = a :=
  extensionHom_coe (RingHom.id S) continuous_id a

/-- The inverse isomorphism **is** the canonical inclusion: it sends an element of `S` to
itself, regarded as an element of the completion. -/
@[simp]
theorem completeRingEquivSelf_symm_apply (a : S) :
    (completeRingEquivSelf S).symm a = (a : UniformSpace.Completion S) :=
  (RingEquiv.symm_apply_eq _).mpr (completeRingEquivSelf_coe S a).symm

/-- The isomorphism **is** the uniform bijection `UniformCompletion.completeEquivSelf`, as a
function: both are `UniformSpace.Completion.extension id`. -/
theorem coe_completeRingEquivSelf :
    ⇑(completeRingEquivSelf S) = ⇑(UniformCompletion.completeEquivSelf (α := S)) :=
  coe_extensionHom_id S

/-- The inverse isomorphism **is** the canonical map into the completion, as a function. -/
theorem coe_completeRingEquivSelf_symm :
    ⇑(completeRingEquivSelf S).symm = ((↑) : S → UniformSpace.Completion S) :=
  funext (completeRingEquivSelf_symm_apply S)

/-- The isomorphism is uniformly continuous: it is the uniform bijection
`UniformCompletion.completeEquivSelf`. -/
theorem uniformContinuous_completeRingEquivSelf :
    UniformContinuous ⇑(completeRingEquivSelf S) :=
  coe_completeRingEquivSelf S ▸ (UniformCompletion.completeEquivSelf (α := S)).uniformContinuous

/-- The inverse isomorphism is uniformly continuous: it is the canonical map into the
completion. -/
theorem uniformContinuous_completeRingEquivSelf_symm :
    UniformContinuous ⇑(completeRingEquivSelf S).symm :=
  coe_completeRingEquivSelf_symm S ▸ uniformContinuous_coe S

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R S] [UniformContinuousConstSMul R S]

/-- For a complete Hausdorff topological `R`-algebra `S` whose scalar multiplication by `R` is
uniformly continuous (`UniformContinuousConstSMul R S`, which is what gives the completion its
`R`-algebra structure), the extension of the identity is an `R`-algebra equivalence from the
completion: `completeRingEquivSelf` is `R`-linear, since it fixes the image of `R`. -/
noncomputable def completeAlgEquivSelf : UniformSpace.Completion S ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := completeRingEquivSelf S) fun r ↦ by
    rw [algebraMap_def]
    exact completeRingEquivSelf_coe S _

/-- The algebra equivalence has the same underlying map as the ring isomorphism, so `simp`
normalises the `R`-algebra bundling onto the ring one. -/
@[simp]
theorem coe_completeAlgEquivSelf :
    ⇑(completeAlgEquivSelf S R) = ⇑(completeRingEquivSelf S) := (rfl)

/-- The inverses agree too, so the two bundlings normalise together in both directions. -/
@[simp]
theorem coe_completeAlgEquivSelf_symm :
    ⇑(completeAlgEquivSelf S R).symm = ⇑(completeRingEquivSelf S).symm := (rfl)

end Algebra

end UniformSpace.Completion
