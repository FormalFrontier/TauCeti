/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Morphisms from connected affine groups to finite constant groups

Let `H` be the coordinate Hopf algebra of a connected affine group over a field
`k`, and let `G` be a finite group. Every group-scheme morphism from `Spec H` to the constant
group scheme attached to `G` is trivial. Contravariantly, every bialgebra morphism

```text
  k^G ⟶ H
```

is the composite of the counit of `k^G` and the unit of `H`.

The proof uses the characteristic functions of the elements of `G`. Their images are
idempotents in `H`, hence are zero or one because `Spec H` is connected. Compatibility with the
counit determines which alternative occurs: the characteristic function of the identity maps to
one, and all the others map to zero. The same computation shows that the induced map on points
has constant value the identity.

This is the connectedness input in the Lie--Kolchin induction. The derived subgroup first
produces finitely many weight spaces permuted by the ambient group; the result here makes the
resulting morphism to that finite permutation group trivial. In that application geometric
connectedness supplies connectedness of the coordinate ring after extension to an algebraic
closure.

## Main declarations

* `TauCeti.ConstantGroup.bialgHom_eq_unit_comp_counit_of_connected`: a morphism from
  a connected affine group to a finite constant group is trivial in Hopf coordinates.
* `TauCeti.ConstantGroup.point_comp_eq_one_of_connected`: the induced map on
  algebra-valued points is constantly the identity.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.34 and Chapter 2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.

This advances the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap.
-/

public section

open WithConv

namespace TauCeti.ConstantGroup

universe u v w

noncomputable section

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable (G : Type w) [Group G] [Finite G]

omit [Group G] in
private theorem functionAlgHom_eq_algebraMap_comp
    [ConnectedSpace (PrimeSpectrum H)]
    (f : (G → k) →ₐ[k] H) (q : H →ₐ[k] k) :
    f = (Algebra.ofId k H).comp (q.comp f) := by
  classical
  let _ := Fintype.ofFinite G
  apply AlgHom.toLinearMap_injective
  apply (Pi.basisFun k G).ext
  intro g
  -- Basis extensionality retains the linear-map coercions; expose its standard basis vector.
  change f (Pi.single g 1) =
    (Algebra.ofId k H) (q (f (Pi.single g 1)))
  have hidempotent : IsIdempotentElem (f (Pi.single g 1)) := by
    apply IsIdempotentElem.map
    rw [isIdempotentElem_iff]
    ext x
    by_cases hx : x = g <;> simp [hx]
  rcases TauCeti.eq_zero_or_eq_one_of_isIdempotentElem hidempotent with hzero | hone
  · rw [hzero, map_zero, map_zero]
  · rw [hone, map_one, map_one]

/-- **Every morphism from a connected affine group to a finite constant group is
trivial.**

In coordinate Hopf algebras, a morphism to the constant group attached to `G` is a bialgebra
homomorphism from its function algebra to `H`. It is necessarily the counit followed by the
unit. -/
theorem bialgHom_eq_unit_comp_counit_of_connected
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : coordinateRing k G →ₐc[k] H) :
    f = (Bialgebra.unitBialgHom k H).comp
      (Bialgebra.counitBialgHom k (coordinateRing k G)) := by
  let _ : ConnectedSpace (PrimeSpectrum H) := hconnected
  apply BialgHom.coe_toAlgHom_injective
  -- Mathlib has no theorem exposing the underlying algebra homomorphism of the bialgebra unit;
  -- put the target into that coordinate form before cancelling the function-algebra equivalence.
  change f.toAlgHom = (Algebra.ofId k H).comp
    (Bialgebra.counitAlgHom k (coordinateRing k G))
  let e := functionAlgEquiv k G
  have hf : f.toAlgHom.comp e.symm.toAlgHom =
      (Algebra.ofId k H).comp
        ((Bialgebra.counitAlgHom k H).comp (f.toAlgHom.comp e.symm.toAlgHom)) :=
    functionAlgHom_eq_algebraMap_comp G _ _
  rw [← AlgHom.comp_assoc (Bialgebra.counitAlgHom k H) f.toAlgHom e.symm.toAlgHom,
    BialgHom.counitAlgHom_comp] at hf
  apply_fun (·.comp e.toAlgHom) at hf
  simpa only [AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id] using hf

/-- A connected affine group's map to a finite constant group sends every
algebra-valued point to the identity. -/
theorem point_comp_eq_one_of_connected
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : coordinateRing k G →ₐc[k] H)
    {A : Type*} [CommRing A] [Algebra k A] (p : H →ₐ[k] A) :
    toConv (p.comp f.toAlgHom) = 1 := by
  rw [bialgHom_eq_unit_comp_counit_of_connected G hconnected f]
  apply ofConv_injective
  ext x
  simp only [BialgHom.comp_toAlgHom, AlgHom.comp_apply, AlgHom.convOne_apply]
  -- Mathlib has no application lemma for the bialgebra unit; unfold that value explicitly.
  change p (algebraMap k H (Coalgebra.counit x)) =
    algebraMap k A (Coalgebra.counit x)
  exact p.commutes _

end

end TauCeti.ConstantGroup
