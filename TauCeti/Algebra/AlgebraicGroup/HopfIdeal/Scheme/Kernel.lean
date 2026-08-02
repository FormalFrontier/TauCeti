/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The kernel of a morphism of affine group schemes

A morphism `f : H ⟶ K` of commutative Hopf algebras induces contravariantly a morphism of
affine group schemes `Spec K ⟶ Spec H` over `Spec R`. This file packages its kernel: the
closed subgroup scheme of `Spec K` cut out by the kernel Hopf ideal
(`TauCeti.CommHopfAlgCat.kernelHopfIdeal`, the extension `K·f(H⁺)` of the augmentation
ideal, whose kernel semantics — the trivialization criterion — live in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel`). The inclusion is a closed
immersion by `TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`, and the
scheme-level triangle here is the image of the coordinate-ring triangle under `hopfSpec`.
The pullback square against the unit section is future work; the points-level kernel
property is `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff` in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel`.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelSpec` and `TauCeti.CommHopfAlgCat.kernelSpecι`: the
  kernel closed subgroup scheme and its inclusion.
* `TauCeti.CommHopfAlgCat.kernelSpecι_comp`: the scheme-level triangle.

## References

Milne, *Algebraic Groups*, Proposition 4.1. The same-universe restriction on the Hopf
algebras is imposed by Mathlib's current `hopfSpec` construction, as in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{u} R}

/-- The kernel of the induced morphism of affine group schemes, as an affine group
scheme: the closed subgroup scheme of the source cut out by the kernel Hopf ideal. -/
noncomputable abbrev kernelSpec (f : H ⟶ K) :
    Grp (Over (Spec (CommRingCat.of R))) :=
  quotientSpec K (kernelHopfIdeal f)

/-- The inclusion of the kernel into the source group scheme. Its underlying scheme
morphism is a closed immersion by
`TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι`. -/
noncomputable def kernelSpecι (f : H ⟶ K) :
    kernelSpec f ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op K) :=
  quotientSpecι K (kernelHopfIdeal f)

/-- `kernelSpecι` is the quotient inclusion at the kernel Hopf ideal. -/
theorem kernelSpecι_def (f : H ⟶ K) :
    kernelSpecι f = quotientSpecι K (kernelHopfIdeal f) := by
  -- `kernelSpecι` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change quotientSpecι K (kernelHopfIdeal f) = _
  rfl

/-- The scheme-level triangle: the composite of the kernel inclusion with the induced
group-scheme morphism is the trivial morphism, the image under `hopfSpec` of the
counit-unit composite. Not a `simp` lemma: Mathlib's simp set unfolds `hopfSpec.map`
itself, so this left-hand side is not in simp-normal form. -/
theorem kernelSpecι_comp (f : H ⟶ K) :
    kernelSpecι f ≫ (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (_root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
            (Bialgebra.counitBialgHom R H))).op := by
  rw [kernelSpecι_def, quotientSpecι_def, ← Functor.map_comp, ← op_comp,
    comp_mkQuotient_kernelHopfIdeal]

end CommHopfAlgCat

end TauCeti
