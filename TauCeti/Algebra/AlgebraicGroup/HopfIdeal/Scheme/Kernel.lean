/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

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
The quotient--tensor identification presents this kernel as the scheme-theoretic fibre over
the identity section, and the resulting pullback square lifts from schemes to group objects.
The points-level kernel property is `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff` in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel`.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelSpec` and `TauCeti.CommHopfAlgCat.kernelSpecι`: the
  kernel closed subgroup scheme and its inclusion.
* `TauCeti.CommHopfAlgCat.kernelSpecι_comp`: the scheme-level triangle.
* `TauCeti.CommHopfAlgCat.isPullback_kernelSpec`: the kernel square against the identity
  section is a pullback of group schemes.

## References

Milne, *Algebraic Groups*, Proposition 4.1. The same-universe restriction on the Hopf
algebras is imposed by Mathlib's current `hopfSpec` construction, as in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic`.
-/

public section

open CategoryTheory CategoryTheory.Limits

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

-- The affine comparison expressing the quotient spectrum as the spectrum of the tensor
-- product, followed by the canonical affine pullback presentation.
private noncomputable def kernelSpecPullbackIso (f : H ⟶ K) :
    Spec (CommRingCat.of (K ⧸ (kernelHopfIdeal f).toIdeal)) ≅
      pullback
        (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
        (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H).toRingHom)) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  exact
    (Scheme.Spec.mapIso
      (quotientKernelHopfIdealAlgEquiv f).toRingEquiv.toCommRingCatIso.op).symm ≪≫
      (pullbackSpecIso H K R).symm

private lemma kernelSpecPullbackIso_hom_fst (f : H ⟶ K) :
    (kernelSpecPullbackIso f).hom ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
          (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        (mkQuotient K (kernelHopfIdeal f)).hom.toAlgHom.toRingHom) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  simp only [kernelSpecPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    RingEquiv.toCommRingCatIso_inv]
  rw [Category.assoc, pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp, Spec.map_inj]
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext k
  change (quotientKernelHopfIdealAlgEquiv f).symm (k ⊗ₜ[↥H] 1) =
    (mkQuotient K (kernelHopfIdeal f)).hom k
  rw [quotientKernelHopfIdealAlgEquiv_symm_tmul, mkQuotient_apply, map_one,
    one_mul, Ideal.Quotient.mkₐ_eq_mk]

private lemma kernelSpecPullbackIso_hom_snd (f : H ⟶ K) :
    (kernelSpecPullbackIso f).hom ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
          (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal))) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  simp only [kernelSpecPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    RingEquiv.toCommRingCatIso_inv]
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp, Spec.map_inj]
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext r
  change (quotientKernelHopfIdealAlgEquiv f).symm (1 ⊗ₜ[↥H] r) =
    algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal) r
  rw [quotientKernelHopfIdealAlgEquiv_symm_tmul, mul_one,
    Ideal.Quotient.mk_algebraMap]

private lemma isPullback_kernelSpec_scheme (f : H ⟶ K) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (mkQuotient K (kernelHopfIdeal f)).hom.toAlgHom.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal))))
      (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R H).toRingHom)) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (kernelSpecPullbackIso f)
    (kernelSpecPullbackIso_hom_fst f) (kernelSpecPullbackIso_hom_snd f)
  rw [← kernelSpecPullbackIso_hom_fst f, ← kernelSpecPullbackIso_hom_snd f,
    Category.assoc, Category.assoc, pullback.condition]

/-- The Hopf spectrum of the kernel quotient is the scheme-theoretic fibre over the identity.
The horizontal maps are the kernel inclusion and the unique map to the trivial group scheme;
the vertical maps are the morphism induced by `f` and the identity section, respectively. -/
theorem isPullback_kernelSpec (f : H ⟶ K) :
    IsPullback (kernelSpecι f)
      (0 : kernelSpec f ⟶ Grp.trivial (Over (Spec (CommRingCat.of R))))
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op)
      (0 : Grp.trivial (Over (Spec (CommRingCat.of R))) ⟶
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) := by
  apply IsPullback.of_map_of_faithful (Grp.forget _)
  apply IsPullback.of_map_of_faithful (Over.forget _)
  convert isPullback_kernelSpec_scheme f using 1 <;> try rfl
  rw [kernelSpecι_def, quotientSpecι_def]
  rfl

end CommHopfAlgCat

end TauCeti
