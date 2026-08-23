/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

-- The two structure maps of the tensor product, transported along the quotient--tensor
-- equivalence: both are computed by its `simp` lemma
-- `quotientKernelHopfIdealAlgEquiv_symm_tmul` at `k ⊗ₜ 1` resp. `1 ⊗ₜ r`.
private lemma quotientKernelHopfIdealAlgEquiv_symm_comp_includeLeft (f : H ⟶ K) :
    letI : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
    letI : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
    (quotientKernelHopfIdealAlgEquiv f).toRingEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := ↥H) (A := ↥K) (B := R)) =
        (mkQuotient K (kernelHopfIdeal f)).hom.toAlgHom.toRingHom := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  ext k
  simp

private lemma quotientKernelHopfIdealAlgEquiv_symm_comp_includeRight (f : H ⟶ K) :
    letI : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
    letI : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
    (quotientKernelHopfIdealAlgEquiv f).toRingEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ↥H) (A := ↥K) (B := R)).toRingHom =
        algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let : Algebra ↥H ↥K := f.hom.toAlgHom.toAlgebra
  let : Algebra ↥H R := (Bialgebra.counitAlgHom R ↥H).toAlgebra
  ext r
  simp

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
  exact quotientKernelHopfIdealAlgEquiv_symm_comp_includeLeft f

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
  exact quotientKernelHopfIdealAlgEquiv_symm_comp_includeRight f

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

-- The following four lemmas isolate the underlying scheme maps of the group-object square.
-- In particular, the two zero morphisms become the structural map and the identity section,
-- rather than being left to unfold inside the pullback proof.
private lemma kernelSpecι_underlying (f : H ⟶ K) :
    (Over.forget (Spec (CommRingCat.of R))).map
        ((Grp.forget (Over (Spec (CommRingCat.of R)))).map (kernelSpecι f)) =
      Spec.map (CommRingCat.ofHom
        (mkQuotient K (kernelHopfIdeal f)).hom.toAlgHom.toRingHom) := by
  rw [kernelSpecι_def, quotientSpecι_def]
  rfl

private lemma kernelSpec_to_trivial_underlying (f : H ⟶ K) :
    (Over.forget (Spec (CommRingCat.of R))).map
        ((Grp.forget (Over (Spec (CommRingCat.of R)))).map
          (0 : kernelSpec f ⟶ Grp.trivial (Over (Spec (CommRingCat.of R))))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (K ⧸ (kernelHopfIdeal f).toIdeal))) := by
  rfl

private lemma hopfSpec_map_underlying (f : H ⟶ K) :
    (Over.forget (Spec (CommRingCat.of R))).map
        ((Grp.forget (Over (Spec (CommRingCat.of R)))).map
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op)) =
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) := by
  rfl

private lemma trivial_to_hopfSpec_underlying (H : _root_.CommHopfAlgCat.{u} R) :
    (Over.forget (Spec (CommRingCat.of R))).map
        ((Grp.forget (Over (Spec (CommRingCat.of R)))).map
          (0 : Grp.trivial (Over (Spec (CommRingCat.of R))) ⟶
            (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H))) =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R H).toRingHom) := by
  rfl

/-- The Hopf spectrum of the kernel quotient is the scheme-theoretic fibre over the identity.
The horizontal maps are the kernel inclusion and the identity section; the vertical maps are the
unique map to the trivial group scheme and the morphism induced by `f`, respectively. -/
theorem isPullback_kernelSpec (f : H ⟶ K) :
    IsPullback (kernelSpecι f)
      (0 : kernelSpec f ⟶ Grp.trivial (Over (Spec (CommRingCat.of R))))
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op)
      (0 : Grp.trivial (Over (Spec (CommRingCat.of R))) ⟶
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) := by
  apply IsPullback.of_map_of_faithful (Grp.forget _)
  apply IsPullback.of_map_of_faithful (Over.forget _)
  rw [kernelSpecι_underlying, kernelSpec_to_trivial_underlying,
    hopfSpec_map_underlying, trivial_to_hopfSpec_underlying]
  exact isPullback_kernelSpec_scheme f

end CommHopfAlgCat

end TauCeti
