/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Image factorizations of commutative Hopf-algebra morphisms over a field

For a morphism `f : H ⟶ K` of commutative Hopf algebras over a field, this file packages the
canonical factorization through the quotient by its kernel Hopf ideal:

```text
H ⟶ H / ker f ⟶ K
```

The first morphism is surjective and an epimorphism, while the second is injective and a
monomorphism. Geometrically, this quotient-by-the-ring-kernel construction motivates the
coordinate algebra of the scheme-theoretic image of the represented affine-group morphism;
that geometric compatibility is not formalized here.

## Main declarations

* `TauCeti.CommHopfAlgCat.image`: the quotient Hopf algebra by the kernel of a morphism.
* `TauCeti.CommHopfAlgCat.mkImage`: the quotient morphism onto the image quotient.
* `TauCeti.CommHopfAlgCat.imageι`: the injective factor from the image quotient.
* `TauCeti.CommHopfAlgCat.mkImage_comp_imageι`: the factorization identity.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
* Mathlib's `AlgebraicGeometry.specTargetImage`, `specTargetImageRingHom`, and
  `specTargetImageFactorization` in `Mathlib.AlgebraicGeometry.AffineScheme`, whose affine
  scheme-theoretic image construction this Hopf-level quotient factorization mirrors.

This is image infrastructure for Layer 3, "Subgroups, quotients, components", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

namespace CommHopfAlgCat

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- The quotient Hopf algebra by the kernel of a morphism. -/
noncomputable abbrev image (f : H ⟶ K) : _root_.CommHopfAlgCat.{v} k :=
  quotient H (HopfIdeal.ker f.hom)

/-- The quotient morphism onto the image quotient. -/
noncomputable abbrev mkImage (f : H ⟶ K) : H ⟶ image f :=
  mkQuotient H (HopfIdeal.ker f.hom)

/-- The injective factor from the image quotient into the codomain. -/
noncomputable abbrev imageι (f : H ⟶ K) : image f ⟶ K :=
  liftQuotient (HopfIdeal.ker f.hom) f (by
    rw [HopfIdeal.ker_toIdeal]
    intro x hx
    exact hx)

/-- A morphism factors through its image quotient. -/
@[reassoc]
theorem mkImage_comp_imageι (f : H ⟶ K) : mkImage f ≫ imageι f = f :=
  mkQuotient_comp_liftQuotient (HopfIdeal.ker f.hom) f _

/-- The quotient morphism onto the image evaluates to the quotient class. -/
theorem mkImage_apply (f : H ⟶ K) (x : H) :
    (mkImage f).hom x = Ideal.Quotient.mkₐ k (HopfIdeal.ker f.hom).toIdeal x :=
  mkQuotient_apply H (HopfIdeal.ker f.hom) x

/-- The injective factor evaluates on a quotient class as the original morphism. -/
theorem imageι_mk (f : H ⟶ K) (x : H) :
    (imageι f).hom (Ideal.Quotient.mkₐ k (HopfIdeal.ker f.hom).toIdeal x) = f.hom x :=
  liftQuotient_mk (HopfIdeal.ker f.hom) f _ x

/-- The pointwise form of the factorization through the image quotient. -/
theorem imageι_mkImage_apply (f : H ⟶ K) (x : H) :
    (imageι f).hom ((mkImage f).hom x) = f.hom x := by
  rw [mkImage_apply, imageι_mk]

/-- The quotient morphism onto the image is surjective. -/
theorem mkImage_surjective (f : H ⟶ K) : Function.Surjective (mkImage f).hom :=
  Ideal.Quotient.mk_surjective

/-- The injective factor agrees with the algebra map induced from the quotient by the
kernel. -/
private theorem imageι_apply (f : H ⟶ K) (x : image f) :
    (imageι f).hom x =
      Ideal.kerLiftAlg f.hom.toAlgHom
        (Ideal.quotientEquivAlgOfEq k (HopfIdeal.ker_toIdeal f.hom) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (HopfIdeal.ker f.hom).toIdeal x
  rw [imageι_mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.kerLiftAlg_mk]
  simp only [BialgHom.coe_toAlgHom]

/-- The factor from the image quotient into the codomain is injective. -/
theorem imageι_injective (f : H ⟶ K) : Function.Injective (imageι f).hom := by
  intro x y hxy
  apply (Ideal.quotientEquivAlgOfEq k (HopfIdeal.ker_toIdeal f.hom)).injective
  apply Ideal.kerLiftAlg_injective f.hom.toAlgHom
  simpa only [← imageι_apply] using hxy

instance imageι_mono (f : H ⟶ K) : Mono (imageι f) :=
  ConcreteCategory.mono_of_injective _ (imageι_injective f)

instance mkImage_epi (f : H ⟶ K) : Epi (mkImage f) :=
  ConcreteCategory.epi_of_surjective _ (mkImage_surjective f)

end CommHopfAlgCat

end TauCeti
