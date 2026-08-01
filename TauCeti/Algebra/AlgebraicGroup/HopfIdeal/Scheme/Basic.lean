/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Closed subgroup schemes from Hopf ideals

A Hopf ideal `I` in a commutative Hopf algebra `H` determines a quotient commutative Hopf
algebra `H ⧸ I`. Applying relative spectrum contravariantly to the quotient morphism gives a
morphism of group objects

`Spec(H ⧸ I) ⟶ Spec(H)`

over `Spec R`. Its underlying morphism of schemes is a closed immersion because the coordinate
map is surjective. Thus the construction retains the scheme structure cut out by `I`, rather
than only the induced inclusion on ordinary points.

If `I ≤ J`, the quotient-to-quotient coordinate map `H ⧸ I ⟶ H ⧸ J` gives a closed immersion
`Spec(H ⧸ J) ⟶ Spec(H ⧸ I)`. The ambient triangle, identity, and composition laws below record
that these closed subgroup schemes depend contravariantly on the Hopf ideal. For a finite-type
coordinate Hopf algebra, the quotient group scheme remains locally of finite type over the base.

The pinned affine-group-scheme bridge requires the base ring and the Hopf-algebra carrier to lie
in the same universe, which is reflected in all scheme-level declarations in this file.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientSpec`: the group scheme represented by `H ⧸ I`.
* `TauCeti.CommHopfAlgCat.quotientSpecι`: its group-object morphism to the group scheme
  represented by `H`.
* `TauCeti.CommHopfAlgCat.quotientSpecι_isClosedImmersion`: the underlying scheme morphism of
  `quotientSpecι` is a closed immersion.
* `TauCeti.CommHopfAlgCat.quotientSpecMapOfLe`: the closed subgroup morphism induced by
  `I ≤ J`.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotientSpec_locallyOfFiniteType`: a finite-type Hopf
  algebra has quotient group schemes locally of finite type over `Spec R`.

## References

Milne, *Algebraic Groups*, Definition 3.10 and Propositions 3.12 and 3.15, describes Hopf-ideal
quotients and their relation to closed subgroup schemes over a field. The forward construction
used here works over an arbitrary commutative ring and is supplied by Tau Ceti's quotient Hopf
algebra API together with Mathlib's affine `Spec` and closed-immersion APIs.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

private lemma hopfSpec_map_left {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B) :
    ((AlgebraicGeometry.hopfSpec S).map f.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) :=
  rfl

private lemma hopfSpec_map_isClosedImmersion_of_surjective {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) :
    IsClosedImmersion ((AlgebraicGeometry.hopfSpec S).map f.op).hom.hom.left := by
  rw [hopfSpec_map_left]
  exact IsClosedImmersion.spec_of_surjective _ hf

/-- The affine group scheme represented by the quotient Hopf algebra `H ⧸ I`.

The same-universe restriction on `H` is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable abbrev quotientSpec (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op (quotient H I))

/-- The group-object morphism `Spec(H ⧸ I) ⟶ Spec(H)` induced contravariantly by the quotient
Hopf-algebra morphism `H ⟶ H ⧸ I`. -/
@[expose] noncomputable def quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    quotientSpec H I ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (mkQuotient H I).op

/-- `quotientSpecι` is the image under `hopfSpec` of the opposite quotient morphism. -/
lemma quotientSpecι_def (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    quotientSpecι H I =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (mkQuotient H I).op :=
  rfl

/-- The underlying scheme morphism of `quotientSpecι` is a closed immersion. Thus the quotient
Hopf algebra defines a closed subgroup scheme of the affine group scheme represented by `H`. -/
instance quotientSpecι_isClosedImmersion (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : IsClosedImmersion (quotientSpecι H I).hom.hom.left := by
  rw [quotientSpecι_def]
  apply hopfSpec_map_isClosedImmersion_of_surjective
  change Function.Surjective (Ideal.Quotient.mkₐ R I.toIdeal)
  exact Ideal.Quotient.mkₐ_surjective R I.toIdeal

/-- If `I ≤ J`, the quotient coordinate map `H ⧸ I ⟶ H ⧸ J` induces the group-object morphism
`Spec(H ⧸ J) ⟶ Spec(H ⧸ I)`. -/
@[expose] noncomputable def quotientSpecMapOfLe (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotientSpec H J ⟶ quotientSpec H I :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (quotientMapOfLe H hIJ).op

/-- `quotientSpecMapOfLe` is the image under `hopfSpec` of the opposite quotient-to-quotient
morphism. -/
lemma quotientSpecMapOfLe_def (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    quotientSpecMapOfLe H hIJ =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (quotientMapOfLe H hIJ).op :=
  rfl

/-- The scheme morphism underlying `quotientSpecMapOfLe` is a closed immersion. In particular,
a larger Hopf ideal defines a closed subgroup scheme of the subgroup defined by a smaller one. -/
instance quotientSpecMapOfLe_isClosedImmersion (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    IsClosedImmersion (quotientSpecMapOfLe H hIJ).hom.hom.left := by
  rw [quotientSpecMapOfLe_def]
  apply hopfSpec_map_isClosedImmersion_of_surjective
  intro q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J.toIdeal q
  exact ⟨Ideal.Quotient.mkₐ R I.toIdeal h, quotientMapOfLe_mk H hIJ h⟩

/-- The inclusion associated to `I ≤ J`, followed by the inclusion into the ambient group scheme,
is the inclusion associated to `J`. -/
@[simp]
lemma quotientSpecMapOfLe_comp_quotientSpecι (H : _root_.CommHopfAlgCat.{u} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    quotientSpecMapOfLe H hIJ ≫ quotientSpecι H I = quotientSpecι H J := by
  rw [quotientSpecMapOfLe_def, quotientSpecι_def, quotientSpecι_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp, mkQuotient_comp_quotientMapOfLe]

/-- The group-scheme inclusion induced by the reflexive inclusion `I ≤ I` is the identity. -/
@[simp]
lemma quotientSpecMapOfLe_refl (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    quotientSpecMapOfLe H (le_refl I) = 𝟙 (quotientSpec H I) := by
  rw [quotientSpecMapOfLe_def, quotientMapOfLe_refl]
  exact (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_id _

/-- Closed subgroup morphisms compose contravariantly along inclusions `I ≤ J ≤ K`. -/
@[simp]
lemma quotientSpecMapOfLe_comp (H : _root_.CommHopfAlgCat.{u} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientSpecMapOfLe H hJK ≫ quotientSpecMapOfLe H hIJ =
      quotientSpecMapOfLe H (hIJ.trans hJK) := by
  rw [quotientSpecMapOfLe_def, quotientSpecMapOfLe_def, quotientSpecMapOfLe_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp, quotientMapOfLe_comp]

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- If `H` is a finite-type commutative Hopf algebra, then the group scheme represented by
`H ⧸ I` is locally of finite type over `Spec R`. No finite-generation hypothesis on `I` is
needed. -/
instance quotientSpec_locallyOfFiniteType (H : FiniteTypeCommHopfAlgCat.{u, u} R)
    (I : HopfIdeal R H) :
    LocallyOfFiniteType (CommHopfAlgCat.quotientSpec H.obj I).X.hom := by
  let Q := quotient H I
  letI : Algebra.FiniteType R (H ⧸ I.toIdeal) := Q.property
  change LocallyOfFiniteType
    (Spec (CommRingCat.of (H ⧸ I.toIdeal)) ↘ Spec (CommRingCat.of R))
  infer_instance

end FiniteTypeCommHopfAlgCat

end TauCeti
