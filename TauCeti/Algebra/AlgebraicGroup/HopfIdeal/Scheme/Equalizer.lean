/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The equalizer of two homomorphisms of affine group schemes

Two morphisms `f g : H ⟶ K` of commutative Hopf algebras are, contravariantly, two homomorphisms
`Spec K ⟶ Spec H` of affine group schemes. The quotient of `K` by
`TauCeti.CommHopfAlgCat.equalizerHopfIdeal` represents the closed subgroup scheme of `Spec K` on
which the two agree, and this file records the resulting cone.

`equalizerSpecι` is a closed immersion equalizing the two homomorphisms, and it is universal among
homomorphisms of affine group schemes into `Spec K` that do so: such a homomorphism factors
through `equalizerSpec` in exactly one way. The factorization is the image under `hopfSpec` of the
coequalizer factorization on coordinate Hopf algebras, and its uniqueness comes from full
faithfulness of `hopfSpec` together with uniqueness of that factorization.

## Main declarations

* `TauCeti.CommHopfAlgCat.equalizerSpec` and `TauCeti.CommHopfAlgCat.equalizerSpecι`: the equalizer
  as a closed subgroup scheme of `Spec K`, together with its closed immersion.
* `TauCeti.CommHopfAlgCat.equalizerSpecι_comp_hopfSpec_map`: the equalizing equation.
* `TauCeti.CommHopfAlgCat.liftEqualizerSpec`, with
  `TauCeti.CommHopfAlgCat.liftEqualizerSpec_comp_equalizerSpecι` and
  `TauCeti.CommHopfAlgCat.liftEqualizerSpec_unique`: the universal property of that cone among
  affine group schemes.

## References

The equalizer of two homomorphisms of group schemes is a closed subgroup scheme; see
[Milne, *Algebraic Groups*][milne2017], §1.h, and Waterhouse, *Introduction to Affine Group
Schemes*, §15.3. It serves `TauCetiRoadmap/ReductiveGroups/README.md`, "Hopf ideals ↔ closed
subgroup schemes".
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K Y : _root_.CommHopfAlgCat.{u} R}

/-- The **equalizer group scheme** of two homomorphisms of affine group schemes: the closed
subgroup scheme of `Spec K` cut out by the equalizer Hopf ideal. -/
noncomputable abbrev equalizerSpec (f g : H ⟶ K) : Grp (Over (Spec (CommRingCat.of R))) :=
  quotientSpec K (equalizerHopfIdeal f g)

/-- The inclusion of the equalizer group scheme into `Spec K`. -/
noncomputable def equalizerSpecι (f g : H ⟶ K) :
    equalizerSpec f g ⟶ (hopfSpec (CommRingCat.of R)).obj (Opposite.op K) :=
  quotientSpecι K (equalizerHopfIdeal f g)

/-- `equalizerSpecι` is the inclusion of the quotient by the equalizer Hopf ideal. -/
theorem equalizerSpecι_def (f g : H ⟶ K) :
    equalizerSpecι f g = quotientSpecι K (equalizerHopfIdeal f g) :=
  (rfl)

/-- The equalizer is a *closed* subgroup scheme of `Spec K`. -/
instance isClosedImmersion_equalizerSpecι (f g : H ⟶ K) :
    IsClosedImmersion (equalizerSpecι f g).hom.hom.left := by
  rw [equalizerSpecι_def]
  infer_instance

/-- The equalizer group scheme equalizes the two homomorphisms of affine group schemes. -/
theorem equalizerSpecι_comp_hopfSpec_map (f g : H ⟶ K) :
    equalizerSpecι f g ≫ (hopfSpec (CommRingCat.of R)).map f.op =
      equalizerSpecι f g ≫ (hopfSpec (CommRingCat.of R)).map g.op := by
  rw [equalizerSpecι_def, quotientSpecι_def, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
    ← op_comp, comp_mkQuotient_equalizerHopfIdeal]

/-- A homomorphism of affine group schemes into `Spec K` that equalizes `f` and `g` comes from a
morphism of coordinate Hopf algebras coequalizing them. -/
private theorem comp_preimage_unop_eq (f g : H ⟶ K)
    (q : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (hq : q ≫ (hopfSpec (CommRingCat.of R)).map f.op =
      q ≫ (hopfSpec (CommRingCat.of R)).map g.op) :
    f ≫ ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage q).unop =
      g ≫ ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage q).unop := by
  refine Quiver.Hom.op_inj
    ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_injective ?_)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, Quiver.Hom.op_unop,
    (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage]
  exact hq

/-- The universal property of the equalizer: a homomorphism of affine group schemes into `Spec K`
equalizing `f` and `g` factors through the equalizer group scheme. -/
noncomputable def liftEqualizerSpec (f g : H ⟶ K)
    (q : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (hq : q ≫ (hopfSpec (CommRingCat.of R)).map f.op =
      q ≫ (hopfSpec (CommRingCat.of R)).map g.op) :
    (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶ equalizerSpec f g :=
  (hopfSpec (CommRingCat.of R)).map
    (liftEqualizer (f := f) (g := g)
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage q).unop
      (comp_preimage_unop_eq f g q hq)).op

/-- The factorization law of the equalizer: `liftEqualizerSpec` followed by the inclusion of the
equalizer is the original homomorphism. -/
@[simp]
theorem liftEqualizerSpec_comp_equalizerSpecι (f g : H ⟶ K)
    (q : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (hq : q ≫ (hopfSpec (CommRingCat.of R)).map f.op =
      q ≫ (hopfSpec (CommRingCat.of R)).map g.op) :
    liftEqualizerSpec f g q hq ≫ equalizerSpecι f g = q := by
  rw [liftEqualizerSpec, equalizerSpecι_def, quotientSpecι_def, ← Functor.map_comp, ← op_comp,
    mkQuotient_comp_liftEqualizer, Quiver.Hom.op_unop,
    (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage]

/-- The uniqueness law of the equalizer: `liftEqualizerSpec` is the only factorization of `q`
through the inclusion of the equalizer group scheme. -/
theorem liftEqualizerSpec_unique (f g : H ⟶ K)
    (q : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op K))
    (hq : q ≫ (hopfSpec (CommRingCat.of R)).map f.op =
      q ≫ (hopfSpec (CommRingCat.of R)).map g.op)
    (m : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y) ⟶ equalizerSpec f g)
    (hm : m ≫ equalizerSpecι f g = q) :
    m = liftEqualizerSpec f g q hq := by
  have hn : mkQuotient K (equalizerHopfIdeal f g) ≫
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage m).unop =
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage q).unop := by
    refine Quiver.Hom.op_inj
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_injective ?_)
    rw [op_comp, Functor.map_comp, Quiver.Hom.op_unop, Quiver.Hom.op_unop,
      (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage,
      (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage, ← quotientSpecι_def,
      ← equalizerSpecι_def]
    exact hm
  have hpre : ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage m).unop =
      liftEqualizer ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage q).unop
        (comp_preimage_unop_eq f g q hq) :=
    liftEqualizer_unique _ _ _ hn
  rw [liftEqualizerSpec, ← hpre, Quiver.Hom.op_unop,
    (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage]

end CommHopfAlgCat

end TauCeti
