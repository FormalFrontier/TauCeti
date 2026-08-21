/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Functoriality of universal enveloping algebras

A homomorphism of Lie algebras induces an algebra homomorphism of their universal enveloping
algebras. This file constructs that map directly from Mathlib's universal property and proves its
characteristic equation on the canonical Lie generators, its identity and composition laws, and
its behaviour on split monomorphisms and split epimorphisms. A Lie algebra equivalence consequently
induces an algebra equivalence of universal enveloping algebras.

The split-morphism results avoid any freeness or Poincare--Birkhoff--Witt hypothesis: a chosen
one-sided inverse of a Lie homomorphism lifts to the same one-sided inverse on enveloping algebras.
In particular, the equivalence construction is available over an arbitrary commutative ring.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.map`: the algebra homomorphism induced by a Lie algebra
  homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.mapEquiv`: the algebra equivalence induced by a Lie algebra
  equivalence.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_ι`: the induced map agrees with the original Lie
  homomorphism on the canonical generators.
* `TauCeti.UniversalEnvelopingAlgebra.map_id` and
  `TauCeti.UniversalEnvelopingAlgebra.map_comp`: enveloping-algebra maps are functorial.
* `TauCeti.UniversalEnvelopingAlgebra.map_injective_of_leftInverse` and
  `TauCeti.UniversalEnvelopingAlgebra.map_surjective_of_rightInverse`: split morphisms remain split
  after passing to enveloping algebras.

## Roadmap

This supplies functoriality needed by the explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. That construction forms the Kostant integral form inside
the universal enveloping algebra of a Chevalley Lie algebra. Isomorphisms of the pinned root data
act first on the Chevalley generators; `map` and `mapEquiv` lift those actions to the enveloping
algebra, where preservation of the Kostant form can be stated and proved. The pinned isomorphism
theorem then consumes that construction, and `TauCetiRoadmap/CFSGStatement/README.md` milestone L1
uses it to realize diagram permutations as graph automorphisms of the pinned group.

No Poincare--Birkhoff--Witt theorem or injectivity of the canonical Lie map is asserted here.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The algebra homomorphism of universal enveloping algebras induced by a Lie algebra
homomorphism.

It is the unique algebra homomorphism sending the canonical generator `ι R x` to `ι R (f x)`;
`map_ι` is the corresponding computation rule and `map_unique` is the universal property in that
form. -/
noncomputable def map (f : LieHom R L M) :
    _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  _root_.UniversalEnvelopingAlgebra.lift R
    ((_root_.UniversalEnvelopingAlgebra.ι R).comp f)

/-- An enveloping-algebra map acts on the canonical Lie generators by the original Lie
homomorphism. -/
-- `simp`-normal form is `map_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem map_ι (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x) := by
  rw [map, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact LieHom.comp_apply _ _ _

/-- The `simp`-normal form of `map_ι`, stated for the canonical generators as `simp` writes them:
`ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem map_ι' (f : LieHom R L M) (x : L) :
    map R f (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (f x)) := by
  simpa using map_ι R f x

/-- An algebra homomorphism out of an enveloping algebra is the map induced by `f` exactly when
it sends every canonical generator to the image prescribed by `f`. -/
theorem map_unique (f : LieHom R L M)
    (g : _root_.UniversalEnvelopingAlgebra R L →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M) :
    (∀ x, g (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x)) ↔ g = map R f := by
  rw [map]
  refine Iff.trans ?_
    (_root_.UniversalEnvelopingAlgebra.lift_unique R
      ((_root_.UniversalEnvelopingAlgebra.ι R).comp f) g)
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- The identity Lie homomorphism induces the identity algebra homomorphism. -/
@[simp]
theorem map_id :
    map R (LieHom.id : LieHom R L L) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.id_apply, AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.id_apply]

/-- Composition of Lie homomorphisms becomes composition of the induced algebra homomorphisms. -/
@[simp]
theorem map_comp (f : LieHom R L M) (g : LieHom R M N) :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [map_ι, LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply]

/-- A left inverse of Lie homomorphisms induces a left inverse of the corresponding
enveloping-algebra maps. -/
theorem map_leftInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : g.comp f = LieHom.id) : Function.LeftInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R g).comp (map R f) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R L) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A right inverse of Lie homomorphisms induces a right inverse of the corresponding
enveloping-algebra maps. -/
theorem map_rightInverse {f : LieHom R L M} {g : LieHom R M L}
    (h : f.comp g = LieHom.id) : Function.RightInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R f).comp (map R g) =
      AlgHom.id R (_root_.UniversalEnvelopingAlgebra R M) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A split monomorphism of Lie algebras induces an injective homomorphism of enveloping
algebras. -/
theorem map_injective_of_leftInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : g.comp f = LieHom.id) : Function.Injective (map R f) :=
  (map_leftInverse R h).injective

/-- A split epimorphism of Lie algebras induces a surjective homomorphism of enveloping
algebras. -/
theorem map_surjective_of_rightInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : f.comp g = LieHom.id) : Function.Surjective (map R f) :=
  (map_rightInverse R h).surjective

/-- A Lie algebra equivalence induces an algebra equivalence of universal enveloping algebras. -/
noncomputable def mapEquiv (e : LieEquiv R L M) :
    _root_.UniversalEnvelopingAlgebra R L ≃ₐ[R]
      _root_.UniversalEnvelopingAlgebra R M :=
  AlgEquiv.ofAlgHom (map R e.toLieHom) (map R e.symm.toLieHom)
    (by
      rw [← map_comp]
      have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.apply_symm_apply
      rw [h, map_id])
    (by
      rw [← map_comp]
      have h : e.symm.toLieHom.comp e.toLieHom = LieHom.id := by
        apply LieHom.ext
        exact e.symm_apply_apply
      rw [h, map_id])

/-- The algebra homomorphism underlying `mapEquiv` is the map induced by the underlying Lie
homomorphism. -/
@[simp]
theorem mapEquiv_toAlgHom (e : LieEquiv R L M) :
    (mapEquiv R e).toAlgHom = map R e.toLieHom :=
  by rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The algebra equivalence induced by a Lie equivalence acts on canonical generators by that Lie
equivalence. -/
-- `simp`-normal form is `mapEquiv_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem mapEquiv_ι (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (e x) := by
  rw [← AlgEquiv.toAlgHom_apply, mapEquiv_toAlgHom, map_ι, LieEquiv.coe_coe]

/-- The `simp`-normal form of `mapEquiv_ι`, stated for the canonical generators as `simp` writes
them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem mapEquiv_ι' (e : LieEquiv R L M) (x : L) :
    mapEquiv R e (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R (e x)) := by
  simpa using mapEquiv_ι R e x

/-- Passing the inverse Lie equivalence to enveloping algebras gives the inverse algebra
equivalence. -/
@[simp]
theorem mapEquiv_symm (e : LieEquiv R L M) :
    (mapEquiv R e).symm = mapEquiv R e.symm :=
  by
    apply AlgEquiv.ext
    intro a
    rw [mapEquiv, AlgEquiv.ofAlgHom_symm]
    simp only [AlgEquiv.ofAlgHom_apply, mapEquiv, LieEquiv.symm_symm]

/-- The identity Lie equivalence induces the identity algebra equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv R (LieEquiv.refl : LieEquiv R L L) = AlgEquiv.refl :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have hrefl : (LieEquiv.refl : LieEquiv R L L).toLieHom = LieHom.id := by
      apply LieHom.ext
      intro x
      rfl
    rw [hrefl, map_id, AlgEquiv.refl_toAlgHom]

/-- Composition of Lie equivalences becomes composition of the induced algebra equivalences. -/
@[simp]
theorem mapEquiv_trans (e : LieEquiv R L M) (d : LieEquiv R M N) :
    (mapEquiv R e).trans (mapEquiv R d) = mapEquiv R (e.trans d) :=
  by
    apply AlgEquiv.coe_toAlgHom_injective
    rw [mapEquiv_toAlgHom]
    have htrans : ((mapEquiv R e).trans (mapEquiv R d)).toAlgHom =
        (mapEquiv R d).toAlgHom.comp (mapEquiv R e).toAlgHom := by
      apply AlgHom.ext
      intro a
      simp only [AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply, AlgHom.comp_apply]
    rw [htrans, mapEquiv_toAlgHom, mapEquiv_toAlgHom]
    have hLie : (e.trans d).toLieHom = d.toLieHom.comp e.toLieHom := by
      apply LieHom.ext
      intro x
      simp only [LieEquiv.trans_apply, LieHom.comp_apply, LieEquiv.coe_coe]
    rw [hLie, map_comp]

end TauCeti.UniversalEnvelopingAlgebra
