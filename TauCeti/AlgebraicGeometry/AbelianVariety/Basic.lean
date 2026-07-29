/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension

/-!
# Abelian varieties

This file opens the Jacobian roadmap's Layer E by defining an **abelian variety** over a field
`K`.

Following the roadmap, an abelian variety is bundled as a proper geometrically integral group
scheme over `K`. From geometric integrality and the group-scheme smoothness theorem we derive the
roadmap's smooth and geometrically connected interface, while Mathlib's rigidity theorem gives
commutativity.

We bundle the data as a structure `AbelianVariety K`, so that later roadmap targets can write
`JacobianVariety X x₀ : AbelianVariety k` and refer to `(JacobianVariety X x₀).toScheme` and
its base changes, matching `TauCetiRoadmap/JacobianChallenge/Suggested.lean`. From the bundled
hypotheses we derive:

* `AbelianVariety.isCommMonObj`: the group law is commutative, straight from Mathlib's rigidity
  theorem `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`;
* `AbelianVariety.isIntegral`: the underlying scheme is integral;
* `AbelianVariety.smooth` and `AbelianVariety.geometricallyConnected`: the roadmap's geometric
  hypotheses derived from geometric integrality;
* `AbelianVariety.dim`: the topological Krull dimension of the underlying scheme;
* `AbelianVariety.ofGeometricallyIntegral`: a constructor from the geometrically integral package
  used by Mathlib's rigidity theorem;
* `AbelianVariety.baseChange`: the base change of an abelian variety along a field extension
  `K → L` is again an abelian variety, since properness and geometric integrality are stable under
  base change and the monoidal pullback functor carries the group-object structure.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API ... Commutativity is automatic
(rigidity, `Group/Abelian.lean`)", and the roadmap's base-change compatibility. No external
mathematics is vendored; the proofs reuse Mathlib's `Over`/`GrpObj` monoidal API, the
`GeometricallyIntegral`/`IsProper` morphism-property instances, and the commutativity theorem in
`Mathlib.AlgebraicGeometry.Group.Abelian`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A geometrically irreducible morphism is geometrically connected. Kept `private` as an
implementation helper for `AbelianVariety.geometricallyConnected`; it is not part of the
abelian-variety public interface. -/
private lemma GeometricallyConnected.of_geometricallyIrreducible {X S : Scheme.{u}} {f : X ⟶ S}
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨?_⟩
  have h : geometrically (IrreducibleSpace ·) f :=
    GeometricallyIrreducible.geometrically_irreducibleSpace ..
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono (fun {X Y} f hf hint hsub ↦ ?_) _ h
  have := hf hint hsub
  infer_instance

/-- An **abelian variety** over a field `K`: a proper geometrically integral group scheme over
`Spec K`.

The group-object structure lives on `toOver : Over (Spec (.of K))`; the underlying scheme is
`toScheme = toOver.left`. The fields are the standing hypotheses of the theory: `grpObj` is the
group law, `isProper` says the structure morphism to `Spec K` is proper, and
`geometricallyIntegral` records the geometric hypothesis from which smoothness, geometric
connectedness, absolute integrality, and commutativity are derived. -/
structure AbelianVariety (K : Type u) [Field K] where
  /-- The underlying group scheme over `Spec K`. -/
  toOver : Over (Spec (.of K))
  /-- The group-object structure on `toOver`. -/
  grpObj : GrpObj toOver
  /-- The structure morphism to `Spec K` is proper. -/
  isProper : IsProper toOver.hom
  /-- The structure morphism to `Spec K` is geometrically integral. -/
  geometricallyIntegral : GeometricallyIntegral toOver.hom

namespace AbelianVariety

variable {K : Type u} [Field K]

attribute [instance] AbelianVariety.grpObj AbelianVariety.isProper
  AbelianVariety.geometricallyIntegral

/-- The underlying scheme of an abelian variety. -/
noncomputable abbrev toScheme (A : AbelianVariety K) : Scheme.{u} :=
  A.toOver.left

/-- The dimension of an abelian variety, defined as the topological Krull dimension of its
underlying scheme. -/
noncomputable abbrev dim (A : AbelianVariety K) : WithBot ℕ∞ :=
  topologicalKrullDim A.toScheme

@[simp]
lemma dim_def (A : AbelianVariety K) :
    A.dim = topologicalKrullDim A.toScheme :=
  rfl

/-- An abelian variety is smooth over the base field. -/
instance smooth (A : AbelianVariety K) : Smooth A.toOver.hom := by
  haveI : GrpObj (Over.mk A.toOver.hom) := inferInstanceAs (GrpObj A.toOver)
  exact smooth_of_grpObj A.toOver.hom

/-- An abelian variety is geometrically connected over the base field. -/
instance geometricallyConnected (A : AbelianVariety K) :
    GeometricallyConnected A.toOver.hom :=
  GeometricallyConnected.of_geometricallyIrreducible

/-- The group law of an abelian variety is commutative: a proper geometrically integral group
scheme over a field is a commutative group object. This is the abstract rigidity theorem
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, packaged for the bundled
`AbelianVariety`. -/
instance isCommMonObj (A : AbelianVariety K) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

/-- The underlying scheme of an abelian variety is integral: geometric integrality over the
one-point base `Spec K` descends to absolute integrality. In particular the underlying space is
nonempty, irreducible, and reduced. -/
instance isIntegral (A : AbelianVariety K) : IsIntegral A.toScheme :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.toOver.hom

/-- A constructor for abelian varieties from Mathlib's geometrically integral package. -/
noncomputable def ofGeometricallyIntegral (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] : AbelianVariety K where
  toOver := G
  grpObj := inferInstance
  isProper := inferInstance
  geometricallyIntegral := inferInstance

@[simp]
lemma ofGeometricallyIntegral_toOver (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    (ofGeometricallyIntegral G).toOver = G :=
  (rfl)

/-- The unit of `ofGeometricallyIntegral G` is the unit of `G`. -/
@[simp]
lemma ofGeometricallyIntegral_one (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    η[(ofGeometricallyIntegral G).toOver] ≫
        eqToHom (ofGeometricallyIntegral_toOver G) = η[G] := by
  unfold ofGeometricallyIntegral
  simp

/-- The multiplication of `ofGeometricallyIntegral G` is the multiplication of `G`. -/
@[simp]
lemma ofGeometricallyIntegral_mul (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    μ[(ofGeometricallyIntegral G).toOver] ≫
        eqToHom (ofGeometricallyIntegral_toOver G) =
      (eqToHom (ofGeometricallyIntegral_toOver G) ⊗ₘ
          eqToHom (ofGeometricallyIntegral_toOver G)) ≫ μ[G] := by
  unfold ofGeometricallyIntegral
  simp

/-- The inverse of `ofGeometricallyIntegral G` is the inverse of `G`. -/
@[simp]
lemma ofGeometricallyIntegral_inv (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    ι[(ofGeometricallyIntegral G).toOver] ≫
        eqToHom (ofGeometricallyIntegral_toOver G) =
      eqToHom (ofGeometricallyIntegral_toOver G) ≫ ι[G] := by
  unfold ofGeometricallyIntegral
  simp

/-! ### Base change along a field extension -/

/-- The base change of an abelian variety along a field extension `K → L`, obtained by pulling
back the group scheme along `Spec L → Spec K`.

Properness and geometric integrality are stable under base change, and the monoidal pullback
functor carries the group-object structure (`Functor.grpObjObj`), so the result is again an
abelian variety. This realizes the roadmap's base-change compatibility of the Jacobian at the
level of abelian varieties. -/
noncomputable def baseChange (A : AbelianVariety K) (L : Type u) [Field L]
    [Algebra K L] : AbelianVariety L where
  toOver := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs
    (IsProper (Limits.pullback.snd A.toOver.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
  geometricallyIntegral := inferInstanceAs
    (GeometricallyIntegral (Limits.pullback.snd A.toOver.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

@[simp]
lemma baseChange_toOver (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange L).toOver =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.toOver :=
  (rfl)

/-- Bundling the underlying `Over` object of a base change with `CommGrp.mk` gives the
commutative group object obtained by applying pullback. -/
lemma commGrpMk_baseChange_toOver (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    CommGrp.mk (A.baseChange L).toOver =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.obj
        (CommGrp.mk A.toOver) := by
  unfold baseChange
  rfl

/-- The unit of a base-changed abelian variety is the pullback of the original unit, with the
monoidal comparison for `Over.pullback`. -/
@[simp]
lemma baseChange_one (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    η[(A.baseChange L).toOver] ≫ eqToHom (baseChange_toOver A L) =
      Functor.LaxMonoidal.ε
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map η[A.toOver] :=
  by
    unfold baseChange
    simp

/-- The multiplication of a base-changed abelian variety is the pullback of the original
multiplication, with the monoidal comparison for `Over.pullback`. -/
@[simp]
lemma baseChange_mul (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    μ[(A.baseChange L).toOver] ≫ eqToHom (baseChange_toOver A L) =
      (eqToHom (baseChange_toOver A L) ⊗ₘ eqToHom (baseChange_toOver A L)) ≫
        Functor.LaxMonoidal.μ
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.toOver A.toOver ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map μ[A.toOver] :=
  by
    unfold baseChange
    simp

/-- The inverse of a base-changed abelian variety is the pullback of the original inverse. -/
@[simp]
lemma baseChange_inv (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    ι[(A.baseChange L).toOver] ≫ eqToHom (baseChange_toOver A L) =
      eqToHom (baseChange_toOver A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map ι[A.toOver] :=
  by
    unfold baseChange
    simp

/-- The underlying scheme of a base change is the fibre product of the abelian variety with
`Spec L` over `Spec K`. -/
@[simp]
lemma baseChange_toScheme (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange L).toScheme =
      Limits.pullback A.toOver.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  simp only [toScheme, baseChange_toOver, Over.pullback_obj_left]

@[simp]
lemma baseChange_dim (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange L).dim =
      topologicalKrullDim
        (Limits.pullback A.toOver.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) := by
  rw [dim, baseChange_toScheme]

end AbelianVariety

end AlgebraicGeometry

end TauCeti
