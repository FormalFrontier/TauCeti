/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic

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
* `AbelianVariety.isLocallyNoetherian`: the underlying scheme is locally Noetherian, since the
  structure morphism is locally of finite type; this is what makes the tangent space at the
  identity finite-dimensional downstream;
* `AbelianVariety.dim`: the topological Krull dimension of the underlying scheme;
* `AbelianVariety.ofGeometricallyIntegral`: a constructor from the geometrically integral package
  used by Mathlib's rigidity theorem;
* `AbelianVariety.baseChange`: the base change of an abelian variety along a field extension
  `K → L` is again an abelian variety, since properness and geometric integrality are stable under
  base change and the monoidal pullback functor carries the group-object structure.

The unit of the group law is a `K`-rational point, so the file also records the identity-point
interface used by every later construction at the identity — the zero section
`AbelianVariety.zeroSection`, the identity point `AbelianVariety.zeroPoint`, and the resulting
identification `AbelianVariety.zeroResidueFieldRingEquiv : κ(0) ≃+* K` of the residue field there
with the ground field, with its `K`-algebra instance. These specialize the rational-point API of
`TauCeti.AlgebraicGeometry.RationalPoint.Basic` at the unit section; the tangent space built on
them lives in `TauCeti.AlgebraicGeometry.AbelianVariety.TangentSpace`.

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
  have : GrpObj (Over.mk A.toOver.hom) := inferInstanceAs (GrpObj A.toOver)
  exact smooth_of_grpObj A.toOver.hom

/-- The underlying scheme of an abelian variety is locally Noetherian. -/
instance isLocallyNoetherian (A : AbelianVariety K) : IsLocallyNoetherian A.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian A.toOver.hom

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

/-! ### The identity point

The unit of the group law is a section `Spec K ⟶ A` of the structure morphism, so it is a
`K`-rational point of `A` and the residue field there is canonically the ground field. Following
the additive convention for abelian varieties, these carry the `zero` stem. -/

/-- The zero section `Spec K ⟶ A` of an abelian variety, that is, the unit of its group law. -/
noncomputable abbrev zeroSection (A : AbelianVariety K) : Spec (.of K) ⟶ A.toScheme :=
  η[A.toOver].left

/-- The zero section is a section of the structure morphism of `A`. -/
lemma zeroSection_comp_toOver_hom (A : AbelianVariety K) :
    A.zeroSection ≫ A.toOver.hom = 𝟙 (Spec (.of K)) := by
  simpa only [Over.tensorUnit_hom] using η[A.toOver].w

/-- The identity point `0` of an abelian variety, obtained by evaluating the zero section at the
unique point of `Spec K`. Its implementation is kept opaque; use `zeroPoint_def` to rewrite it
explicitly. -/
noncomputable def zeroPoint (A : AbelianVariety K) : A.toScheme :=
  A.zeroSection (IsLocalRing.closedPoint K)

/-- The identity point is the value of the zero section. Not a simp lemma: the simp normal form
of the structure morphism at the identity point is `toOver_hom_zeroPoint`, whose left-hand side
this equation would rewrite. -/
lemma zeroPoint_def (A : AbelianVariety K) :
    A.zeroPoint = A.zeroSection (IsLocalRing.closedPoint K) :=
  (rfl)

/-- The structure morphism sends the identity point to the unique point of `Spec K`. -/
@[simp]
lemma toOver_hom_zeroPoint (A : AbelianVariety K) :
    A.toOver.hom A.zeroPoint = IsLocalRing.closedPoint K := by
  rw [zeroPoint_def]
  exact section_apply (zeroSection_comp_toOver_hom A) (IsLocalRing.closedPoint K)

/-- The residue field of an abelian variety at its identity is canonically the ground field `K`,
through the evaluation map of the zero section. -/
noncomputable def zeroResidueFieldRingEquiv (A : AbelianVariety K) :
    IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint) ≃+* K :=
  residueFieldRingEquivOfSection (zeroSection_comp_toOver_hom A)

/-- `zeroResidueFieldRingEquiv` is the evaluation map of the identity point. The argument is
transported explicitly from `zeroPoint` to the value of the zero section. -/
@[simp]
lemma zeroResidueFieldRingEquiv_apply (A : AbelianVariety K)
    (z : IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) :
    A.zeroResidueFieldRingEquiv z =
      A.toScheme.descResidueField (Scheme.stalkClosedPointTo A.zeroSection)
        (A.zeroPoint_def ▸ z) := by
  exact residueFieldRingEquivOfSection_apply (zeroSection_comp_toOver_hom A)
    (A.zeroPoint_def ▸ z)

/-- The residue field at the identity is a `K`-algebra through `zeroResidueFieldRingEquiv`. -/
noncomputable instance algebraZeroResidueField (A : AbelianVariety K) :
    Algebra K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) :=
  A.zeroResidueFieldRingEquiv.symm.toRingHom.toAlgebra

/-- The structure map of the `K`-algebra `κ(0)` is the inverse of
`zeroResidueFieldRingEquiv`. -/
@[simp]
lemma algebraMap_zeroResidueField (A : AbelianVariety K) (k : K) :
    algebraMap K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) k =
      A.zeroResidueFieldRingEquiv.symm k := by
  rw [RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

/-- A constructor for abelian varieties from Mathlib's geometrically integral package. -/
noncomputable def ofGeometricallyIntegral (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] : AbelianVariety K where
  toOver := G
  grpObj := inferInstance
  isProper := inferInstance
  geometricallyIntegral := inferInstance

@[simp]
lemma ofGeometricallyIntegral_toOver (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] : (ofGeometricallyIntegral G).toOver = G :=
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
  -- After `unfold` the named casts are between syntactically equal objects, so `change` reduces
  -- them to identities and `simp` cancels them.
  change μ[G] = (𝟙 G ⊗ₘ 𝟙 G) ≫ μ[G]
  simp

/-- The inverse of `ofGeometricallyIntegral G` is the inverse of `G`. -/
@[simp]
lemma ofGeometricallyIntegral_inv (G : Over (Spec (.of K))) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] :
    ι[(ofGeometricallyIntegral G).toOver] ≫
        eqToHom (ofGeometricallyIntegral_toOver G) =
      eqToHom (ofGeometricallyIntegral_toOver G) ≫ ι[G] := by
  unfold ofGeometricallyIntegral
  -- As in `ofGeometricallyIntegral_mul`, the named casts reduce to identities.
  change ι[G] = 𝟙 G ≫ ι[G]
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
    -- After `unfold` the named casts are between syntactically equal objects, so `change` reduces
    -- them to identities and `simp` cancels them.
    change _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
    simp

/-- The inverse of a base-changed abelian variety is the pullback of the original inverse. -/
@[simp]
lemma baseChange_inv (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    ι[(A.baseChange L).toOver] ≫ eqToHom (baseChange_toOver A L) =
      eqToHom (baseChange_toOver A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map ι[A.toOver] :=
  by
    unfold baseChange
    -- As in `baseChange_mul`, the named casts reduce to identities.
    change _ = 𝟙 _ ≫ _
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
