/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso
public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The trivial abelian variety

The base `Spec K` itself, with its unique group-scheme structure, is an abelian variety over `K`.
This file constructs it as `AbelianVariety.trivial K` and identifies it as the zero object of the
category of abelian varieties over `K`.

* `AbelianVariety.trivial`: the trivial abelian variety, carried by the monoidal unit
  `𝟙_ (Over (Spec K))`, whose underlying scheme is `Spec K`;
* `AbelianVariety.dim_trivial`: its dimension is `0`;
* `AbelianVariety.isTerminalTrivial`, `AbelianVariety.isInitialTrivial`,
  `AbelianVariety.isZeroTrivial`: it is a zero object, so there is exactly one homomorphism in
  either direction between it and any abelian variety;
* `AbelianVariety.toTrivial_comp_fromTrivial`: the composite `A ⟶ trivial K ⟶ B` is the identity
  element of the group `A ⟶ B` of `MorphismGroup.lean`, so the zero object of the category and the
  neutral element of the pointwise group law agree;
* `AbelianVariety.baseChangeTrivialIso`: base change along `K → L` carries the trivial abelian
  variety over `K` to the trivial abelian variety over `L`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API, `dim`", and the roadmap's
base-change compatibility. Mathematically this is the degenerate case of the Jacobian: a curve of
genus `0` has trivial Jacobian, and there the acceptance criterion `dim (Jac X) = genus X` reads
`dim (trivial K) = 0`. No external mathematics is vendored; the proofs reuse Mathlib's group-object
structure on the monoidal unit together with its uniqueness API for the trivial group object
(`CommGrp.uniqueHomFromTrivial`, `Grp.uniqueHomToTrivial`), the terminal object of `Over S`,
preservation of terminal objects by the right adjoint `Over.pullback`, and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` together with `ringKrullDim_eq_zero_of_field`.
The geometric-integrality input is `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`.
The abelian variety itself is assembled by the existing constructor
`AbelianVariety.ofGeometricallyIntegral`; its characteristic lemmas identify the underlying group
scheme and operations without exposing the constructor's implementation.

An earlier Tau Ceti formalization of this target,
[PR #1030](https://github.com/TauCetiProject/TauCeti/pull/1030), was retired by queue housekeeping
at the review round cap without an all-green review. This file follows its overall design: the same
carrier `𝟙_ (Over (Spec K))` passed to `ofGeometricallyIntegral`, the same `trivial_toOver` /
`trivial_toScheme` / `isTerminalTrivialToOver` interface, and its
`geometricallyIntegral_of_isIso` (revised here from a low-priority instance to a plain lemma, and
placed in `TauCeti.AlgebraicGeometry.Geometrically.Integral`). It is extended here beyond
terminality to the full zero-object statement, the compatibility with the pointwise group law on
hom-sets, and the behaviour under base change.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- The spectrum of a field has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_spec_eq_zero (K : Type u) [Field K] :
    topologicalKrullDim (Spec (.of K)) = 0 := by
  -- The underlying topological space of `Spec R` *is* `PrimeSpectrum R`, definitionally
  -- (`AlgebraicGeometry.Scheme.Spec_carrier`); no lemma states `topologicalKrullDim` of a scheme
  -- in terms of its coordinate ring, and Mathlib crosses the same gap by `change`, in
  -- `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`.
  change topologicalKrullDim (PrimeSpectrum K) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

namespace AbelianVariety

open scoped Hom

noncomputable section

variable (K : Type u) [Field K]

/-- The **trivial abelian variety** over `K`: the base `Spec K` regarded as a group scheme over
itself.

It is carried by the monoidal unit `𝟙_ (Over (Spec K))`, which is a group object because it is
terminal, and whose structure morphism is the identity of `Spec K` (`Over.tensorUnit_hom`); the
identity is proper, and it is geometrically integral by `geometricallyIntegral_of_isIso`. Those
are exactly the hypotheses of `AbelianVariety.ofGeometricallyIntegral`, which assembles them. -/
def trivial : AbelianVariety K :=
  haveI hid : GeometricallyIntegral (𝟙 (Spec (.of K))) := geometricallyIntegral_of_isIso _
  haveI : IsProper (𝟙_ (Over (Spec (.of K)))).hom := by
    rw [Over.tensorUnit_hom]
    -- `infer_instance` fails on the rewritten goal because the failed attempt on the original
    -- goal is cached; `inferInstanceAs` re-elaborates the type and succeeds.
    exact inferInstanceAs (IsProper (𝟙 _))
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (.of K)))).hom := by
    rw [Over.tensorUnit_hom]
    exact hid
  ofGeometricallyIntegral (𝟙_ (Over (Spec (.of K))))

private lemma isProperTensorUnit :
    IsProper (𝟙_ (Over (Spec (.of K)))).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (IsProper (𝟙 _))

private lemma geometricallyIntegralTensorUnit :
    GeometricallyIntegral (𝟙_ (Over (Spec (.of K)))).hom := by
  haveI hid : GeometricallyIntegral (𝟙 (Spec (.of K))) := geometricallyIntegral_of_isIso _
  rw [Over.tensorUnit_hom]
  exact hid

/-- The group scheme underlying the trivial abelian variety is the monoidal unit of
`Over (Spec K)`. -/
@[simp]
lemma trivial_toOver : (trivial K).toOver = 𝟙_ (Over (Spec (.of K))) := by
  letI := isProperTensorUnit K
  letI := geometricallyIntegralTensorUnit K
  unfold trivial
  exact ofGeometricallyIntegral_toOver _

/-- The scheme underlying the trivial abelian variety is `Spec K`. -/
@[simp]
lemma trivial_toScheme : (trivial K).toScheme = Spec (.of K) := by
  simp only [toScheme, trivial_toOver, Over.tensorUnit_left]

/-- The scheme over `Spec K` underlying the trivial abelian variety is terminal: it is the
monoidal unit of `Over (Spec K)`. -/
def isTerminalTrivialToOver : IsTerminal (trivial K).toOver :=
  IsTerminal.ofIso isTerminalTensorUnit (eqToIso (trivial_toOver K).symm)

/-- The unit section of the trivial abelian variety is the identity: it is an endomorphism of a
terminal object. -/
@[simp]
lemma trivial_one :
    η[(trivial K).toOver] ≫ eqToHom (trivial_toOver K) =
      η[𝟙_ (Over (Spec (.of K)))] := by
  letI := isProperTensorUnit K
  letI := geometricallyIntegralTensorUnit K
  unfold trivial
  exact ofGeometricallyIntegral_one _

/-- The multiplication of the trivial abelian variety is the terminal projection. -/
@[simp]
lemma trivial_mul :
    μ[(trivial K).toOver] ≫ eqToHom (trivial_toOver K) =
      (eqToHom (trivial_toOver K) ⊗ₘ eqToHom (trivial_toOver K)) ≫
        μ[𝟙_ (Over (Spec (.of K)))] := by
  letI := isProperTensorUnit K
  letI := geometricallyIntegralTensorUnit K
  unfold trivial
  exact ofGeometricallyIntegral_mul _

/-- The inversion of the trivial abelian variety is the identity. -/
@[simp]
lemma trivial_inv :
    ι[(trivial K).toOver] ≫ eqToHom (trivial_toOver K) =
      eqToHom (trivial_toOver K) ≫ ι[𝟙_ (Over (Spec (.of K)))] := by
  letI := isProperTensorUnit K
  letI := geometricallyIntegralTensorUnit K
  unfold trivial
  exact ofGeometricallyIntegral_inv _

/-- The trivial abelian variety has dimension `0`. -/
@[simp]
lemma dim_trivial : (trivial K).dim = 0 := by
  rw [dim_def, trivial_toScheme, topologicalKrullDim_spec_eq_zero]

variable {K}

/-! ### The zero object -/

/-- There is exactly one homomorphism from an abelian variety to the trivial one. Since
`(trivial K).toOver` is the monoidal unit, this is Mathlib's `Grp.uniqueHomToTrivial`, transported
through the hom equivalences of the induced categories `AbelianVariety K`, `CommGrp` and `Grp`. -/
instance uniqueHomToTrivial (A : AbelianVariety K) : Unique (A ⟶ trivial K) :=
  -- `InducedCategory.homEquiv : (X ⟶ Y) ≃ (F X ⟶ F Y)` leaves the inducing map `F` implicit, and
  -- neither the expected type `Unique (A ⟶ trivial K)` nor `Equiv.trans` determines it. Each
  -- `show` therefore names the codomain hom-type, which fixes `F`: first the `CommGrp` layer that
  -- `AbelianVariety K` is induced from, then the `Grp` layer that `CommGrp` is induced from.
  -- `CommGrp.mkIso` transports the middle hom-type along `trivial_toOver`.
  let e : CommGrp.mk (trivial K).toOver ≅ CommGrp.trivial (Over (Spec (.of K))) :=
    CommGrp.mkIso (eqToIso (trivial_toOver K)) (trivial_one K) (trivial_mul K)
  ((show _ ≃ (CommGrp.mk A.toOver ⟶ CommGrp.mk (trivial K).toOver) from
      InducedCategory.homEquiv).trans
    (((Iso.refl _).homCongr e).trans
      (show _ ≃ (Grp.mk A.toOver ⟶ Grp.trivial (Over (Spec (.of K)))) from
        InducedCategory.homEquiv))).unique

/-- There is exactly one homomorphism from the trivial abelian variety to an abelian variety.
Since `(trivial K).toOver` is the monoidal unit, this is Mathlib's
`CommGrp.uniqueHomFromTrivial`, transported through the hom equivalence of the induced category
`AbelianVariety K`. -/
instance uniqueHomFromTrivial (A : AbelianVariety K) : Unique (trivial K ⟶ A) :=
  -- As in `uniqueHomToTrivial`, the `show` names the codomain hom-type to fix the inducing map
  -- implicit in `InducedCategory.homEquiv`; one layer suffices here because `CommGrp` already has
  -- the uniqueness statement. `CommGrp.mkIso` transports along `trivial_toOver`.
  let e : CommGrp.mk (trivial K).toOver ≅ CommGrp.trivial (Over (Spec (.of K))) :=
    CommGrp.mkIso (eqToIso (trivial_toOver K)) (trivial_one K) (trivial_mul K)
  ((show _ ≃ (CommGrp.mk (trivial K).toOver ⟶ CommGrp.mk A.toOver) from
      InducedCategory.homEquiv).trans
    (e.homCongr (Iso.refl _))).unique

/-- The homomorphism from an abelian variety to the trivial one, namely the identity element of
the group `A ⟶ trivial K`. Its underlying morphism over `Spec K` is the structure morphism of
`A`. -/
def toTrivial (A : AbelianVariety K) : A ⟶ trivial K :=
  1

/-- The morphism over `Spec K` underlying `toTrivial A` is the structure morphism of `A`, after
transporting its codomain along `trivial_toOver`. -/
@[simp]
lemma toOverHom_toTrivial (A : AbelianVariety K) :
    Hom.toOverHom (toTrivial A) ≫ eqToHom (trivial_toOver K) = toUnit A.toOver :=
  isTerminalTensorUnit.hom_ext _ _

/-- The scheme morphism underlying `toTrivial A` is the structure morphism of `A`, after
transporting its codomain to `Spec K`. -/
@[simp]
lemma toSchemeHom_toTrivial (A : AbelianVariety K) :
    Hom.toSchemeHom (toTrivial A) ≫ eqToHom (trivial_toScheme K) = A.toOver.hom := by
  -- `toOverHom_toTrivial` transports along `trivial_toOver`, so its `Over.Hom.left` carries
  -- `(eqToHom (trivial_toOver K)).left`. That is not in simp normal form: `Over.eqToHom_left`
  -- turns it into the `eqToHom` of `trivial_toScheme`, which is the form stated here.
  rw [show eqToHom (trivial_toScheme K) = (eqToHom (trivial_toOver K)).left from
    (Over.eqToHom_left (trivial_toOver K)).symm]
  exact congrArg Over.Hom.left (toOverHom_toTrivial A)

/-- The homomorphism from the trivial abelian variety to an abelian variety, namely the identity
element of the group `trivial K ⟶ A`. Its underlying morphism over `Spec K` is the unit section
of `A`. -/
def fromTrivial (A : AbelianVariety K) : trivial K ⟶ A :=
  1

/-- The identity element of `trivial K ⟶ A` is the unit section of `A`: it is
`toUnit (trivial K).toOver ≫ η[A.toOver]`, and the first factor is an endomorphism of a terminal
object, hence the identity. -/
@[simp]
lemma toOverHom_fromTrivial (A : AbelianVariety K) :
    eqToHom (trivial_toOver K).symm ≫ Hom.toOverHom (fromTrivial A) = η[A.toOver] := by
  rw [← Hom.one_hom]
  congr 1
  exact (isTerminalTrivialToOver K).hom_ext _ _

/-- The scheme morphism underlying `fromTrivial A` is the unit section of `A`, after transporting
its domain from `Spec K`. -/
@[simp]
lemma toSchemeHom_fromTrivial (A : AbelianVariety K) :
    eqToHom (trivial_toScheme K).symm ≫ Hom.toSchemeHom (fromTrivial A) =
      η[A.toOver].left := by
  -- As in `toSchemeHom_toTrivial`, `Over.eqToHom_left` puts the transport in simp normal form.
  rw [show eqToHom (trivial_toScheme K).symm = (eqToHom (trivial_toOver K).symm).left from
    (Over.eqToHom_left (trivial_toOver K).symm).symm]
  exact congrArg Over.Hom.left (toOverHom_fromTrivial A)

/-- The trivial abelian variety is terminal: the only homomorphism to it from an abelian variety
over `K` is that variety's structure morphism to `Spec K`. -/
def isTerminalTrivial (K : Type u) [Field K] : IsTerminal (trivial K) :=
  IsTerminal.ofUnique _

/-- The trivial abelian variety is initial: the only homomorphism from it to an abelian variety
over `K` is that variety's unit section, because a homomorphism of group schemes preserves the
unit and the unit of the trivial group scheme is the identity. -/
def isInitialTrivial (K : Type u) [Field K] : IsInitial (trivial K) :=
  IsInitial.ofUnique _

/-- The trivial abelian variety is a zero object of the category of abelian varieties over `K`. -/
lemma isZeroTrivial (K : Type u) [Field K] : IsZero (trivial K) where
  unique_to A := nonempty_unique (trivial K ⟶ A)
  unique_from A := nonempty_unique (A ⟶ trivial K)

instance (K : Type u) [Field K] : HasZeroObject (AbelianVariety K) :=
  ⟨trivial K, isZeroTrivial K⟩

/-- Factoring through the trivial abelian variety gives the identity element of the group of
homomorphisms `A ⟶ B`: the zero object of the category and the neutral element of the pointwise
group law agree. -/
@[simp]
lemma toTrivial_comp_fromTrivial (A B : AbelianVariety K) :
    toTrivial A ≫ fromTrivial B = 1 :=
  Hom.one_comp (fromTrivial B)

/-! ### Base change -/

variable (K)

/-- The scheme over `Spec L` underlying the base change of the trivial abelian variety is
terminal, because pulling back along `Spec L ⟶ Spec K` is a right adjoint and so preserves the
terminal object of `Over (Spec K)`. -/
private def isTerminalBaseChangeTrivialToOver (L : Type u) [Field L] [Algebra K L] :
    IsTerminal ((trivial K).baseChange L).toOver :=
  IsTerminal.ofIso
    ((isTerminalTrivialToOver K).isTerminalObj
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (eqToIso (baseChange_toOver (trivial K) L).symm)

/-- The base change of the trivial abelian variety along `K → L` is terminal in the category of
abelian varieties over `L`. -/
def isTerminalBaseChangeTrivial (L : Type u) [Field L] [Algebra K L] :
    IsTerminal ((trivial K).baseChange L) :=
  IsTerminal.ofUniqueHom
    (fun B ↦ Hom.mk' ((isTerminalBaseChangeTrivialToOver K L).from B.toOver)
      ((isTerminalBaseChangeTrivialToOver K L).hom_ext _ _)
      ((isTerminalBaseChangeTrivialToOver K L).hom_ext _ _))
    fun _ _ ↦ Hom.ext (congrArg Over.Hom.left
      ((isTerminalBaseChangeTrivialToOver K L).hom_ext _ _))

/-- Base change along a field extension `K → L` carries the trivial abelian variety over `K` to
the trivial abelian variety over `L`: both are terminal in the category of abelian varieties
over `L`. -/
def baseChangeTrivialIso (L : Type u) [Field L] [Algebra K L] :
    (trivial K).baseChange L ≅ trivial L :=
  (isTerminalBaseChangeTrivial K L).uniqueUpToIso (isTerminalTrivial L)

/-- The base change of the trivial abelian variety still has dimension `0`. -/
-- Not `@[simp]`: `baseChange_dim` already rewrites the left-hand side. It does not, however,
-- prove this lemma: `baseChange_dim` computes no dimension, it only replaces the left-hand side
-- by `topologicalKrullDim (pullback (trivial K).toOver.hom (Spec.map (algebraMap K L)))`, a goal
-- that neither `dim_trivial` nor the simp set can discharge. The content below is that base
-- change preserves the terminal object, via `baseChangeTrivialIso`.
lemma dim_baseChange_trivial (L : Type u) [Field L] [Algebra K L] :
    ((trivial K).baseChange L).dim = 0 := by
  rw [dim_eq_of_iso (baseChangeTrivialIso K L), dim_trivial]

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
