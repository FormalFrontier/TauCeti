/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso
public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The trivial abelian variety

The base `Spec K` itself, with its unique group-scheme structure, is an abelian variety over `K`.
This file constructs it as `AbelianVariety.trivial K` and identifies it as the zero object of the
category of abelian varieties over `K`.

* `AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is geometrically
  integral. This is the input that makes `Spec K` an abelian variety over `K`;
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
structure on the monoidal unit, stability of isomorphisms under base change, the terminal object of
`Over S`, preservation of terminal objects by the right adjoint `Over.pullback`, and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` together with `ringKrullDim_eq_zero_of_field`.
The abelian variety itself is assembled by the existing constructor
`AbelianVariety.ofGeometricallyIntegral`, whose body this file's companion change `@[expose]`s so
that `(trivial K).toOver` still reduces to the monoidal unit.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An isomorphism of schemes is geometrically integral.

Every base change of an isomorphism is an isomorphism, so the fibre product of `f` with a morphism
`Spec L ⟶ Y` is isomorphic to `Spec L`, which is integral because `L` is a field. -/
lemma geometricallyIntegral_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIntegral f := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd :=
    (MorphismProperty.isomorphisms Scheme).of_isPullback h (inferInstanceAs (IsIso f))
  exact IsIntegral.of_isIso (inv snd)

/-- The spectrum of a field has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_spec_eq_zero (K : Type u) [Field K] :
    topologicalKrullDim (Spec (.of K)) = 0 := by
  change topologicalKrullDim (PrimeSpectrum K) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

namespace AbelianVariety

open scoped Hom

noncomputable section

variable (K : Type u) [Field K]

/-- The **trivial abelian variety** over `K`: the base `Spec K` regarded as a group scheme over
itself.

It is carried by the monoidal unit `𝟙_ (Over (Spec K))`, which is a group object because it is
terminal, and whose structure morphism is the identity of `Spec K`; the identity is proper, and it
is geometrically integral by `geometricallyIntegral_of_isIso`. Those are exactly the hypotheses of
`AbelianVariety.ofGeometricallyIntegral`, which assembles them. -/
@[expose] def trivial : AbelianVariety K :=
  haveI : IsProper (𝟙_ (Over (Spec (.of K)))).hom :=
    inferInstanceAs (IsProper (𝟙 (Spec (.of K))))
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (.of K)))).hom :=
    show GeometricallyIntegral (𝟙 (Spec (.of K))) from geometricallyIntegral_of_isIso _
  ofGeometricallyIntegral (𝟙_ (Over (Spec (.of K))))

@[simp]
lemma trivial_toOver : (trivial K).toOver = 𝟙_ (Over (Spec (.of K))) :=
  (rfl)

@[simp]
lemma trivial_toScheme : (trivial K).toScheme = Spec (.of K) :=
  (rfl)

/-- The scheme over `Spec K` underlying the trivial abelian variety is terminal: it is the
monoidal unit of `Over (Spec K)`. -/
def isTerminalTrivialToOver : IsTerminal (trivial K).toOver :=
  isTerminalTensorUnit

/-- The trivial abelian variety has dimension `0`. -/
@[simp]
lemma dim_trivial : (trivial K).dim = 0 := by
  rw [dim_def, trivial_toScheme, topologicalKrullDim_spec_eq_zero]

variable {K}

/-! ### The zero object -/

/-- The homomorphism from an abelian variety to the trivial one, namely the identity element of
the group `A ⟶ trivial K`. Its underlying morphism over `Spec K` is the structure morphism of
`A`. -/
def toTrivial (A : AbelianVariety K) : A ⟶ trivial K :=
  1

@[simp]
lemma toOverHom_toTrivial (A : AbelianVariety K) :
    Hom.toOverHom (toTrivial A) = toUnit A.toOver :=
  (isTerminalTrivialToOver K).hom_ext _ _

@[simp]
lemma toSchemeHom_toTrivial (A : AbelianVariety K) :
    Hom.toSchemeHom (toTrivial A) = A.toOver.hom :=
  congrArg Over.Hom.left (toOverHom_toTrivial A)

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
    Hom.toOverHom (fromTrivial A) = η[A.toOver] :=
  have h : toUnit (trivial K).toOver = 𝟙 (𝟙_ (Over (Spec (.of K)))) :=
    (isTerminalTrivialToOver K).hom_ext _ _
  Hom.toOverHom_one.trans
    ((congrArg (· ≫ η[A.toOver]) h).trans (Category.id_comp η[A.toOver]))

@[simp]
lemma toSchemeHom_fromTrivial (A : AbelianVariety K) :
    Hom.toSchemeHom (fromTrivial A) = η[A.toOver].left :=
  congrArg Over.Hom.left (toOverHom_fromTrivial A)

/-- The trivial abelian variety is terminal: the only homomorphism to it from an abelian variety
over `K` is that variety's structure morphism to `Spec K`. -/
def isTerminalTrivial (K : Type u) [Field K] : IsTerminal (trivial K) :=
  IsTerminal.ofUniqueHom toTrivial fun A f ↦
    Hom.ext (congrArg Over.Hom.left
      ((isTerminalTrivialToOver K).hom_ext (Hom.toOverHom f) (Hom.toOverHom (toTrivial A))))

/-- The trivial abelian variety is initial: the only homomorphism from it to an abelian variety
over `K` is that variety's unit section, because a homomorphism of group schemes preserves the
unit and the unit of the trivial group scheme is the identity. -/
def isInitialTrivial (K : Type u) [Field K] : IsInitial (trivial K) :=
  IsInitial.ofUniqueHom fromTrivial fun A f ↦
    -- the unit of the trivial group scheme is the identity, so `Hom.one_hom` reads `f = η[A]`
    have h : Hom.toOverHom f = η[A.toOver] :=
      (Category.id_comp (Hom.toOverHom f)).symm.trans (Hom.one_hom f)
    Hom.ext (congrArg Over.Hom.left (h.trans (toOverHom_fromTrivial A).symm))

/-- The trivial abelian variety is a zero object of the category of abelian varieties over `K`. -/
lemma isZeroTrivial (K : Type u) [Field K] : IsZero (trivial K) where
  unique_to A := ⟨⟨⟨fromTrivial A⟩, fun f ↦ (isInitialTrivial K).hom_ext f _⟩⟩
  unique_from A := ⟨⟨⟨toTrivial A⟩, fun f ↦ (isTerminalTrivial K).hom_ext f _⟩⟩

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
def isTerminalBaseChangeTrivialToOver (L : Type u) [Field L] [Algebra K L] :
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
-- Not `@[simp]`: `baseChange_dim` already rewrites the left-hand side.
lemma dim_baseChange_trivial (L : Type u) [Field L] [Algebra K L] :
    ((trivial K).baseChange L).dim = 0 := by
  rw [dim_eq_of_iso (baseChangeTrivialIso K L), dim_trivial]

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
