/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Semilinear functoriality of Kähler differentials along algebra homomorphisms

For an `R`-algebra homomorphism `f : A →ₐ[R] B`, the induced map on Kähler differentials sends
`D x` to `D (f x)`. It is `R`-linear, since `f` fixes `R`, but it moves the `A`-action through
`f` — it is `f`-**semilinear**, `mapSemilinear f (a • ω) = f a • mapSemilinear f ω` — so it is
packaged as a semilinear map `Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`, following the precedent of
`LinearMap.frobenius`. The motivating special case is an algebra *endomorphism*
`f : S →ₐ[R] S` (for instance Frobenius), where this is the pullback of differentials along `f`
and where the map need not be `S`-linear.

Mathlib's `KaehlerDifferential.map` is functoriality for a *tower* `[Algebra A B]`
`[IsScalarTower R A B]`, so it cannot state this map: for an arbitrary `f : A →ₐ[R] B` no
`Algebra A B` instance exists, and for an endomorphism, installing one would clash with
`Algebra.id`. The two structures induced by `f` do exist *locally*, however, and `mapSemilinear` is
`KaehlerDifferential.map` under those local `letI` instances, repackaged with the `A`-action on
the target unfolded into `f`-semilinearity — which is exactly the statement that survives
outside the `letI` scope.

## Main definitions

* `KaehlerDifferential.mapSemilinear f : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`

## Main results

* `KaehlerDifferential.mapSemilinear_D`: `mapSemilinear f (D x) = D (f x)`. This
  characterises the map: `Ω[A⁄R]` is spanned by the range of `D` (`span_range_derivation`), so
  two semilinear maps agreeing there are equal by `LinearMap.ext_on`.
* `KaehlerDifferential.mapSemilinear_toAlgHom_apply`: on a tower it agrees with Mathlib's
  `KaehlerDifferential.map`.
* `KaehlerDifferential.mapSemilinear_smul`: the semilinearity law, with `f` applied rather than
  `f.toRingHom`.
* `KaehlerDifferential.mapSemilinear_id`, `mapSemilinear_id_apply`: the identity acts as the
  identity.
* `KaehlerDifferential.mapSemilinear_comp_apply`, `mapSemilinear_comp`: compatibility with
  composition.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/PullbackKaehler.lean`, declarations `AlgHom.pullbackKaehler`,
`pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
and `pullbackKaehler_id`. The source treats an endomorphism of a fixed `S`, exports an
`AddMonoidHom` with hand-stated semilinearity lemmas, and builds the map from scratch through a
public `TwistedKaehler` module; here the map is generalised to an arbitrary `R`-algebra
homomorphism `A →ₐ[R] B`, constructed from Mathlib's `KaehlerDifferential.map`, and exported as
the semilinear map, whose type already carries the scalar law the source stated by hand.
-/

namespace KaehlerDifferential

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

public section

/-- **The map of Kähler differentials along an `R`-algebra homomorphism** `f : A →ₐ[R] B`,
characterised by `mapSemilinear f (D x) = D (f x)`. It is `f`-semilinear:
`mapSemilinear f (a • ω) = f a • mapSemilinear f ω` (`mapSemilinear_smul`).

This is `KaehlerDifferential.map` under the local `Algebra A B` structure induced by `f`,
repackaged semilinearly so that the statement survives outside that instance's scope. -/
noncomputable def mapSemilinear (f : A →ₐ[R] B) : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R] :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toFun := KaehlerDifferential.map R R A B
    map_add' := map_add _
    map_smul' := fun a ω => by
      -- The `A`-action induced by `f` on the target unfolds to acting through `f`.
      rw [LinearMap.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (KaehlerDifferential.map R R A B ω)).symm }

/-- `mapSemilinear f` sends `D x` to `D (f x)`. -/
@[simp]
theorem mapSemilinear_D (f : A →ₐ[R] B) (x : A) : mapSemilinear f (D R A x) = D R B (f x) :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  KaehlerDifferential.map_D R R A B x

/-- The semilinearity law of `mapSemilinear`, stated with `f` applied rather than
`f.toRingHom`.

This is not interchangeable with the generic `map_smulₛₗ`: that lemma produces the coefficient
`f.toRingHom a`, which is only *definitionally* `f a`, and it carries no `@[simp]` attribute, so
`simp` alone leaves `mapSemilinear f (a • ω)` untouched. This is the simp-normal form. -/
@[simp]
theorem mapSemilinear_smul (f : A →ₐ[R] B) (a : A) (ω : Ω[A⁄R]) :
    mapSemilinear f (a • ω) = f a • mapSemilinear f ω :=
  (mapSemilinear f).map_smulₛₗ a ω

/-- The map along the identity is the identity, as (plainly linear) maps. -/
theorem mapSemilinear_id :
    (mapSemilinear (AlgHom.id R A) : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = LinearMap.id :=
  LinearMap.ext_on (span_range_derivation R A) <| by
    rintro _ ⟨x, rfl⟩; exact mapSemilinear_D _ x

/-- The map along the identity fixes every differential. -/
@[simp]
theorem mapSemilinear_id_apply (ω : Ω[A⁄R]) : mapSemilinear (AlgHom.id R A) ω = ω :=
  DFunLike.congr_fun mapSemilinear_id ω

/-- Functoriality of `mapSemilinear`, at map level. -/
theorem mapSemilinear_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    mapSemilinear (f.comp g) = (mapSemilinear f).comp (mapSemilinear g) :=
  LinearMap.ext_on (span_range_derivation R A) <| by
    rintro _ ⟨x, rfl⟩
    rw [mapSemilinear_D, LinearMap.comp_apply, mapSemilinear_D, mapSemilinear_D, AlgHom.comp_apply]

/-- `mapSemilinear` is functorial: mapping along `f.comp g` is mapping along `g`, then along
`f`. -/
@[simp]
theorem mapSemilinear_comp_apply (f : B →ₐ[R] C) (g : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    mapSemilinear (f.comp g) ω = mapSemilinear f (mapSemilinear g ω) :=
  DFunLike.congr_fun (mapSemilinear_comp f g) ω

/-- On a tower, `mapSemilinear` along the structure map is Mathlib's `KaehlerDifferential.map`
— the sense in which this construction extends the tower functoriality to arbitrary algebra
homomorphisms. -/
@[simp]
theorem mapSemilinear_toAlgHom_apply [Algebra A B] [IsScalarTower R A B] (ω : Ω[A⁄R]) :
    mapSemilinear (IsScalarTower.toAlgHom R A B) ω = KaehlerDifferential.map R R A B ω := by
  -- Unlike the identity and composition laws this cannot be proved at map level: the two sides
  -- are semilinear over `algebraMap A B` and linear over `A`, i.e. the same function at different
  -- types, so `LinearMap.ext_on` has no equation to prove. Hence the induction.
  induction (span_range_derivation R A ▸ Submodule.mem_top :
      ω ∈ Submodule.span A (Set.range (D R A))) using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨x, rfl⟩ := hω
    rw [mapSemilinear_D, KaehlerDifferential.map_D, IsScalarTower.toAlgHom_apply]
  | zero => rw [map_zero, map_zero]
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  | smul a ω _ ih =>
    rw [mapSemilinear_smul, LinearMap.map_smul, ih]
    exact IsScalarTower.algebraMap_smul B a _

end

end KaehlerDifferential
