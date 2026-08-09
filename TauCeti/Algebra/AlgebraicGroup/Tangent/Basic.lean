/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.Coalgebra.Convolution
public import TauCeti.RingTheory.Derivation.DualNumber

/-!
# The tangent space at the identity point

For a bialgebra `A` over `R`, the identity `B`-point of the functor of points is the
counit followed by the structure map — the unit of the convolution
monoid whenever the latter exists. This file packages `B` as an `A`-algebra through that point
(`Bialgebra.CounitAlgebra`), so that the dual-number dictionary
`TauCeti.derivationToDualNumberEquivLift` applies verbatim: derivations of `A` at the
identity point are the dual-number points lying over the identity
(the dictionary applied at `Bialgebra.CounitAlgebra`).

For `A` a Hopf algebra and `B` commutative, the dual-number points form a convolution
group, reduction of the infinitesimal part is a group homomorphism
(`dualNumberReduction`), and its kernel `tangentKer` is multiplicatively equivalent to
the additive monoid of derivations at the identity
(`derivationMulEquivTangentKer`); in particular the kernel is a commutative group
(the `CommGroup (tangentKer R A B)` instance).

This identifies counit-valued derivations with the first-order infinitesimal kernel.
The additive wrapper of the kernel inherits its natural `B`-module structure through this
identification, and `derivationLinearEquivTangentKer` records the resulting linear equivalence.
No Lie bracket or functoriality in `B` is constructed here — first-order commutativity of the
kernel says nothing about the Lie bracket, which appears at second order.

The synonym `CounitAlgebra` is a fresh scope for the point-induced algebra structure,
as the dictionary requires; it does not install instances on `B` itself, and
`Bialgebra.CounitAlgebra.algEquivSelf` transports back to `B` as an `R`-algebra.
An algebra homomorphism between coefficient algebras transports these synonyms via
`Bialgebra.CounitAlgebra.mapAlgHom`; `Bialgebra.CounitAlgebra.map` records that this
transport is linear for the actions induced by the counit.

## The exterior convolution product

This file *applies* the exterior convolution product `LinearMap.mulTensor` — two
convolution linear maps applied legwise on `A ⊗[R] A` and multiplied in the coefficients
— to counit-valued derivations. The product itself, together with its normalization rules
(zero, addition, scalars) and its multiplicativity for convolution, is defined generically
in `TauCeti/Algebra/Coalgebra/Convolution.lean`. Composing with the multiplication of `A` lands in
this product's image: an algebra-map point satisfies `g ∘ mul = g ⊠ g`
(`AlgHom.toConv_toLinearMap_comp_mul'`), and a counit-valued derivation satisfies the
Leibniz rule `d ∘ mul = 1 ⊠ d + d ⊠ 1` (`Derivation.toConv_coe_comp_mul'`). This
calculus lives here, at the tangent level, because every later structure on the tangent
space — the Lie bracket and the adjoint action alike — is a composition-level
consequence of these three identities.

-/

public section

namespace TauCeti

open TauCeti.Bialgebra _root_.Bialgebra _root_.Coalgebra WithConv

section BialgebraPoint

variable (R A B : Type*) [CommSemiring R] [Semiring A] [Bialgebra R A]
  [Semiring B] [Algebra R B]

/-- Type synonym: `B` as an `A`-algebra through the identity point of the functor of
points — the counit followed by the structure map, which is the convolution unit
whenever `B` is commutative (`toAlgHom_eq_one_ofConv`); at semiring `B` the
convolution monoid does not exist and the composite is its generalization.
Derivations of `A` valued in `Bialgebra.CounitAlgebra R A B` are the tangent vectors
at the identity. -/
-- `@[expose]` is mandated by the compiler for a type synonym carrying instances under
-- the module system ("locally inferred compilation type differs from type that would
-- be inferred in other modules ... may need to be `@[expose]`d"); removing it fails
-- the build. Consumers should still prefer `algEquivSelf` for transport.
@[expose]
def Bialgebra.CounitAlgebra (_R _A : Type*) (B : Type*) : Type _ := B

namespace Bialgebra.CounitAlgebra

instance : Semiring (CounitAlgebra R A B) := inferInstanceAs (Semiring B)

instance : Algebra R (CounitAlgebra R A B) := inferInstanceAs (Algebra R B)

/-- The canonical `R`-algebra identification of the counit-point coefficient algebra
with `B` itself. -/
def algEquivSelf : CounitAlgebra R A B ≃ₐ[R] B := AlgEquiv.refl

omit [Semiring A] [Bialgebra R A] in
@[simp]
lemma algEquivSelf_apply (x : CounitAlgebra R A B) : algEquivSelf R A B x = x := by
  -- A direct `rfl` is rejected by the module system's exported-`rfl` validation (the
  -- synonym's body is involved); the `change` performs the definitional identification
  -- of `CounitAlgebra R A B` with `B` once, explicitly, and the proof term is opaque.
  change (AlgEquiv.refl (R := R) (A₁ := B)) x = x
  simp only [AlgEquiv.coe_refl]
  rfl

omit [Semiring A] [Bialgebra R A] in
@[simp]
lemma algEquivSelf_symm_apply (b : B) : (algEquivSelf R A B).symm b = b := by
  -- Same documented definitional identification as in `algEquivSelf_apply`.
  change (AlgEquiv.refl (R := R) (A₁ := B)).symm b = b
  simp only [AlgEquiv.refl_symm, AlgEquiv.coe_refl]
  rfl

end Bialgebra.CounitAlgebra

section SynonymScalars

variable {R A B : Type*}

namespace Bialgebra.CounitAlgebra

/-- The coefficient synonym is a module over the coefficients, inherited from `B`. -/
instance [Semiring B] : Module B (CounitAlgebra R A B) := inferInstanceAs (Module B B)

/-- Base and coefficient scalars commute on the synonym, inherited from `B`. -/
instance [CommSemiring R] [Semiring B] [Algebra R B] :
    SMulCommClass R B (CounitAlgebra R A B) :=
  inferInstanceAs (SMulCommClass R B B)

/-- Coefficient scalars associate with the synonym's multiplication, inherited from
`B`. -/
instance [Semiring B] : IsScalarTower B (CounitAlgebra R A B) (CounitAlgebra R A B) :=
  inferInstanceAs (IsScalarTower B B B)

end Bialgebra.CounitAlgebra

end SynonymScalars


end BialgebraPoint

section RingTarget

namespace Bialgebra.CounitAlgebra

variable {R A B : Type*}

/-- The counit-point coefficient synonym is a ring whenever `B` is. -/
instance [Ring B] : Ring (CounitAlgebra R A B) := inferInstanceAs (Ring B)

/-- The counit-point coefficient synonym is a commutative ring whenever `B` is. -/
instance [CommRing B] : CommRing (CounitAlgebra R A B) := inferInstanceAs (CommRing B)

end Bialgebra.CounitAlgebra

end RingTarget

section BialgebraPointScalar

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [Semiring B] [Algebra R B]

namespace Bialgebra.CounitAlgebra

noncomputable instance : Algebra A (CounitAlgebra R A B) :=
  ((Algebra.ofId R B).comp (counitAlgHom R A)).toRingHom.toAlgebra' fun a x => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp,
      Function.comp_apply, counitAlgHom_apply, Algebra.ofId_apply]
    exact Algebra.commutes (counit a) x

noncomputable instance : IsScalarTower R A (CounitAlgebra R A B) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    -- `change` performs the definitional unfolding of the synonym's `toAlgebra'`
    -- instance once, explicitly; the goal is then about `B` itself.
    change algebraMap R B r =
      ((Algebra.ofId R B).comp (counitAlgHom R A)) (algebraMap R A r)
    simp

/-- Scalars of the coefficient algebra commute with the bialgebra scalar action, because
the latter multiplies by a central element — the image of the counit in `B`. -/
instance : SMulCommClass B A (CounitAlgebra R A B) where
  smul_comm b a x := by
    -- The bialgebra scalar action multiplies by a central element, so it commutes
    -- with the `B`-action: move the central factor across the product.
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.commutes a (b • x), smul_mul_assoc,
      Algebra.commutes a x]

omit [CommSemiring A] [Bialgebra R A] in
/-- The base `R`-algebra map of the coefficient synonym agrees with that of `B` itself:
the synonym changes only the `A`-algebra structure. -/
@[simp]
lemma algebraMap_base (r : R) :
    algebraMap R (CounitAlgebra R A B) r = algebraMap R B r := rfl

@[simp]
lemma algebraMap_apply (a : A) :
    algebraMap A (CounitAlgebra R A B) a = algebraMap R B (counit a) := by
  -- `change` performs the definitional unfolding of the synonym's `toAlgebra'`
  -- instance once, explicitly; the goal is then about `B` itself.
  change ((Algebra.ofId R B).comp (counitAlgHom R A)) a = _
  simp [Algebra.ofId_apply]

end Bialgebra.CounitAlgebra

end BialgebraPointScalar

section CounitAlgebraMap

namespace Bialgebra.CounitAlgebra

variable {R A B C : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- An algebra homomorphism of coefficients, transported to the counit coefficient
algebras. -/
noncomputable def mapAlgHom (phi : B →ₐ[R] C) :
    CounitAlgebra R A B →ₐ[R] CounitAlgebra R A C :=
  (algEquivSelf R A C).symm.toAlgHom.comp (phi.comp (algEquivSelf R A B).toAlgHom)

omit [CommSemiring A] [Bialgebra R A] in
/-- Transport of counit coefficient algebras acts pointwise by the original
coefficient homomorphism. -/
@[simp]
lemma mapAlgHom_apply (phi : B →ₐ[R] C) (b : CounitAlgebra R A B) :
    mapAlgHom (A := A) phi b = phi b := by
  -- This is the first application theorem for `mapAlgHom`, so there is no
  -- pointwise public lemma to rewrite with yet. Unfolding the composite through
  -- its two public equivalences exposes exactly their application lemmas.
  change (algEquivSelf R A C).symm (phi (algEquivSelf R A B b)) = phi b
  rw [algEquivSelf_apply, algEquivSelf_symm_apply]

omit [CommSemiring A] [Bialgebra R A] in
/-- The identity coefficient homomorphism induces the identity homomorphism of
counit coefficient algebras. -/
@[simp]
lemma mapAlgHom_id :
    mapAlgHom (A := A) (AlgHom.id R B) =
      AlgHom.id R (CounitAlgebra R A B) := by
  ext b
  apply (algEquivSelf R A B).injective
  rw [mapAlgHom_apply]
  -- The two identity homomorphisms have definitionally equal carriers but
  -- distinct exported synonym types. `algEquivSelf_apply` cannot rewrite the
  -- temporarily ill-typed coercion, so cross that boundary explicitly once.
  change (AlgHom.id R B) (algEquivSelf R A B b) = algEquivSelf R A B b
  rw [AlgHom.id_apply]

omit [CommSemiring A] [Bialgebra R A] in
/-- Homomorphisms of counit coefficient algebras preserve composition. -/
@[simp]
lemma mapAlgHom_comp {D : Type*} [Semiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    mapAlgHom (A := A) (psi.comp phi) =
      (mapAlgHom (A := A) psi).comp (mapAlgHom (A := A) phi) := by
  ext b
  apply (algEquivSelf R A D).injective
  rw [mapAlgHom_apply]
  -- As in `mapAlgHom_id`, the synonym boundary prevents further rewriting
  -- even though all remaining maps are exposed by `mapAlgHom_apply`.
  change (psi.comp phi) (algEquivSelf R A B b) =
    psi (phi (algEquivSelf R A B b))
  rw [AlgHom.comp_apply]

/-- An algebra map between coefficient algebras, regarded as a linear map for the
`A`-module structures induced by the counit. -/
noncomputable def map (phi : B →ₐ[R] C) :
    CounitAlgebra R A B →ₗ[A] CounitAlgebra R A C where
  toFun := mapAlgHom (A := A) phi
  map_add' := map_add (mapAlgHom (A := A) phi)
  map_smul' a b := by
    rw [mapAlgHom_apply, mapAlgHom_apply]
    -- Scalar multiplication on each synonym is multiplication by the counit
    -- image. No conversion lemma combines this with a map between two distinct
    -- synonym types, so expose that stable pointwise formula explicitly.
    change phi (algebraMap R B (counit a) * algEquivSelf R A B b) =
      algebraMap R C (counit a) * phi (algEquivSelf R A B b)
    rw [map_mul, phi.commutes]

/-- The linear coefficient map has the same underlying function as the coefficient
algebra map. -/
@[simp]
lemma map_apply (phi : B →ₐ[R] C) (b : CounitAlgebra R A B) :
    map (A := A) phi b = phi b := by
  -- `map` is a structure-valued definition with no generated application theorem;
  -- unfolding its `toFun` field is stable and exposes exactly `mapAlgHom`.
  change mapAlgHom (A := A) phi b = _
  rw [mapAlgHom_apply]

/-- The identity algebra homomorphism induces the identity coefficient map. -/
@[simp]
lemma map_id :
    map (A := A) (AlgHom.id R B) =
      LinearMap.id (R := A) (M := CounitAlgebra R A B) := by
  ext b
  apply (algEquivSelf R A B).injective
  rw [map_apply, LinearMap.id_apply, algEquivSelf_apply]
  -- `map_apply` exposes the public pointwise API, after which only the exported
  -- coefficient synonym prevents `AlgHom.id_apply` from matching directly.
  change (AlgHom.id R B) (algEquivSelf R A B b) = algEquivSelf R A B b
  rw [AlgHom.id_apply]

/-- Coefficient maps preserve composition. -/
@[simp]
lemma map_comp {D : Type*} [Semiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    map (A := A) (psi.comp phi) =
      (map (A := A) psi).comp (map (A := A) phi) := by
  ext b
  apply (algEquivSelf R A D).injective
  rw [map_apply, LinearMap.comp_apply, map_apply, map_apply]
  -- The application lemmas reduce both sides to coefficient homomorphisms; the
  -- remaining conversion only identifies their exported synonym carriers.
  change (psi.comp phi) (algEquivSelf R A B b) =
    psi (phi (algEquivSelf R A B b))
  rw [AlgHom.comp_apply]

end Bialgebra.CounitAlgebra

end CounitAlgebraMap

section CommPointScalar

-- The synonym's carrier is `B`, so this instance is inherited from the coefficient semiring
-- alone; `R` and `A` are phantom parameters here and need no structure.
variable (R A B : Type*) [CommSemiring B]

/-- Coefficient scalars commute with multiplication in the coefficient synonym. -/
instance : SMulCommClass B (Bialgebra.CounitAlgebra R A B) (Bialgebra.CounitAlgebra R A B) :=
  inferInstanceAs (SMulCommClass B B B)

end CommPointScalar

section BialgebraCommTarget

variable (R A B : Type*) [CommSemiring R] [Semiring A] [Bialgebra R A]
  [CommSemiring B] [Algebra R B]

instance : CommSemiring (Bialgebra.CounitAlgebra R A B) :=
  inferInstanceAs (CommSemiring B)

/-- Reduction of dual-number points to their classical part, as a homomorphism of
convolution monoids: postcomposition with the infinitesimal augmentation `B[ε] → B`.
For a Hopf algebra its kernel is the tangent space at the identity. -/
noncomputable def dualNumberReduction :
    WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B)) →*
      WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B) :=
  AlgHom.mapValue (TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A B)
    (Bialgebra.CounitAlgebra R A B))

/-- `dualNumberReduction` is postcomposition with the classical-part projection. -/
theorem dualNumberReduction_def :
    dualNumberReduction R A B =
      AlgHom.mapValue (TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A B)
        (Bialgebra.CounitAlgebra R A B)) := by
  -- `dualNumberReduction` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change AlgHom.mapValue (TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A B)
    (Bialgebra.CounitAlgebra R A B)) = _
  rfl

@[simp]
lemma dualNumberReduction_apply
    (ψ : WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B))) (x : A) :
    (dualNumberReduction R A B ψ).ofConv x =
      TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A B)
        (Bialgebra.CounitAlgebra R A B) (ψ.ofConv x) := by
  simp [dualNumberReduction, AlgHom.mapValue_apply]

end BialgebraCommTarget

section BialgebraCommTargetPoint

variable (R A B : Type*) [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommSemiring B] [Algebra R B]

/-- Where the convolution monoid exists — commutative `B` — the identity point through
which `CounitAlgebra` is built is the convolution unit. -/
lemma Bialgebra.CounitAlgebra.toAlgHom_eq_one_ofConv :
    IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B) =
      (1 : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B)).ofConv := by
  ext a
  exact (Bialgebra.CounitAlgebra.algebraMap_apply R A B a).trans
    (AlgHom.convOne_apply a).symm

end BialgebraCommTargetPoint

/-- Mirror of `Coalgebra.sum_counit_smul`: summing the counit of the right factors
against the left factors of a comultiplication representative recovers the element.
Mathlib has the left identity in both forms (`Coalgebra.sum_counit_smul`, point-free
`Coalgebra.lift_lsmul_comp_counit_comp_comul`, sending `x ⊗ y` to `ε x • y`); this
right identity `∑ ε (a₂) • a₁ = a` exists in neither form there and is derived from
the closest mirror, `Coalgebra.sum_tmul_counit_eq`. -/
private lemma sum_smul_counit {R C : Type*} [CommSemiring R] [AddCommMonoid C]
    [Module R C] [Coalgebra R C] {c : C} {ι : Type*} (𝓡 : Coalgebra.Repr R c ι) :
    ∑ x ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.right x) • 𝓡.left x = c := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.lsmul_apply,
    one_smul] using congr(TensorProduct.lift (LinearMap.lsmul R C).flip
      $(Coalgebra.sum_tmul_counit_eq (R := R) 𝓡))

section Hopf

open TrivSqZeroExt WithConv _root_.Bialgebra Bialgebra.CounitAlgebra

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B]

variable (R A B) in
/-- The tangent subgroup: dual-number points of `A` lying over the identity point, as
the kernel of the reduction inside the convolution group. Over commutative rings this
is the additive group of the tangent space at the identity of the corresponding affine
group scheme; the Lie bracket is second-order data and is not carried by this
subgroup. -/
noncomputable def tangentKer :
    Subgroup (WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B))) :=
  (dualNumberReduction R A B).ker

variable (R A B) in
/-- `tangentKer` is the kernel of the dual-number reduction. -/
theorem tangentKer_def :
    tangentKer R A B =
      ((dualNumberReduction R A B).ker :
        Subgroup (WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B)))) := by
  -- `tangentKer` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ((dualNumberReduction R A B).ker :
    Subgroup (WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B)))) = _
  rfl

/-- The classical part of any tangent-kernel point is the identity point: pointwise, the
first component of its value at `x` is `algebraMap R _ (counit x)`. -/
@[simp]
lemma fst_apply_of_mem_tangentKer
    {ψ : WithConv (A →ₐ[R] DualNumber (CounitAlgebra R A B))}
    (h : ψ ∈ tangentKer R A B) (x : A) :
    fst (R := CounitAlgebra R A B) (ψ.ofConv x) =
      algebraMap R (Bialgebra.CounitAlgebra R A B) (counit x) := by
  rw [tangentKer, MonoidHom.mem_ker] at h
  have := congr($(h).ofConv x)
  simpa [dualNumberReduction_apply, AlgHom.convOne_apply] using this

/-- On kernel elements, convolution multiplication adds infinitesimal components: the
group law of the tangent space is addition of derivations. -/
private lemma snd_convMul_apply
    {ψ₁ ψ₂ : WithConv (A →ₐ[R] DualNumber (CounitAlgebra R A B))}
    (h₁ : ψ₁ ∈ tangentKer R A B)
    (h₂ : ψ₂ ∈ tangentKer R A B) (a : A) :
    snd (R := CounitAlgebra R A B) ((ψ₁ * ψ₂).ofConv a) =
      snd (R := CounitAlgebra R A B) (ψ₁.ofConv a) +
        snd (R := CounitAlgebra R A B) (ψ₂.ofConv a) := by
  classical
  have key : (ψ₁ * ψ₂).ofConv a =
      ∑ i ∈ (ℛ R a).index, ψ₁.ofConv ((ℛ R a).left i) * ψ₂.ofConv ((ℛ R a).right i) :=
    (ℛ R a).convMul_apply (toConv ψ₁.ofConv.toLinearMap) (toConv ψ₂.ofConv.toLinearMap)
  rw [key, snd_sum]
  have expand : ∀ i ∈ (ℛ R a).index,
      snd (R := CounitAlgebra R A B)
          (ψ₁.ofConv ((ℛ R a).left i) * ψ₂.ofConv ((ℛ R a).right i)) =
        counit (R := R) ((ℛ R a).left i) • snd (R := CounitAlgebra R A B)
            (ψ₂.ofConv ((ℛ R a).right i)) +
          counit (R := R) ((ℛ R a).right i) • snd (R := CounitAlgebra R A B)
            (ψ₁.ofConv ((ℛ R a).left i)) := by
    intro i _
    rw [snd_mul, fst_apply_of_mem_tangentKer h₁, fst_apply_of_mem_tangentKer h₂, op_smul_eq_smul,
      algebraMap_smul, algebraMap_smul]
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, add_comm]
  congr 1
  · calc ∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).right i) •
          snd (R := CounitAlgebra R A B) (ψ₁.ofConv ((ℛ R a).left i))
        = snd (R := CounitAlgebra R A B) (ψ₁.ofConv
            (∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).right i) • (ℛ R a).left i)) := by
          simp [map_sum, map_smul, snd_sum, snd_smul]
      _ = _ := by rw [sum_smul_counit]
  · calc ∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).left i) •
          snd (R := CounitAlgebra R A B) (ψ₂.ofConv ((ℛ R a).right i))
        = snd (R := CounitAlgebra R A B) (ψ₂.ofConv
            (∑ i ∈ (ℛ R a).index, counit (R := R) ((ℛ R a).left i) • (ℛ R a).right i)) := by
          simp [map_sum, map_smul, snd_sum, snd_smul]
      _ = _ := by rw [Coalgebra.sum_counit_smul]

private lemma toConv_mem_ker_iff
    {ψ₀ : A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B)} :
    toConv ψ₀ ∈ tangentKer R A B ↔
      (fstHom R _ _).comp ψ₀ =
        IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B) := by
  rw [tangentKer, MonoidHom.mem_ker, toAlgHom_eq_one_ofConv]
  exact ⟨fun h => congrArg ofConv h, fun h => ofConv_injective h⟩

variable (R A B) in
/-- The group of the tangent space at the identity: the kernel of the dual-number
reduction is, additively, the derivations at the identity point. Convolution of
dual-number points over the identity corresponds to addition of derivations. -/
noncomputable def derivationMulEquivTangentKer :
    Multiplicative (Derivation R A (Bialgebra.CounitAlgebra R A B)) ≃*
      tangentKer R A B where
  toFun d := ⟨toConv
      (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B) d.toAdd).1,
    toConv_mem_ker_iff.mpr
      (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B) d.toAdd).2⟩
  invFun ψ := .ofAdd <| (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B)).symm
    ⟨ψ.1.ofConv, toConv_mem_ker_iff.mp ψ.2⟩
  left_inv d :=
    congrArg Multiplicative.ofAdd <|
      (derivationToDualNumberEquivLift R A
        (Bialgebra.CounitAlgebra R A B)).symm_apply_apply d.toAdd
  right_inv ψ := by
    have h := (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B)).apply_symm_apply
      ⟨ψ.1.ofConv, toConv_mem_ker_iff.mp ψ.2⟩
    rw [Subtype.ext_iff] at h
    exact Subtype.ext ((congrArg toConv h).trans (toConv_ofConv ψ.1))
  map_mul' d₁ d₂ := by
    have h₁ := toConv_mem_ker_iff.mpr
      (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B) d₁.toAdd).2
    have h₂ := toConv_mem_ker_iff.mpr
      (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B) d₂.toAdd).2
    have hprod := toConv_mem_ker_iff.mpr
      (derivationToDualNumberEquivLift R A (Bialgebra.CounitAlgebra R A B) (d₁.toAdd + d₂.toAdd)).2
    refine Subtype.ext (ofConv_injective (AlgHom.ext fun a => TrivSqZeroExt.ext ?_ ?_))
    · exact (fst_apply_of_mem_tangentKer hprod a).trans
        (fst_apply_of_mem_tangentKer (mul_mem h₁ h₂) a).symm
    · simp only [MulMemClass.mk_mul_mk]
      rw [snd_convMul_apply h₁ h₂ a]
      simp

variable (R A B) in
/-- Membership in the tangent subgroup: a dual-number point lies in `tangentKer` iff
its classical part is the identity point of the tower. -/
@[simp]
lemma mem_tangentKer_iff {ψ : WithConv (A →ₐ[R] DualNumber (CounitAlgebra R A B))} :
    ψ ∈ tangentKer R A B ↔
      (fstHom R _ _).comp ψ.ofConv =
        IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B) := by
  simpa using toConv_mem_ker_iff (ψ₀ := ψ.ofConv)

/- Not a `simp` lemma: the general `fst_apply_of_mem_tangentKer` (with `SetLike.coe_mem`)
already rewrites this left-hand side. -/
lemma derivationMulEquivTangentKer_apply_fst
    (d : Multiplicative (Derivation R A (Bialgebra.CounitAlgebra R A B))) (a : A) :
    fst (R := CounitAlgebra R A B)
        ((derivationMulEquivTangentKer R A B d).val.ofConv a) =
      algebraMap A (CounitAlgebra R A B) a := by
  simp only [derivationMulEquivTangentKer, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    WithConv.ofConv_toConv, derivationToDualNumberEquivLift_apply_fst]

@[simp]
lemma derivationMulEquivTangentKer_apply_snd
    (d : Multiplicative (Derivation R A (Bialgebra.CounitAlgebra R A B))) (a : A) :
    snd (R := CounitAlgebra R A B)
        ((derivationMulEquivTangentKer R A B d).val.ofConv a) = d.toAdd a := by
  simp [derivationMulEquivTangentKer,
    derivationToDualNumberEquivLift_apply_snd]

@[simp]
lemma derivationMulEquivTangentKer_symm_apply
    (ψ : tangentKer R A B) (a : A) :
    ((derivationMulEquivTangentKer R A B).symm ψ).toAdd a = snd (ψ.val.ofConv a) := by
  simp [derivationMulEquivTangentKer,
    derivationToDualNumberEquivLift_symm_apply]

/-- The tangent subgroup is abelian: first-order infinitesimal points commute, because
multiplication corresponds to addition of derivations under
`derivationMulEquivTangentKer`. -/
noncomputable instance : CommGroup (tangentKer R A B) :=
  { (tangentKer R A B).toGroup with
    mul_comm x y := by
      refine (derivationMulEquivTangentKer R A B).symm.injective ?_
      rw [map_mul, map_mul, mul_comm] }

/-- Counit-valued derivations carry their pointwise `B`-module structure through the
coefficient type synonym. -/
noncomputable instance : Module B
    (Derivation R A (Bialgebra.CounitAlgebra R A B)) := by
  letI : Algebra A B :=
    inferInstanceAs (Algebra A (Bialgebra.CounitAlgebra R A B))
  exact inferInstanceAs (Module B (Derivation R A B))

/-- The natural `B`-module structure on the tangent kernel, written additively and
transported from counit-valued derivations. -/
noncomputable instance : Module B (Additive (tangentKer R A B)) :=
  (AddEquiv.toAdditive_toMultiplicative.symm.trans
    (derivationMulEquivTangentKer R A B).toAdditive).symm.module B

variable (R A B) in
/-- The tangent kernel at the identity is linearly equivalent to the module of derivations
at the counit point. -/
noncomputable def derivationLinearEquivTangentKer :
    Derivation R A (Bialgebra.CounitAlgebra R A B) ≃ₗ[B]
      Additive (tangentKer R A B) :=
  ((AddEquiv.toAdditive_toMultiplicative.symm.trans
    (derivationMulEquivTangentKer R A B).toAdditive).symm.linearEquiv B).symm

/-- Applying `derivationLinearEquivTangentKer` and removing the additive type tag
recovers `derivationMulEquivTangentKer`. -/
@[simp]
lemma derivationLinearEquivTangentKer_apply_toMul
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    (derivationLinearEquivTangentKer R A B d).toMul =
      derivationMulEquivTangentKer R A B (.ofAdd d) := by
  rw [derivationLinearEquivTangentKer, AddEquiv.linearEquiv_symm_apply]
  -- The remaining reduction only removes the generated additive/multiplicative type tags.
  rfl

/-- Applying the inverse of `derivationLinearEquivTangentKer` recovers the derivation
underlying the inverse of `derivationMulEquivTangentKer`. -/
@[simp]
lemma derivationLinearEquivTangentKer_symm_apply_toAdd
    (ψ : Additive (tangentKer R A B)) :
    (derivationLinearEquivTangentKer R A B).symm ψ =
      ((derivationMulEquivTangentKer R A B).symm ψ.toMul).toAdd := by
  rw [derivationLinearEquivTangentKer, LinearEquiv.symm_symm,
    AddEquiv.linearEquiv_apply]
  -- `MulEquiv.toAdditive` has no application lemma, so the final step only removes its
  -- generated additive/multiplicative type tags.
  exact (AddEquiv.symm_trans_apply
    AddEquiv.toAdditive_toMultiplicative.symm
    (derivationMulEquivTangentKer R A B).toAdditive ψ).trans rfl

/-- The second component of the tangent point associated to a derivation is the value
of that derivation. -/
lemma derivationLinearEquivTangentKer_apply_snd
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    snd (R := CounitAlgebra R A B)
        ((derivationLinearEquivTangentKer R A B d).toMul.val.ofConv a) = d a := by
  rw [derivationLinearEquivTangentKer_apply_toMul]
  simpa only [toAdd_ofAdd] using derivationMulEquivTangentKer_apply_snd (.ofAdd d) a

/-- The inverse linear equivalence evaluates a tangent point at `a` by taking its
second component at `a`. -/
lemma derivationLinearEquivTangentKer_symm_apply
    (ψ : Additive (tangentKer R A B)) (a : A) :
    (derivationLinearEquivTangentKer R A B).symm ψ a =
      TrivSqZeroExt.snd (ψ.toMul.val.ofConv a) := by
  rw [derivationLinearEquivTangentKer_symm_apply_toAdd]
  exact derivationMulEquivTangentKer_symm_apply ψ.toMul a

private lemma algEquivSelf_derivation_smul_apply
    (b : B) (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    Bialgebra.CounitAlgebra.algEquivSelf R A B ((b • d) a) =
      b * Bialgebra.CounitAlgebra.algEquivSelf R A B (d a) := by
  -- `CounitAlgebra` deliberately has no `SMul B` instance. The derivation module was
  -- transferred from `B`, so this `rfl` isolates the necessary coefficient-synonym reduction.
  rfl

/-- Scalar multiplication on the additive tangent kernel multiplies its second component,
viewed in `B` through `Bialgebra.CounitAlgebra.algEquivSelf`. -/
@[simp]
lemma tangentKer_smul_apply_snd
    (b : B) (ψ : Additive (tangentKer R A B)) (a : A) :
    snd (R := CounitAlgebra R A B) ((b • ψ).toMul.val.ofConv a) =
      (Bialgebra.CounitAlgebra.algEquivSelf R A B).symm
        (b * Bialgebra.CounitAlgebra.algEquivSelf R A B
          (snd (R := CounitAlgebra R A B) (ψ.toMul.val.ofConv a))) := by
  have h := congrArg (fun d : Derivation R A (Bialgebra.CounitAlgebra R A B) =>
      Bialgebra.CounitAlgebra.algEquivSelf R A B (d a))
    ((derivationLinearEquivTangentKer R A B).symm.map_smul b ψ)
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  calc
    _ = b * Bialgebra.CounitAlgebra.algEquivSelf R A B
          (snd (R := CounitAlgebra R A B) (ψ.toMul.val.ofConv a)) := by
      simpa only [derivationLinearEquivTangentKer_symm_apply,
        algEquivSelf_derivation_smul_apply] using h
    _ = _ := (Bialgebra.CounitAlgebra.algEquivSelf R A B).apply_symm_apply _ |>.symm

end Hopf

section DerivationLeibniz

open WithConv TensorProduct

-- Only `Semiring B` is needed: the statement preserves multiplication order, and the
-- centrality it relies on comes from the `Algebra A (CounitAlgebra R A B)` structure.
-- Commutativity is required later, by `mulTensor_convMul` and the adjoint representation.
variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [Semiring B] [Algebra R B]

namespace Derivation

open TauCeti.LinearMap

/-- The Leibniz rule in convolution form: composing a counit-valued derivation with
the multiplication of `A` is the exterior product against the convolution unit, on
either side. -/
@[simp]
lemma toConv_coe_comp_mul'
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv ((d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ LinearMap.mul' R A) =
      mulTensor 1 (toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) +
        mulTensor (toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) 1 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp only [ofConv_add, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.mul'_apply, mulTensor_apply_tmul,
    Derivation.coeFn_coe, LinearMap.convOne_apply, Bialgebra.CounitAlgebra.algebraMap_base]
  rw [← Bialgebra.CounitAlgebra.algebraMap_apply R A B x,
    ← Bialgebra.CounitAlgebra.algebraMap_apply R A B y, ← Algebra.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def]
  exact d.leibniz x y

end Derivation

end DerivationLeibniz

end TauCeti
