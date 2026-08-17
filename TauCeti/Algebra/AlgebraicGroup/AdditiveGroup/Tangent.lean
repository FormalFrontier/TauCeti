/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic

/-!
# The tangent Lie algebra of the additive group

The vector group represented by `SymmetricAlgebra R M` has `B`-valued tangent module
`M →ₗ[R] B`. Concretely, a counit-valued derivation is determined by its values on the
generators `SymmetricAlgebra.ι R M x`, and every linear assignment of generator values extends
uniquely to such a derivation. `AdditiveGroup.tangentLinearEquiv` packages this as an `R`-linear
equivalence. Specializing to `M = R` gives
`AdditiveGroup.gaTangentLinearEquiv`, the identification of the tangent module of `𝔾ₐ` with
`B`.

Over commutative rings, the convolution bracket of two tangent derivations is zero. It is enough
to calculate on a generator: the generator is primitive, so both convolution products vanish
there. Thus the tangent Lie algebra of every additive vector group is abelian.

The inverse tangent construction uses the universal property `SymmetricAlgebra.lift` and
`TauCeti.derivationToDualNumberEquivLift`: a linear map `f : M →ₗ[R] B` sends a generator `x`
to the pure infinitesimal dual number `ε f(x)`. No choice of basis or finiteness hypothesis on
`M` is needed.

## Main declarations

* `TauCeti.AdditiveGroup.tangentLinearEquiv`: tangent derivations of a vector group are linear
  maps from its coordinate module.
* `TauCeti.AdditiveGroup.gaTangentLinearEquiv`: the tangent module of `𝔾ₐ` is the coefficient
  algebra `B`.
* `TauCeti.AdditiveGroup.tangent_bracket_eq_zero`: the tangent Lie bracket is zero.

This advances Layer 2 (`Lie(G)`) and the additive-group worked example of the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

namespace AdditiveGroup

open TauCeti.Bialgebra TrivSqZeroExt

universe u v w

section Tangent

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {B : Type w} [CommSemiring B] [Algebra R B]

private noncomputable def infinitesimalGenerator (f : M →ₗ[R] B) :
    M →ₗ[R] DualNumber (CounitAlgebra R (SymmetricAlgebra R M) B) :=
  (inrHom (CounitAlgebra R (SymmetricAlgebra R M) B)
      (CounitAlgebra R (SymmetricAlgebra R M) B)).restrictScalars R ∘ₗ
    (CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B).symm.toLinearMap ∘ₗ f

private lemma infinitesimalGenerator_apply (f : M →ₗ[R] B) (x : M) :
    infinitesimalGenerator f x =
      inr ((CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B).symm (f x)) := by
  rfl

private noncomputable def tangentLift (f : M →ₗ[R] B) :
    {ψ : SymmetricAlgebra R M →ₐ[R] DualNumber (CounitAlgebra R (SymmetricAlgebra R M) B) //
      (fstHom R _ _).comp ψ =
        IsScalarTower.toAlgHom R (SymmetricAlgebra R M)
          (CounitAlgebra R (SymmetricAlgebra R M) B)} := by
  refine ⟨SymmetricAlgebra.lift (infinitesimalGenerator f), ?_⟩
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  -- Expose the two algebra-homomorphism compositions once so their generator values reduce.
  change fst (SymmetricAlgebra.lift (infinitesimalGenerator f)
      (SymmetricAlgebra.ι R M x)) =
    algebraMap (SymmetricAlgebra R M)
      (CounitAlgebra R (SymmetricAlgebra R M) B) (SymmetricAlgebra.ι R M x)
  rw [SymmetricAlgebra.lift_ι_apply, infinitesimalGenerator_apply, fst_inr]
  simp only [CounitAlgebra.algebraMap_apply, SymmetricAlgebra.counit_ι, map_zero]
  rfl

private noncomputable def tangentOfLinear (f : M →ₗ[R] B) :
    Derivation R (SymmetricAlgebra R M)
      (CounitAlgebra R (SymmetricAlgebra R M) B) :=
  (derivationToDualNumberEquivLift R (SymmetricAlgebra R M)
    (CounitAlgebra R (SymmetricAlgebra R M) B)).symm (tangentLift f)

private lemma tangentOfLinear_ι (f : M →ₗ[R] B) (x : M) :
    CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B
        (tangentOfLinear f (SymmetricAlgebra.ι R M x)) = f x := by
  rw [tangentOfLinear, derivationToDualNumberEquivLift_symm_apply, tangentLift,
    SymmetricAlgebra.lift_ι_apply, infinitesimalGenerator_apply, snd_inr,
    AlgEquiv.apply_symm_apply]

/-- Two tangent derivations of a symmetric algebra are equal if they agree on its generators. -/
@[ext]
theorem derivation_ext
    {d e : Derivation R (SymmetricAlgebra R M)
      (CounitAlgebra R (SymmetricAlgebra R M) B)}
    (h : ∀ x, d (SymmetricAlgebra.ι R M x) = e (SymmetricAlgebra.ι R M x)) : d = e := by
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp only [Derivation.map_algebraMap]
  | ι x => exact h x
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The tangent module of the additive vector group represented by `SymmetricAlgebra R M` is
the module `M →ₗ[R] B` of possible generator values.

The equivalence sends a derivation `d` to `x ↦ d (SymmetricAlgebra.ι R M x)`, transported from
the counit coefficient synonym back to `B`. Its inverse sends `f : M →ₗ[R] B` to the unique
derivation taking each generator to `f x`. -/
noncomputable def tangentLinearEquiv :
    Derivation R (SymmetricAlgebra R M)
        (CounitAlgebra R (SymmetricAlgebra R M) B) ≃ₗ[R] (M →ₗ[R] B) where
  toFun d :=
    (CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B).toLinearMap ∘ₗ
      d.toLinearMap ∘ₗ SymmetricAlgebra.ι R M
  invFun := tangentOfLinear
  left_inv d := by
    apply derivation_ext
    intro x
    apply (CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B).injective
    exact tangentOfLinear_ι _ _
  right_inv f := by
    ext x
    exact tangentOfLinear_ι f x
  map_add' d e := by
    ext x
    simp only [LinearMap.comp_apply, Derivation.coe_add_linearMap, LinearMap.add_apply, map_add]
  map_smul' r d := by
    ext x
    simp

/-- The vector-group tangent equivalence evaluates a derivation on the symmetric-algebra
generator. -/
@[simp]
theorem tangentLinearEquiv_apply (d : Derivation R (SymmetricAlgebra R M)
    (CounitAlgebra R (SymmetricAlgebra R M) B)) (x : M) :
    tangentLinearEquiv d x =
      CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B
        (d (SymmetricAlgebra.ι R M x)) :=
  by
    simp only [tangentLinearEquiv]
    rfl

/-- The inverse vector-group tangent equivalence has the prescribed value on every generator. -/
@[simp]
theorem tangentLinearEquiv_symm_apply_ι (f : M →ₗ[R] B) (x : M) :
    (tangentLinearEquiv (R := R) (M := M) (B := B)).symm f
        (SymmetricAlgebra.ι R M x) = f x := by
  simp only [tangentLinearEquiv, LinearEquiv.coe_symm_mk]
  have h := congrArg (CounitAlgebra.algEquivSelf R (SymmetricAlgebra R M) B).symm
    (tangentOfLinear_ι f x)
  simpa only [AlgEquiv.symm_apply_apply, CounitAlgebra.algEquivSelf_symm_apply] using h

/-- The tangent module of the one-dimensional additive group `𝔾ₐ` is the value algebra `B`.

This is the specialization of `tangentLinearEquiv` to the rank-one coordinate module `M = R`;
it sends a derivation to its value on the coordinate `SymmetricAlgebra.ι R R 1`. -/
noncomputable def gaTangentLinearEquiv :
    Derivation R (SymmetricAlgebra R R)
        (CounitAlgebra R (SymmetricAlgebra R R) B) ≃ₗ[R] B :=
  (tangentLinearEquiv (R := R) (M := R) (B := B)).trans
    (LinearMap.ringLmapEquivSelf R R B)

/-- The `𝔾ₐ` tangent equivalence reads a derivation on the coordinate `ι(1)`. -/
@[simp]
theorem gaTangentLinearEquiv_apply
    (d : Derivation R (SymmetricAlgebra R R)
      (CounitAlgebra R (SymmetricAlgebra R R) B)) :
    gaTangentLinearEquiv d =
      CounitAlgebra.algEquivSelf R (SymmetricAlgebra R R) B
        (d (SymmetricAlgebra.ι R R 1)) := by
  simp only [gaTangentLinearEquiv, LinearEquiv.trans_apply,
    LinearMap.ringLmapEquivSelf_apply, tangentLinearEquiv_apply]

/-- A tangent derivation annihilates every power other than the first of a coordinate
generator.

The generator of a vector group is primitive, so its counit vanishes; the Leibniz rule then
leaves the factor `ι(x) ^ (k - 1)`, which acts on the counit coefficient algebra through that
vanishing counit. Only the linear term of a coordinate function survives differentiation at
the identity, which is what makes a differential read off a linear coefficient. -/
theorem tangent_ι_pow_eq_zero
    (d : Derivation R (SymmetricAlgebra R M)
      (CounitAlgebra R (SymmetricAlgebra R M) B)) (x : M) {k : ℕ} (hk : k ≠ 1) :
    d (SymmetricAlgebra.ι R M x ^ k) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero, d.map_one_eq_zero]
  · have hc : Coalgebra.counit (R := R) (SymmetricAlgebra.ι R M x ^ (k - 1)) = 0 := by
      rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply,
        SymmetricAlgebra.counit_ι, zero_pow (by omega)]
    have hz : algebraMap (SymmetricAlgebra R M)
        (CounitAlgebra R (SymmetricAlgebra R M) B)
        (SymmetricAlgebra.ι R M x ^ (k - 1)) = 0 := by
      rw [CounitAlgebra.algebraMap_apply, hc]
      -- The rewritten value sits in `B` rather than in the counit synonym, which carries `B`
      -- itself; the two zeroes are identified definitionally.
      exact map_zero (algebraMap R B)
    have hsmul :
        (SymmetricAlgebra.ι R M x ^ (k - 1)) • d (SymmetricAlgebra.ι R M x) = 0 := by
      rw [Algebra.smul_def, hz, zero_mul]
    rw [d.leibniz_pow, hsmul, smul_zero]

/-- The derivation corresponding to `b : B` under the `𝔾ₐ` tangent equivalence takes the
coordinate `ι(1)` to `b`. -/
@[simp]
theorem gaTangentLinearEquiv_symm_apply_ι (b : B) :
    (gaTangentLinearEquiv (R := R) (B := B)).symm b
        (SymmetricAlgebra.ι R R 1) = b := by
  have h : CounitAlgebra.algEquivSelf R (SymmetricAlgebra R R) B
      ((gaTangentLinearEquiv (R := R) (B := B)).symm b
        (SymmetricAlgebra.ι R R 1)) = b := by
    simpa only [gaTangentLinearEquiv_apply] using
      (gaTangentLinearEquiv (R := R) (B := B)).apply_symm_apply b
  have h' := congrArg (CounitAlgebra.algEquivSelf R (SymmetricAlgebra R R) B).symm h
  simpa only [AlgEquiv.symm_apply_apply, CounitAlgebra.algEquivSelf_symm_apply] using h'

end Tangent

section Lie

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- The convolution Lie bracket on the tangent space of an additive vector group is zero.

Indeed, every symmetric-algebra generator is primitive. Both convolution products of two
counit-valued derivations vanish on primitive elements, and derivations are determined by their
values on the generators. -/
@[simp]
theorem tangent_bracket_eq_zero
    (d e : Derivation R (SymmetricAlgebra R M)
      (CounitAlgebra R (SymmetricAlgebra R M) B)) : ⁅d, e⁆ = 0 := by
  apply derivation_ext
  intro x
  rw [TauCeti.Derivation.bracket_apply, SymmetricAlgebra.comul_ι]
  simp

end Lie

end AdditiveGroup

end TauCeti
