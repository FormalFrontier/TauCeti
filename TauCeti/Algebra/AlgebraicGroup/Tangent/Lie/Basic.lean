/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The Lie algebra of the tangent space at the identity

Counit-valued derivations of a bialgebra `A` — the tangent vectors at the identity
point (`TauCeti.Bialgebra.CounitAlgebra`) — are closed under the commutator of the
convolution product: for derivations `d₁ d₂` the linear map `d₁ ⋆ d₂ - d₂ ⋆ d₁` is
again a derivation. This equips the tangent space with `LieRing` and `LieAlgebra R`
structures: the Lie algebra of the corresponding affine monoid scheme — of the affine
group scheme, when `A` is a Hopf algebra (ReductiveGroups roadmap, Layer 2,
`Lie(G)`).

The closure proof is composition-level, with no Sweedler-style computation.
Multiplication of the bialgebra is a coalgebra morphism (`Bialgebra.mulCoalgHom`), so
precomposing with it is multiplicative into the convolution algebra on `A ⊗[R] A`
(`LinearMap.convMul_comp_coalgHom_distrib`). There the Leibniz rule for `d` reads
`d ∘ mul = 1 ⊠ d + d ⊠ 1` for the exterior convolution product `⊠` of two factors on
the two tensor legs, and `⊠` is itself multiplicative (`TensorProduct.map_convMul_map`
pushed through `Algebra.TensorProduct.lmul'`). Expanding, the cross terms
`d₁ ⊠ d₂ + d₂ ⊠ d₁` of the two composite products coincide and cancel in the
commutator. Commutativity of `B` matters to closure itself, not only to this route:
over a noncommutative coefficient ring the commutator of counit-valued derivations
need not satisfy the Leibniz rule, the obstruction being the value commutators
`⁅d₁ x, d₂ y⁆`.

## Main declarations

* the `Bracket`, `LieRing`, and `LieAlgebra R` instances on
  `Derivation R A (Bialgebra.CounitAlgebra R A B)`;
* `TauCeti.Derivation.coe_bracket`, `TauCeti.Derivation.bracket_apply`: the bracket
  is the convolution commutator.

No antipode enters: everything is stated over a bialgebra. The ring (rather than
semiring) hypotheses are those of the additive group of derivations in Mathlib
(`Derivation R A M` is an `AddCommGroup` for `CommRing R`, `CommRing A`), which the
commutator needs. This bracket is the convolution commutator; it cannot collide with Mathlib's
composition-commutator `LieRing (Derivation R A A)`, even at `B = A`: the two
carrier types differ in their `Module A` instance argument — the coefficient action
here is through the counit (`a • m = algebraMap R B (counit a) * m`,
`Bialgebra.CounitAlgebra.algebraMap_apply`), not multiplication — so neither
elaboration nor instance search can identify the types, and no diamond exists.
-/

public section

namespace TauCeti

open _root_.Coalgebra WithConv TensorProduct

namespace Derivation

section Bracket

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommRing B] [Algebra R B]

/-- The convolution square of the Leibniz rule: composing a convolution product of two
derivations with the multiplication of `A` expands into exterior products, with the
symmetric cross terms `d₁ ⊠ d₂ + d₂ ⊠ d₁` exposed. -/
private lemma convMul_comp_mul'
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv ((toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv ∘ₗ
          LinearMap.mul' R A) =
      LinearMap.mulTensor 1 (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) +
        LinearMap.mulTensor (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) 1 +
        (LinearMap.mulTensor (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
            (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) +
          LinearMap.mulTensor (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
            (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))) := by
  have h := LinearMap.convMul_comp_coalgHom_distrib
    (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (_root_.Bialgebra.mulCoalgHom R A)
  -- The `toLinearMap` field of `mulCoalgHom` is definitionally `mul'`; the library
  -- states this only for the coercion (`Bialgebra.toLinearMap_mulCoalgHom`), whose
  -- pattern does not match the field projection, so the identification is by `rfl`.
  rw [show (_root_.Bialgebra.mulCoalgHom R A).toLinearMap = LinearMap.mul' R A from rfl,
    ofConv_toConv, ofConv_toConv] at h
  rw [h, toConv_ofConv, toConv_coe_comp_mul', toConv_coe_comp_mul', add_mul, mul_add,
    mul_add, LinearMap.mulTensor_convMul, LinearMap.mulTensor_convMul,
    LinearMap.mulTensor_convMul, LinearMap.mulTensor_convMul]
  simp only [one_mul, mul_one]
  abel

/-- The Leibniz rule for a convolution product of derivations, in scalar-action form:
the value at a product decomposes into the actions of the factors and the symmetric
cross term. -/
private lemma convMul_ofConv_mul (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B))
    (a b : A) :
    (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv (a * b) =
      a • (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv b +
        b • (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv a +
        (d₁ a * d₂ b + d₂ a * d₁ b) := by
  have h := congrArg (fun F => F.ofConv (a ⊗ₜ[R] b)) (convMul_comp_mul' d₁ d₂)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply,
    ofConv_add, LinearMap.add_apply, LinearMap.mulTensor_apply_tmul, LinearMap.convOne_apply,
    Bialgebra.CounitAlgebra.algebraMap_base, Derivation.coeFn_coe] at h
  rw [h, ← Bialgebra.CounitAlgebra.algebraMap_apply R A B a,
    ← Bialgebra.CounitAlgebra.algebraMap_apply R A B b, ← Algebra.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def]

/-- The Lie bracket of tangent vectors at the identity: the commutator of the
convolution product. -/
noncomputable instance instBracket :
    Bracket (Derivation R A (Bialgebra.CounitAlgebra R A B))
      (Derivation R A (Bialgebra.CounitAlgebra R A B)) :=
  ⟨fun d₁ d₂ =>
    Derivation.mk'
      ((toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) -
        toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv)
      fun a b => by
        simp only [ofConv_sub, LinearMap.sub_apply, convMul_ofConv_mul, smul_sub]
        abel⟩

/-- The bracket of counit-valued derivations is the convolution commutator of their
underlying linear maps. -/
@[simp]
theorem coe_bracket (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    ↑⁅d₁, d₂⁆ =
      (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv -
        (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv :=
  (Derivation.coe_mk'_linearMap _ _).trans (ofConv_sub _ _)

/-- The bracket of tangent vectors, valuewise: the difference of the two convolution
products, in convolution normal form. -/
@[simp]
theorem bracket_apply (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    ⁅d₁, d₂⁆ a =
      LinearMap.mul' R (Bialgebra.CounitAlgebra R A B)
          (map (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ↑d₂ (comul a)) -
        LinearMap.mul' R (Bialgebra.CounitAlgebra R A B)
          (map (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ↑d₁ (comul a)) := by
  have h := DFunLike.congr_fun (coe_bracket d₁ d₂) a
  simp only [Derivation.coeFn_coe, LinearMap.sub_apply, LinearMap.convMul_apply] at h
  exact h

private lemma bracket_apply_ofConv
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    ⁅d₁, d₂⁆ a =
      (⁅toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B),
        toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)⁆ :
          WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv a := by
  have h := DFunLike.congr_fun (coe_bracket d₁ d₂) a
  simp only [Derivation.coeFn_coe, LinearMap.sub_apply] at h
  exact h

private lemma toConv_coe_bracket
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv (↑⁅d₁, d₂⁆ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) =
      ⁅toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B),
        toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)⁆ := by
  rw [coe_bracket, toConv_sub, toConv_ofConv, toConv_ofConv,
    LieRing.of_associative_ring_bracket]

end Bracket

section Lie

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Algebra R B]

/-- The tangent space at the identity is a Lie ring under the convolution
commutator. -/
noncomputable instance instLieRing :
    LieRing (Derivation R A (Bialgebra.CounitAlgebra R A B)) where
  add_lie d₁ d₂ d₃ := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [Derivation.add_apply, bracket_apply_ofConv, bracket_apply_ofConv,
      bracket_apply_ofConv, Derivation.coe_add_linearMap, toConv_add]
    exact DFunLike.congr_fun (congrArg ofConv
      (add_lie (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₃ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)))) a
  lie_add d₁ d₂ d₃ := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [Derivation.add_apply, bracket_apply_ofConv, bracket_apply_ofConv,
      bracket_apply_ofConv, Derivation.coe_add_linearMap, toConv_add]
    exact DFunLike.congr_fun (congrArg ofConv
      (lie_add (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₃ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)))) a
  lie_self d := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [bracket_apply_ofConv, Derivation.zero_apply]
    exact (DFunLike.congr_fun (congrArg ofConv
      (lie_self (toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B)))) a).trans
      (by rw [ofConv_zero]; exact LinearMap.zero_apply a)
  leibniz_lie d₁ d₂ d₃ := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [Derivation.add_apply, bracket_apply_ofConv, bracket_apply_ofConv,
      bracket_apply_ofConv, toConv_coe_bracket, toConv_coe_bracket, toConv_coe_bracket]
    exact DFunLike.congr_fun (congrArg ofConv
      (leibniz_lie (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₃ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)))) a

/-- The tangent space at the identity is a Lie algebra over the base ring. -/
noncomputable instance instLieAlgebra :
    LieAlgebra R (Derivation R A (Bialgebra.CounitAlgebra R A B)) where
  lie_smul r d₁ d₂ := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [Derivation.smul_apply, bracket_apply_ofConv, bracket_apply_ofConv,
      Derivation.coe_smul_linearMap, toConv_smul]
    exact DFunLike.congr_fun (congrArg ofConv
      (lie_smul r (toConv (↑d₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑d₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)))) a

/-- The tangent space at the identity is a Lie algebra over the coefficient ring. -/
noncomputable instance instLieAlgebraCoefficients :
    LieAlgebra B (Derivation R A (Bialgebra.CounitAlgebra R A B)) where
  lie_smul b d₁ d₂ := Derivation.ext fun a => by
    let _ : LieRing (WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) :=
      LieRing.ofAssociativeRing
    rw [Derivation.smul_apply, bracket_apply_ofConv, bracket_apply_ofConv,
      Derivation.coe_smul_linearMap, toConv_smul, LieRing.of_associative_ring_bracket,
      mul_smul_comm, smul_mul_assoc, ← smul_sub, ofConv_smul,
      LieRing.of_associative_ring_bracket, LinearMap.smul_apply]

end Lie

end Derivation

end TauCeti
