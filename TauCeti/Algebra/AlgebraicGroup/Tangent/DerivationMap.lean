/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# The differential on derivations

A morphism `φ : A' →ₐc[R] A` of bialgebras sends a counit-valued derivation of `A` to
one of `A'` by precomposition. The construction splits the transport into the two halves
Mathlib provides: restricting the domain along `φ` (`Derivation.compAlgebraMap`, over
local scalar-tower instances for `φ`), and moving the coefficients across the canonical
identification of the two counit coefficient algebras, which is `A'`-linear precisely
because bialgebra morphisms intertwine counits (`LinearEquiv.compDer`). The Leibniz rule
therefore comes from those two facts and is not reproved here.

## Main declarations

* `TauCeti.derivationComp`: precomposition of counit-valued derivations along a
  bialgebra morphism, as an `R`-linear map — the derivation form of the differential.
* `TauCeti.derivationComp_apply`, `TauCeti.derivationComp_id`,
  `TauCeti.derivationComp_comp`: it acts by precomposition, functorially.

The intertwining with the tangent dictionaries is
`TauCeti.tangentKerMap_derivationMulEquivTangentKer` in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Map`.
-/

public section

namespace TauCeti

open _root_.Coalgebra

section DerivationMap

variable {R A A' B : Type*} [CommSemiring R]
  [CommSemiring A] [Bialgebra R A] [CommSemiring A'] [Bialgebra R A']
  [Semiring B] [Algebra R B]

/-- **The two counit coefficient algebras agree, `A'`-linearly.** `Bialgebra.CounitAlgebra R A B`
and `Bialgebra.CounitAlgebra R A' B` are both copies of `B`, and the identification between them is
`A'`-linear exactly because a bialgebra morphism intertwines the counits
(`BialgHom.counitAlgHom_comp`). The `A'`-algebra structure on the `A`-side copy is not the global
one, so it is taken as an instance argument together with `hmap`, which says its structure map
factors through `φ` — the only property of it this construction uses. -/
private noncomputable def counitAlgebraCongr (φ : A' →ₐc[R] A)
    [Algebra A' (Bialgebra.CounitAlgebra R A B)]
    (hmap : ∀ a : A', algebraMap A' (Bialgebra.CounitAlgebra R A B) a =
      algebraMap A (Bialgebra.CounitAlgebra R A B) ((φ : A' →ₐ[R] A) a)) :
    Bialgebra.CounitAlgebra R A B ≃ₐ[A'] Bialgebra.CounitAlgebra R A' B :=
  AlgEquiv.ofRingEquiv
    (f := (Bialgebra.CounitAlgebra.algEquivSelf R A B).toRingEquiv.trans
      (Bialgebra.CounitAlgebra.algEquivSelf R A' B).symm.toRingEquiv) (by
    intro a
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      Bialgebra.CounitAlgebra.algEquivSelf_apply]
    rw [hmap a, Bialgebra.CounitAlgebra.algebraMap_apply R A B,
      Bialgebra.CounitAlgebra.algebraMap_apply R A' B,
      Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R A' B]
    exact congrArg (algebraMap R B)
      (DFunLike.congr_fun (BialgHom.counitAlgHom_comp φ) a))


/-- Implementation of the bundled `derivationComp`, which is the API. -/
private noncomputable def derivationCompAux (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    Derivation R A' (Bialgebra.CounitAlgebra R A' B) := by
  letI : Algebra A' A := (φ : A' →ₐ[R] A).toAlgebra
  letI : IsScalarTower R A' A := IsScalarTower.of_algHom (φ : A' →ₐ[R] A)
  let ρ : A' →ₐ[R] Bialgebra.CounitAlgebra R A B :=
    (IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B)).comp (φ : A' →ₐ[R] A)
  letI : Algebra A' (Bialgebra.CounitAlgebra R A B) := ρ.toRingHom.toAlgebra'
    (fun a x => by
      -- The centrality obligation of `toAlgebra'` arrives phrased through `RingHom`
      -- coercions of `ρ`; no rewrite lemma applies to that shape, since it is
      -- definitional to this construction, so `change` restates it once.
      change ρ a * x = x * ρ a
      rw [show ρ a = algebraMap R (Bialgebra.CounitAlgebra R A B)
          (counit (R := R) ((φ : A' →ₐ[R] A) a)) from by
        simp [ρ, IsScalarTower.coe_toAlgHom',
          Bialgebra.CounitAlgebra.algebraMap_apply R A B]
        -- The residual is the definitional identification of the coefficient synonym
        -- with `B` itself, which `simp` exposes but no lemma states.
        rfl]
      exact Algebra.commutes _ x)
  letI : IsScalarTower R A' (Bialgebra.CounitAlgebra R A B) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      -- The goal is stated through the `letI` algebra structure just installed, whose
      -- `algebraMap` is definitionally `ρ`; no global lemma can name a local
      -- instance, so `change` performs that definitional unfolding once.
      change algebraMap R (Bialgebra.CounitAlgebra R A B) r = ρ (algebraMap R A' r)
      -- `ρ` is a `let`-bound composite, so its value at `algebraMap R A' r` has no
      -- equation lemma; the `show … from` states the one unfolding-and-`commutes`
      -- step explicitly.
      rw [show ρ (algebraMap R A' r) =
          (IsScalarTower.toAlgHom R A (Bialgebra.CounitAlgebra R A B))
            (algebraMap R A r) from by
          simp [ρ, AlgHomClass.commutes, -Bialgebra.CounitAlgebra.algebraMap_base],
        IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]
  letI : IsScalarTower A' A (Bialgebra.CounitAlgebra R A B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- The `A'`-algebra structure just installed sends `a` to `ρ a = algebraMap A _ (φ a)`,
  -- which is definitional, so `hmap` is discharged by `rfl`.
  exact (counitAlgebraCongr φ (B := B) (fun _ => rfl)).toLinearEquiv.compDer
    (d.compAlgebraMap A')

private lemma derivationCompAux_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A') :
    derivationCompAux (B := B) φ d a = d ((φ : A' →ₐ[R] A) a) := by
  -- `counitAlgebraCongr` is unfolded rather than applied through an `_apply` lemma. Its `hmap`
  -- argument is supplied here as `fun _ => rfl`, elaborated under the `letI` algebra instance of
  -- `derivationCompAux`, in which the two sides of `hmap` are the *same* term; the stored proof
  -- therefore carries a reflexivity type. An `_apply` lemma, whose `hmap` has the general
  -- non-reflexive type, does not match this occurrence, and `rw`/`simp only` find no pattern.
  simp only [derivationCompAux, counitAlgebraCongr, Derivation.linearEquiv_coe_comp,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, Bialgebra.CounitAlgebra.algEquivSelf_apply]
  -- The remaining transport erases at this value, and the precomposition is
  -- definitional in Mathlib's `compAlgebraMap`.
  exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R A' B _).trans rfl

/-- Precomposition of counit-valued derivations along a bialgebra morphism, as an
`R`-linear map: the derivation form of the differential, sending an `R`-derivation
`d : A → B` at the identity point of `A` to `a ↦ d (φ a)` at the identity point of
`A'`.

(The commutativity hypotheses on `A` and `A'` are those of `Derivation` itself.) -/
noncomputable def derivationComp (φ : A' →ₐc[R] A) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ[R]
      Derivation R A' (Bialgebra.CounitAlgebra R A' B) where
  toFun := derivationCompAux φ
  -- After simplification both sides are the same value of `B`; the residual is the
  -- definitional identification of the two coefficient indexings.
  map_add' d₁ d₂ := by ext a; simp [derivationCompAux_apply]; rfl
  map_smul' r d := by ext a; simp [derivationCompAux_apply]; rfl

/-- The differential acts on derivations by precomposition. -/
@[simp]
lemma derivationComp_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A') :
    derivationComp (B := B) φ d a = d ((φ : A' →ₐ[R] A) a) := by
  -- `derivationComp` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change derivationCompAux (B := B) φ d a = _
  rw [derivationCompAux_apply]

/-- Precomposition along the identity is the identity map. -/
@[simp]
theorem derivationComp_id :
    derivationComp (B := B) (BialgHom.id R A) =
      LinearMap.id (R := R) (M := Derivation R A (Bialgebra.CounitAlgebra R A B)) := by
  ext d a
  simp

/-- Precomposition along a composite is the composition of the precompositions. -/
@[simp]
theorem derivationComp_comp {A'' : Type*} [CommSemiring A''] [Bialgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A') :
    derivationComp (B := B) (φ.comp χ) =
      (derivationComp (B := B) χ).comp (derivationComp (B := B) φ) := by
  ext d a
  simp
  -- The residual is the definitional identification of the coefficient indexings.
  rfl

end DerivationMap

end TauCeti
