/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# The differential of a Hopf-algebra morphism on tangent spaces

A morphism `φ : A' →ₐc[R] A` of Hopf algebras induces, contravariantly on coordinate
rings and hence covariantly on the corresponding affine group schemes `Spec A → Spec A'`,
a map of tangent groups at the identity — over rings these are the classical tangent
spaces — by precomposition of dual-number points. The
coefficient algebras `Bialgebra.CounitAlgebra R A B` and `Bialgebra.CounitAlgebra R A' B`
share the carrier `B` and its `R`-algebra structure, and the identity points correspond
under `φ` because bialgebra morphisms intertwine counits; so precomposition restricts to
the tangent kernels.

## Main declarations

* `TauCeti.tangentKerMap`: the differential, as a group homomorphism between tangent
  kernels.
* `TauCeti.tangentKerMap_id` and `TauCeti.tangentKerMap_comp`: functoriality.
-/

public section

namespace TauCeti

open Coalgebra WithConv TrivSqZeroExt

section Differential

variable {R A A' B : Type*} [CommSemiring R]
  [CommSemiring A] [HopfAlgebra R A] [CommSemiring A'] [HopfAlgebra R A']
  [CommSemiring B] [Algebra R B]

/-- The differential of a Hopf-algebra morphism on tangent kernels: a morphism
`φ : A' →ₐc[R] A` of Hopf algebras sends a dual-number point of `A` over the identity to
a dual-number point of `A'` over the identity by precomposition. The coefficient
identification `Bialgebra.CounitAlgebra R A B = B = Bialgebra.CounitAlgebra R A' B` is
definitional, and the identity points correspond because `φ` intertwines the counits. -/
noncomputable def tangentKerMap (φ : A' →ₐc[R] A) :
    tangentKer R A B →* tangentKer R A' B :=
  (((AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ).comp
      (tangentKer R A B).subtype).codRestrict (tangentKer R A' B)) fun ψ => by
    have hψ : dualNumberReduction R A B ψ.val = 1 := by
      have h : ψ.val ∈ tangentKer R A B := ψ.2
      generalize hg : ψ.val = v at h ⊢
      rwa [tangentKer_def, MonoidHom.mem_ker] at h
    rw [tangentKer_def, MonoidHom.mem_ker, dualNumberReduction_def]
    -- The reduction of `ψ` at the `A'` coefficient indexing is its `A`-side reduction:
    -- the two counit coefficient algebras share the carrier `B` and its instances.
    have hred : AlgHom.mapValue (TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A' B)
        (Bialgebra.CounitAlgebra R A' B)) ψ.val = dualNumberReduction R A B ψ.val := by
      rw [dualNumberReduction_def]
      rfl
    have hsquare := DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain φ
        (TrivSqZeroExt.fstHom R (Bialgebra.CounitAlgebra R A' B)
          (Bialgebra.CounitAlgebra R A' B))) ψ.val
    -- Naturality of reduction against precomposition, then the `A`-side reduction of
    -- `ψ` is the identity point; composition applications agree definitionally.
    exact hsquare.symm.trans
      ((congrArg (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ)
        (hred.trans hψ)).trans (map_one _))

/-- The differential acts by precomposition on dual-number points. Not a `simp` lemma:
the pointwise form `tangentKerMap_apply_val_ofConv` is the canonical reduction rule, and
tagging both would leave its left-hand side reducible. -/
lemma tangentKerMap_apply_val (φ : A' →ₐc[R] A) (ψ : tangentKer R A B) :
    (tangentKerMap φ ψ).val =
      AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ.val := by
  -- `tangentKerMap` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly: the value of the corestriction is the
  -- value of `mapDomain` on the inclusion.
  change ((AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ).comp
      (tangentKer R A B).subtype) ψ = _
  rfl

/-- The differential acts pointwise by precomposition of dual-number points. -/
@[simp]
lemma tangentKerMap_apply_val_ofConv (φ : A' →ₐc[R] A) (ψ : tangentKer R A B) (a : A') :
    (tangentKerMap φ ψ).val.ofConv a = ψ.val.ofConv ((φ : A' →ₐ[R] A) a) := by
  rw [tangentKerMap_apply_val]
  exact AlgHom.mapDomain_apply_apply φ ψ.val a

/-- The differential of the identity morphism is the identity. -/
@[simp]
lemma tangentKerMap_id :
    tangentKerMap (B := B) (BialgHom.id R A) = MonoidHom.id (tangentKer R A B) := by
  refine MonoidHom.ext fun ψ => Subtype.ext ?_
  rw [tangentKerMap_apply_val, MonoidHom.id_apply,
    AlgHom.mapDomain_id (A := DualNumber (Bialgebra.CounitAlgebra R A B)),
    MonoidHom.id_apply]

/-- `mapDomain` at the two counit coefficient indexings agrees: precomposition does not
touch the coefficients, and the two indexings share the carrier `B` with the same
`inferInstanceAs` instances. Recorded once as an explicit transport lemma, analogous to
`fst_transport`. -/
private lemma mapDomain_transport {A'' : Type*} [CommSemiring A''] [HopfAlgebra R A'']
    (φ : A' →ₐc[R] A)
    (ψ : WithConv (A →ₐ[R] DualNumber (Bialgebra.CounitAlgebra R A B))) :
    AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A'' B)) φ ψ =
      AlgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R A' B)) φ ψ :=
  rfl

/-- The differential of a composite is the composite of the differentials. -/
@[simp]
lemma tangentKerMap_comp {A'' : Type*} [CommSemiring A''] [HopfAlgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A') :
    tangentKerMap (B := B) (φ.comp χ) =
      (tangentKerMap (B := B) χ).comp (tangentKerMap (B := B) φ) := by
  refine MonoidHom.ext fun ψ => Subtype.ext ?_
  rw [MonoidHom.comp_apply, tangentKerMap_apply_val, tangentKerMap_apply_val,
    tangentKerMap_apply_val,
    AlgHom.mapDomain_comp (A := DualNumber (Bialgebra.CounitAlgebra R A'' B)) φ χ,
    ← mapDomain_transport (A'' := A'') φ ψ.val]
  exact MonoidHom.comp_apply _ _ _

end Differential

end TauCeti
