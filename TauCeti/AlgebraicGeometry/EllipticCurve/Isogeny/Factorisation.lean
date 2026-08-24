/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# The factorisation of an isogeny

The pointedness criterion in `Isogeny/InfinityPlace.lean` discharges the pointedness of a factor.
If two isogenies `φ : W₁ → W₂` and
`ψ : W₁ → W₃` satisfy `ψ^*F(W₃) ⊆ φ^*F(W₂)` as subfields of `F(W₁)`, then inverting `φ^*` on its
image gives an embedding `σ : F(W₃) → F(W₂)` with `φ^* ∘ σ = ψ^*`. Restricting the place at
infinity of `W₁` along `φ^*` and `ψ^*` gives the places at infinity of `W₂` and `W₃`, so
restricting along `σ` carries the one to the other; the criterion then makes `σ` an isogeny
`λ : W₂ → W₃`, and `λ ∘ φ = ψ`. Uniqueness is `TauCeti.Isogeny.comp_right_injective`, and the
degree formula `deg ψ = deg λ · deg φ` is the tower formula `TauCeti.Isogeny.degree_comp`.

The criterion is stated on subfields, not on kernels: over `ℚ` a curve with no rational
`2`-torsion has `ker [2](ℚ) = ker (id)(ℚ) = {O}` while `id` does not factor through `[2]`, and
relative Frobenius has trivial geometric point kernel while `id` does not factor through it. Both
are correctly excluded here, the subfield containment failing in each case.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_iff_fieldRange_le`: **the factorisation theorem**, that
  `ψ` factors through `φ` by a unique isogeny exactly when `ψ^*F(W₃) ⊆ φ^*F(W₂)`.
* `TauCeti.Isogeny.exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one`: **a degree-one isogeny is
  an isomorphism**, the first consequence of the factorisation theorem.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, "The factorisation theorem — made a
milestone in its own right, because it is what the dual is built from": for isogenies
`φ : W₁ → W₂` and `ψ : W₁ → W₃`, `ψ` factors as `ψ = λ ∘ φ` for a unique isogeny `λ` iff
`ψ^*K(W₃) ⊆ φ^*K(W₂)` as subfields of `K(W₁)`, with `deg ψ = deg φ · deg λ`. The same layer's
dual-isogeny bullet asks for the route taken here — "an **unpointed induced-place map** for
finite function-field embeddings, with the named criterion `MapsInfinity λ ↔ λ_*(O₂) = O₃`
(equivalently its valuation/integral-closure form), and functoriality of induced places along
`λ ∘ φ = ψ`".

## Provenance

Not ported. Silverman's III.4.11 is stated for separable isogenies and proved by Galois theory of
the function-field extension; the subfield criterion here subsumes it and needs no separability,
and the pointedness of the factor — which the classical account does not have to address, its
morphisms being maps of projective curves — is discharged by the place criterion above.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.4, III.4.11.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.1.13.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

namespace Isogeny

/-- **The factorisation theorem** (Silverman, *The Arithmetic of Elliptic Curves*, III.4.11 in its
separable form): an isogeny `ψ : W₁ → W₃` factors through an isogeny `φ : W₁ → W₂`, by a unique
isogeny `λ : W₂ → W₃`, exactly when the function field `ψ` pulls back sits inside the one `φ`
pulls back.

The criterion is on subfields of `F(W₁)`, not on kernels of point maps, and that is what makes it
correct in general: over `ℚ`, a curve with no rational `2`-torsion has `ker [2](ℚ) = {O}` without
the identity factoring through `[2]`, and relative Frobenius has trivial *geometric* point kernel
without the identity factoring through it. In both cases the subfield containment fails, as it
should. -/
theorem existsUnique_comp_eq_iff_fieldRange_le (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃) :
    (∃! χ : Isogeny W₂ W₃, χ.comp φ = ψ) ↔
      ψ.fieldPullback.fieldRange ≤ φ.fieldPullback.fieldRange := by
  constructor
  · rintro ⟨χ, rfl, -⟩
    rintro z ⟨w, rfl⟩
    exact ⟨χ.fieldPullback w, by simp⟩
  · intro hle
    -- Invert `φ^*` on its image to get `σ : F(W₃) → F(W₂)` with `φ^* ∘ σ = ψ^*`.
    set σ : W₃.FunctionField →ₐ[F] W₂.FunctionField :=
      (AlgEquiv.ofInjectiveField φ.fieldPullback).symm.toAlgHom.comp
        (ψ.fieldPullback.codRestrict φ.fieldPullback.fieldRange.toSubalgebra
          fun z ↦ hle ⟨z, rfl⟩)
    have hcomp : ∀ z, φ.fieldPullback (σ z) = ψ.fieldPullback z := fun z ↦ by
      have := (AlgEquiv.ofInjectiveField φ.fieldPullback).apply_symm_apply
        ⟨ψ.fieldPullback z, hle ⟨z, rfl⟩⟩
      exact congrArg Subtype.val this
    -- The place at infinity restricts along `σ` to the place at infinity, by functoriality.
    have hplace : ((infinityPlace W₂).comap σ.toRingHom).IsEquiv (infinityPlace W₃) := by
      refine Valuation.IsEquiv.trans (Valuation.IsEquiv.comap σ.toRingHom
        (Isogeny.isEquiv_comap_infinityPlace φ).symm) ?_
      have : ((infinityPlace W₁).comap φ.fieldPullback.toRingHom).comap σ.toRingHom
          = (infinityPlace W₁).comap ψ.fieldPullback.toRingHom := by
        ext z
        exact congrArg (infinityPlace W₁) (hcomp z)
      exact this ▸ Isogeny.isEquiv_comap_infinityPlace ψ
    -- The criterion packages `σ` as an isogeny, and it is a factor of `ψ` by construction.
    set χ : Isogeny W₂ W₃ :=
      ⟨σ.comp (IsScalarTower.toAlgHom F W₃.CoordinateRing W₃.FunctionField),
        (CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace σ).2 hplace⟩
    have hfactor : χ.comp φ = ψ := by
      refine Isogeny.ext (AlgHom.ext fun c ↦ ?_)
      rw [comp_pullback]
      exact (hcomp _).trans (fieldPullback_algebraMap ψ c)
    exact ⟨χ, hfactor, fun _ h ↦ comp_right_injective φ (h.trans hfactor.symm)⟩

/-- **An isogeny of degree one is an isomorphism** (Silverman, *The Arithmetic of Elliptic
Curves*, II.2.4.1): it has an isogeny which is both a left and a right inverse. -/
theorem exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one
    (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1) :
    ∃ χ : Isogeny W₂ W₁, χ.comp φ = id W₁ ∧ φ.comp χ = id W₂ := by
  have htop : φ.fieldPullback.fieldRange = ⊤ :=
    AlgHom.fieldRange_eq_top.2 ((degree_eq_one_iff φ).1 hφ)
  obtain ⟨χ, hχ, -⟩ :=
    (existsUnique_comp_eq_iff_fieldRange_le φ (id W₁)).2 (htop ▸ le_top)
  refine ⟨χ, hχ, comp_right_injective φ ?_⟩
  simp [comp_assoc, hχ]

end Isogeny

end TauCeti

end
