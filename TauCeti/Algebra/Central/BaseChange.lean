/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.Central.TensorProduct` is imported publicly: `Algebra.IsCentral` occurs in every
-- statement below, and the centralizer computation
-- `TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff` that the forward direction runs on
-- lives there.
public import TauCeti.Algebra.Central.TensorProduct
-- Non-public: neither appears in the type of an exported declaration. `Algebra.TensorProduct.comm`
-- is used only inside the proof of the forward direction, and the retraction
-- `LinearMap.exists_leftInverse_of_injective` only inside the proof of the converse.
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change preserves and detects centrality

Let `A` be a central algebra over a field `K` and let `L / K` be a field extension. This file proves
that the scalar extension `L ⊗[K] A` is central *over `L`*, and conversely that centrality of
`L ⊗[K] A` over `L` forces centrality of `A` over `K`.

This is a genuinely different statement from the centrality over `K` proved in
`TauCeti/Algebra/Central/TensorProduct.lean`: that one asks both factors to be central over `K`, and
for a nontrivial extension the factor `L` is not.

The proof is short once the centralizer computation is available. The centre of `L ⊗[K] A` is
contained in the centralizer of `1 ⊗ A`, which is `L ⊗ 1` because `A` is central over `K`; and
`L ⊗ 1` is exactly the image of `L`.

## Main results

* `TauCeti.Algebra.IsCentral.baseChange`: **`L ⊗[K] A` is central over `L`** when `A` is central
  over `K` and `L` is a commutative `K`-algebra free as a `K`-module. It is an instance, so
  together with `TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` instance search sees
  `L ⊗[K] A` as a central simple `L`-algebra with no glue.
* `TauCeti.Algebra.IsCentral.of_baseChange`: the converse over a field `K`, so centrality is not
  merely preserved by base change but **detected** by it.
* `TauCeti.Algebra.isCentral_baseChange_iff`: the two packaged as an equivalence.

Central *simplicity* of a scalar extension, its degree, and the compatibility of base change with
`⊗` and `ᵐᵒᵖ` are assembled from these in `TauCeti/Algebra/CentralSimple/BaseChange.lean`.

## Implementation notes

The forward direction is stated over a commutative semiring `K` and a commutative `K`-algebra `L`
that is free as a `K`-module, the hypotheses the centralizer computation
`TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff` needs; a field extension is the case of
interest and satisfies them. The converse genuinely needs `K` to be a field: it splits off a
`K`-linear retraction `L → K` of the structure map, which is where the vector-space hypothesis
enters, and `L` need only be a nontrivial commutative `K`-algebra.

Both directions are about the `L`-algebra structure on `L ⊗[K] A` coming from the left factor, which
is Mathlib's `Algebra.TensorProduct.leftAlgebra`.

## References

This is part of the **Base change preserves central simplicity, then is a homomorphism** bullet of
Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra.IsCentral

section Forward

variable (K L A : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Module.Free K L]
  [Semiring A] [Algebra K A]

/-- **Base change preserves centrality.** If `A` is a central `K`-algebra and `L` is a commutative
`K`-algebra which is free as a `K`-module, then the scalar extension `L ⊗[K] A` is central over
`L`.

Freeness of `L` and centrality of `A` are both used, through the centralizer computation
`TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff`: an element of `L ⊗[K] A` commuting with
every `1 ⊗ₜ a` is of the form `l ⊗ₜ 1`, that is, a scalar. Centrality of `A` cannot be dropped, and
`ℂ ⊗[ℝ] ℂ` is the standard witness. -/
instance baseChange [Algebra.IsCentral K A] : Algebra.IsCentral L (L ⊗[K] A) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    -- Transport to `A ⊗[K] L`, where the centralizer of `A ⊗ 1` is already computed.
    set e := Algebra.TensorProduct.comm K L A with he
    have h : ∀ a : A, Commute (a ⊗ₜ[K] (1 : L)) (e x) := fun a => by
      have := congrArg e (hx ((1 : L) ⊗ₜ[K] a))
      simpa [Commute, SemiconjBy, he, Algebra.TensorProduct.comm_tmul] using this
    obtain ⟨l, hl⟩ := Algebra.TensorProduct.forall_commute_tmul_one_iff.mp h
    refine Algebra.mem_bot.mpr ⟨l, e.injective ?_⟩
    rw [hl, he]
    simp [Algebra.TensorProduct.algebraMap_apply]

end Forward

section Converse

variable {K L A : Type*} [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- **Base change detects centrality.** Over a field `K`, if the scalar extension `L ⊗[K] A` is
central over a nontrivial commutative `K`-algebra `L`, then `A` was already central over `K`.

The centre of `A` lands in the centre of `L ⊗[K] A` under `a ↦ 1 ⊗ₜ a`, so a central `a` satisfies
`1 ⊗ₜ a = l ⊗ₜ 1` for some `l : L`. Applying `L ⊗[K] A → A` built from a `K`-linear retraction of
`K → L` turns that identity into `a = g l • 1`. -/
theorem of_baseChange [Algebra.IsCentral L (L ⊗[K] A)] : Algebra.IsCentral K A where
  out a ha := by
    rw [Subalgebra.mem_center_iff] at ha
    -- `1 ⊗ₜ a` is central in `L ⊗[K] A`; centrality of the ring does not depend on the base.
    have hcentral : (1 : L) ⊗ₜ[K] a ∈ Subalgebra.center L (L ⊗[K] A) := by
      refine Subalgebra.mem_center_iff.mpr fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul l b => simp [Algebra.TensorProduct.tmul_mul_tmul, ha b]
      | add y z hy hz => simp [add_mul, mul_add, hy, hz]
    obtain ⟨l, hl⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcentral)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply] at hl
    -- A `K`-linear retraction of the structure map `K → L`.
    have hinj : Function.Injective (Algebra.linearMap K L) := fun x y h =>
      (algebraMap K L).injective (by simpa using h)
    -- Splitting an injection asks `L` to be a `K`-vector space, and a module over the field `K` is
    -- a group whether or not it was handed to us as one, so a commutative semiring `L` suffices.
    let : AddCommGroup L := Module.addCommMonoidToAddCommGroup K (M := L)
    obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot (f := Algebra.linearMap K L) |>.mpr hinj)
    have hg1 : g 1 = 1 := by
      simpa using congrArg (fun f : K →ₗ[K] K => f 1) hg
    -- Contract `L ⊗[K] A → K ⊗[K] A → A` along `g`.
    have := congrArg
      (⇑((TensorProduct.lid K A).toLinearMap.comp (TensorProduct.map g LinearMap.id))) hl
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, TensorProduct.lid_tmul, hg1, one_smul] at this
    exact Algebra.mem_bot.mpr ⟨g l, by rw [Algebra.algebraMap_eq_smul_one, this]⟩

end Converse

end Algebra.IsCentral

namespace Algebra

section Iff

variable (K L A : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- **Centrality passes both ways along a scalar extension.** Over a field `K`, an algebra `A` is
central exactly when its scalar extension along a nontrivial commutative `K`-algebra `L` is central
over `L`. Freeness of `L` is automatic here, `K` being a field. -/
@[simp]
theorem isCentral_baseChange_iff :
    Algebra.IsCentral L (L ⊗[K] A) ↔ Algebra.IsCentral K A := by
  -- The forward direction wants `Module.Free K L`, which instance search does not supply for a bare
  -- commutative semiring. Seeing `L` as the additive group it already is makes it a `K`-vector
  -- space, hence free.
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup K (M := L)
  exact ⟨fun _ => Algebra.IsCentral.of_baseChange (K := K) (L := L) (A := A),
    fun _ => Algebra.IsCentral.baseChange K L A⟩

end Iff

end Algebra

end TauCeti
