/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.NumberTheory.Cyclotomic.FixedField
public import TauCeti.NumberTheory.Cyclotomic.FixingSubgroup
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum

/-!
# The tagged fixed fields are cyclotomic

`M / K` is Galois with `Gal(M/K)` split by `galEquivProd` as `Gal(L/K) × (ZMod m)ˣ`, the second
factor being the cyclotomic character on the `m`-th roots of unity. A *tag* is a pair `(σ, τ)` in
that product. This file shows that when the tag satisfies `orderOf σ ∣ orderOf τ`, the field fixed
by the cyclic subgroup the tag generates has `M` as an `m`-th cyclotomic extension.

## Main results

* `TauCeti.fixedField_zpowers_isCyclotomicExtension`: for a tag `(σ, τ)` with
  `orderOf σ ∣ orderOf τ`, `M / fixedField ⟪(σ, τ)⟫` is an `m`-th cyclotomic extension.

## References

The result is due to the Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0), at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`. There it is two private declarations in
`CebotarevDensity/Abelian.lean`: `compositum_isCyclotomic_over_fixedField`, which assumes the meet
is trivial, and `zpowers_inf_fixingSubgroup_eq_bot_aux`, which supplies that hypothesis. The source
combines them at their call site rather than stating a single theorem. The hypothesis taken here is
`orderOf σ ∣ orderOf τ`, where the source asks for `Nat.card Gal(L/K) ∣ orderOf τ`.
-/

public section

open IntermediateField IsCyclotomicExtension
open scoped NumberField

namespace TauCeti

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L]
  (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

/-- **The tagged fixed field carries the cyclotomic extension.** For a tag `(σ, τ)` in the
splitting `Gal(M/K) ≃ Gal(L/K) × (ZMod m)ˣ` whose first component's order divides the second's,
`M` is an `m`-th cyclotomic extension of the field fixed by the cyclic subgroup the tag generates.

The divisibility is what makes the tag's cyclic subgroup meet the fixer of `K(μ_m)` trivially,
which is the hypothesis the general criterion needs. -/
theorem fixedField_zpowers_isCyclotomicExtension
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) (τ : (ZMod m)ˣ) (hστ : orderOf σ ∣ orderOf τ) :
    IsCyclotomicExtension {m}
      (fixedField (Subgroup.zpowers ((galEquivProd K L M m hcop hζ).symm (σ, τ)))) M := by
  have : FiniteDimensional L M := finiteDimensional {m} L M
  have : FiniteDimensional K M := FiniteDimensional.trans K L M
  have : IsGalois K M := isGalois_of_isGalois_of_isCyclotomicExtension K L M m
  refine hζ.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot _ ?_
  rw [hζ.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow,
    ker_autToPow_eq_comap_galEquivProd K L M m hcop hζ]
  set e := galEquivProd K L M m hcop hζ
  refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
  rw [Subgroup.map_inf _ _ _ e.injective, MonoidHom.map_zpowers,
    Subgroup.map_comap_eq_self_of_surjective e.surjective, Subgroup.map_bot,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  exact Subgroup.zpowers_inf_top_prod_bot_eq_bot_of_orderOf_dvd σ τ hστ

end TauCeti
