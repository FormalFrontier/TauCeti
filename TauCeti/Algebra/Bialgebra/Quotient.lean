/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The universal property of a bialgebra quotient

For a two-sided ideal `J` of an `R`-bialgebra `H` whose underlying `R`-submodule is a coideal,
Mathlib equips the quotient ring `H ⧸ J` with the structure of an `R`-bialgebra, descending the
comultiplication and counit from `H` (see `Mathlib.RingTheory.Bialgebra.Quotient`). This file
supplies the matching **universal property** that Mathlib lacks: `Bialgebra.Quotient.liftBialgHom`,
the unique bialgebra morphism `H ⧸ J →ₐc[R] K` induced from a bialgebra morphism `H →ₐc[R] K` which
kills `J`.

The construction uses only the bialgebra-quotient structure — a two-sided ideal `J` that is a
coideal — so neither an antipode nor a Hopf-algebra structure is required. For the underlying ideal
of a `TauCeti.HopfIdeal`, use `Bialgebra.Quotient.liftBialgHom I.toIdeal` directly.

## Main definitions

* `Bialgebra.Quotient.liftBialgHom`: the bialgebra morphism `H ⧸ J →ₐc[R] K` induced from a
  bialgebra morphism `f : H →ₐc[R] K` which kills the two-sided coideal `J`, together with its
  computation lemmas (`liftBialgHom_mk`, `liftBialgHom_comp_mkBialgHom`) and its uniqueness
  characterization (`liftBialgHom_unique`).

## References

The construction descends an algebra homomorphism through the algebra quotient
`Ideal.Quotient.liftₐ` and upgrades it to a bialgebra morphism via `BialgHom.ofAlgHom`, on top of
Mathlib's quotient bialgebra machinery (`Mathlib.RingTheory.Bialgebra.Quotient`).
-/

public section

open scoped TensorProduct

namespace Bialgebra.Quotient

/-! ### The universal property of a bialgebra quotient by a two-sided coideal

For a two-sided ideal `J` of an `R`-bialgebra `H` whose underlying `R`-submodule is a coideal,
Mathlib equips `H ⧸ J` with a bialgebra structure (`Mathlib.RingTheory.Bialgebra.Quotient`).
The lift below is the matching universal property: a bialgebra morphism out of `H` that kills `J`
factors uniquely through `H ⧸ J`. Only the bialgebra-quotient structure is used, so neither an
antipode nor a Hopf-algebra structure is required. -/

variable {R H : Type*} [CommRing R] [Ring H] [Bialgebra R H]
variable (J : Ideal H) [J.IsTwoSided]
variable {K : Type*} [Semiring K] [Bialgebra R K]

-- `TensorProduct.map` and `TensorProduct.map_map` are qualified with `_root_` throughout this
-- section: the ambient `Bialgebra` namespace otherwise resolves `TensorProduct.map` to
-- `Bialgebra.TensorProduct.map`, which expects coalgebra rather than linear maps.
omit [J.IsTwoSided] in
private theorem liftBialgHom_kill (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) {h : H} (hh : h ∈ J) :
    (f : H →ₐ[R] K) h = 0 :=
  RingHom.mem_ker.mp (hf hh)

private noncomputable abbrev liftBialgHomAlg (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ J →ₐ[R] K :=
  Ideal.Quotient.liftₐ J (f : H →ₐ[R] K)
    fun _ ha => liftBialgHom_kill J f hf ha

private theorem liftBialgHomAlg_mk (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHomAlg J f hf (Ideal.Quotient.mkₐ R J h) = f h := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp J (f : H →ₐ[R] K)
      fun _ ha => liftBialgHom_kill J f hf ha) h

private theorem liftBialgHomAlg_toLinearMap_comp_mkₐ (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHomAlg J f hf).toLinearMap.comp
      (Ideal.Quotient.mkₐ R J).toLinearMap = f.toLinearMap := by
  ext h
  exact liftBialgHomAlg_mk J f hf h

private theorem liftBialgHomAlg_comul_mk (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    _root_.TensorProduct.map (liftBialgHomAlg J f hf).toLinearMap
        (liftBialgHomAlg J f hf).toLinearMap
        (_root_.TensorProduct.map (Ideal.Quotient.mkₐ R J).toLinearMap
          (Ideal.Quotient.mkₐ R J).toLinearMap (Coalgebra.comul h)) =
      Coalgebra.comul (R := R) (f h) := by
  rw [_root_.TensorProduct.map_map, liftBialgHomAlg_toLinearMap_comp_mkₐ]
  exact CoalgHomClass.map_comp_comul_apply f h

variable [(J.restrictScalars R).IsCoideal]

/-- A bialgebra morphism out of `H` which kills a two-sided coideal `J` factors through the
quotient bialgebra `H ⧸ J`. -/
noncomputable def liftBialgHom (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) : H ⧸ J →ₐc[R] K :=
  BialgHom.ofAlgHom
    (liftBialgHomAlg J f hf)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J q
      rw [AlgHom.comp_apply, liftBialgHomAlg_mk J f hf h, Bialgebra.counitAlgHom_apply,
        Bialgebra.counitAlgHom_apply]
      -- After quotient-surjectivity reduction, `BialgHom.ofAlgHom` leaves the same counit
      -- equality with the two sides presented through different wrapper APIs.
      change Coalgebra.counit (R := R) (f h) =
        Coalgebra.counit (R := R) (Ideal.Quotient.mk J h)
      rw [Bialgebra.Quotient.counit_mk]
      exact CoalgHomClass.counit_comp_apply f h)
    (by
      ext q
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J q
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        liftBialgHomAlg_mk J f hf h, Bialgebra.comulAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        Bialgebra.Quotient.comul_mk]
      exact liftBialgHomAlg_comul_mk J f hf h)

/-- The quotient lift, evaluated on a quotient class. -/
@[simp]
theorem liftBialgHom_mk (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (h : H) :
    liftBialgHom J f hf (Ideal.Quotient.mk J h) = f h := by
  rw [liftBialgHom]
  exact liftBialgHomAlg_mk J f hf h

/-- The quotient lift composed with the quotient map is the original bialgebra morphism. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (liftBialgHom J f hf).comp (Bialgebra.Quotient.mkBialgHom J) = f := by
  ext h
  rw [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply, liftBialgHom_mk]

/-- A bialgebra morphism out of the quotient is determined by its precomposition with the
quotient map. -/
theorem liftBialgHom_unique (f : H →ₐc[R] K)
    (hf : J ≤ RingHom.ker f.toAlgHom.toRingHom) (g : H ⧸ J →ₐc[R] K)
    (hg : g.comp (Bialgebra.Quotient.mkBialgHom J) = f) :
    g = liftBialgHom J f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J q
  calc
    g (Ideal.Quotient.mkₐ R J h)
        = (g.comp (Bialgebra.Quotient.mkBialgHom J)) h := by
          rw [BialgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_apply,
            Ideal.Quotient.mkₐ_eq_mk (R₁ := R)]
    _ = f h := BialgHom.congr_fun hg h
    _ = liftBialgHom J f hf (Ideal.Quotient.mkₐ R J h) :=
      (liftBialgHom_mk J f hf h).symm

end Bialgebra.Quotient
