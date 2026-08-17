/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Hopf ideals

This file defines Hopf ideals in a Hopf algebra over a commutative semiring. A Hopf ideal is
an ideal `I` whose comultiplication lands in `I ⊗ H + H ⊗ I`, whose counit vanishes on `I`,
and which is stable under the antipode.

This is a small Layer 3 prerequisite for the reductive-groups roadmap target
"Hopf ideals ↔ closed subgroup schemes": closed subgroup schemes of an affine group scheme
are represented on coordinate rings by quotient Hopf algebras, and the ideal being quotiented
must satisfy exactly these Hopf-ideal closure conditions.

## Main definitions

* `TauCeti.HopfIdeal`: a Hopf ideal in a Hopf algebra over a commutative semiring.
* `TauCeti.HopfIdeal.leftTensorIdeal` and `TauCeti.HopfIdeal.rightTensorIdeal`: the two
  summands `I ⊗ H` and `H ⊗ I` inside `H ⊗ H`.
* `⊥ : HopfIdeal R H`: the zero Hopf ideal.
* `I ⊔ J : HopfIdeal R H`: the sum of two Hopf ideals.
* `sSup S : HopfIdeal R H` and `⨆ i, I i : HopfIdeal R H`: arbitrary suprema of Hopf ideals,
  with underlying ideal the supremum of the underlying ideals.
* `TauCeti.HopfIdeal.instIsCoideal`, `TauCeti.HopfIdeal.instIsHopfIdeal`: over a commutative
  ring, the bridge instances exhibiting `I.toIdeal` as a coideal and a Hopf ideal in Mathlib's
  sense, so that Mathlib's quotient coalgebra/bialgebra/Hopf instances fire on `H ⧸ I.toIdeal`.

## References

This follows the standard Hopf-algebra definition of a Hopf ideal; see Sweedler,
*Hopf Algebras*, Chapter 1. The formalization uses Mathlib's Hopf-algebra and tensor-product
ideal API. The arbitrary-supremum lattice construction follows the local pattern from
`TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice` and
`TauCeti.Algebra.Coalgebra.Subcomodule.Lattice`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

section TensorIdeals

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [Algebra R H]

namespace HopfIdeal

/-- The image of an ideal `I ≤ H` under the left inclusion `H → H ⊗[R] H`, representing
`I ⊗ H` inside the tensor product algebra. -/
@[expose] def leftTensorIdeal (I : Ideal H) : Ideal (H ⊗[R] H) :=
  Ideal.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom I

/-- The image of an ideal `I ≤ H` under the right inclusion `H → H ⊗[R] H`, representing
`H ⊗ I` inside the tensor product algebra. -/
@[expose] def rightTensorIdeal (I : Ideal H) : Ideal (H ⊗[R] H) :=
  Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I

theorem leftTensorIdeal_def (I : Ideal H) :
    leftTensorIdeal (R := R) (H := H) I =
      Ideal.map
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        I :=
  rfl

theorem rightTensorIdeal_def (I : Ideal H) :
    rightTensorIdeal (R := R) (H := H) I =
      Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I :=
  rfl

/-- The left tensor inclusion sends elements of `I` into `I ⊗ H`. -/
theorem includeLeft_mem_leftTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) :
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x ∈
      leftTensorIdeal (R := R) (H := H) I :=
  Ideal.mem_map_of_mem _ hx

/-- The right tensor inclusion sends elements of `I` into `H ⊗ I`. -/
theorem includeRight_mem_rightTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) :
    Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) x ∈
      rightTensorIdeal (R := R) (H := H) I :=
  Ideal.mem_map_of_mem _ hx

/-- A pure tensor `x ⊗ₜ y` with `x ∈ I` lies in `I ⊗ H`. -/
theorem tmul_mem_leftTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) (y : H) :
    x ⊗ₜ[R] y ∈ leftTensorIdeal (R := R) (H := H) I := by
  have h : x ⊗ₜ[R] y =
      Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) y *
        Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x := by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Ideal.mul_mem_left _ _ (includeLeft_mem_leftTensorIdeal (R := R) (H := H) hx)

/-- A pure tensor `x ⊗ₜ y` with `y ∈ I` lies in `H ⊗ I`. -/
theorem tmul_mem_rightTensorIdeal {I : Ideal H} (x : H) {y : H} (hy : y ∈ I) :
    x ⊗ₜ[R] y ∈ rightTensorIdeal (R := R) (H := H) I := by
  have h : x ⊗ₜ[R] y =
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x *
        Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) y := by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Ideal.mul_mem_left _ _ (includeRight_mem_rightTensorIdeal (R := R) (H := H) hy)

theorem mem_leftTensorIdeal {I : Ideal H} {x : H ⊗[R] H} :
    x ∈ leftTensorIdeal (R := R) (H := H) I ↔
      x ∈ Ideal.map
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        I :=
  Iff.rfl

theorem mem_rightTensorIdeal {I : Ideal H} {x : H ⊗[R] H} :
    x ∈ rightTensorIdeal (R := R) (H := H) I ↔
      x ∈ Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I :=
  Iff.rfl

/-- The order universal property for `I ⊗ H`. -/
theorem leftTensorIdeal_le_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    leftTensorIdeal (R := R) (H := H) I ≤ J ↔
      I ≤ Ideal.comap
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        J :=
  Ideal.map_le_iff_le_comap

/-- The order universal property for `H ⊗ I`. -/
theorem rightTensorIdeal_le_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    rightTensorIdeal (R := R) (H := H) I ≤ J ↔
      I ≤ Ideal.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom J :=
  Ideal.map_le_iff_le_comap

/-- The construction `I ↦ I ⊗ H` is monotone. -/
theorem leftTensorIdeal_mono {I J : Ideal H} (hIJ : I ≤ J) :
    leftTensorIdeal (R := R) (H := H) I ≤ leftTensorIdeal (R := R) (H := H) J :=
  Ideal.map_mono hIJ

/-- The construction `I ↦ H ⊗ I` is monotone. -/
theorem rightTensorIdeal_mono {I J : Ideal H} (hIJ : I ≤ J) :
    rightTensorIdeal (R := R) (H := H) I ≤ rightTensorIdeal (R := R) (H := H) J :=
  Ideal.map_mono hIJ

/-- The construction `I ↦ I ⊗ H` distributes over arbitrary suprema of ideals. -/
@[simp]
theorem leftTensorIdeal_iSup {ι : Sort*} (I : ι → Ideal H) :
    leftTensorIdeal (R := R) (H := H) (⨆ i, I i) =
      ⨆ i, leftTensorIdeal (R := R) (H := H) (I i) :=
  Ideal.map_iSup
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom I

/-- The construction `I ↦ H ⊗ I` distributes over arbitrary suprema of ideals. -/
@[simp]
theorem rightTensorIdeal_iSup {ι : Sort*} (I : ι → Ideal H) :
    rightTensorIdeal (R := R) (H := H) (⨆ i, I i) =
      ⨆ i, rightTensorIdeal (R := R) (H := H) (I i) :=
  Ideal.map_iSup
    (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I

/-- The construction `I ↦ I ⊗ H` distributes over joins of ideals. -/
@[simp]
theorem leftTensorIdeal_sup (I J : Ideal H) :
    leftTensorIdeal (R := R) (H := H) (I ⊔ J) =
      leftTensorIdeal (R := R) (H := H) I ⊔ leftTensorIdeal (R := R) (H := H) J :=
  Ideal.map_sup
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom I J

/-- The construction `I ↦ H ⊗ I` distributes over joins of ideals. -/
@[simp]
theorem rightTensorIdeal_sup (I J : Ideal H) :
    rightTensorIdeal (R := R) (H := H) (I ⊔ J) =
      rightTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) J :=
  Ideal.map_sup
    (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I J

/-- TauCeti's `leftTensorIdeal I` (`I ⊗ H`), viewed as an `R`-submodule, is the range of
`rTensor H (I.restrictScalars R).subtype`. This is Mathlib's `Ideal.map_includeLeft_eq`. -/
private theorem leftTensorIdeal_restrictScalars_eq_range (I : Ideal H) :
    (leftTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.rTensor H (I.restrictScalars R).subtype) :=
  Ideal.map_includeLeft_eq (R := R) (A := H) (B := H) I

/-- TauCeti's `rightTensorIdeal I` (`H ⊗ I`), viewed as an `R`-submodule, is the range of
`lTensor H (I.restrictScalars R).subtype`. This is Mathlib's `Ideal.map_includeRight_eq`. -/
private theorem rightTensorIdeal_restrictScalars_eq_range (I : Ideal H) :
    (rightTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.lTensor H (I.restrictScalars R).subtype) :=
  Ideal.map_includeRight_eq (R := R) (A := H) (B := H) I

/-- The bridge to Mathlib's coideal target: TauCeti's `I ⊗ H + H ⊗ I` (a sup of ideals of
`H ⊗[R] H`), viewed as an `R`-submodule, equals `range (lTensor …) ⊔ range (rTensor …)`. -/
private theorem comul_mem_sup_restrictScalars_eq_range (I : Ideal H) :
    (leftTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) I).restrictScalars R =
      LinearMap.range (LinearMap.lTensor H (I.restrictScalars R).subtype) ⊔
        LinearMap.range (LinearMap.rTensor H (I.restrictScalars R).subtype) := by
  rw [Submodule.restrictScalars_sup, leftTensorIdeal_restrictScalars_eq_range,
    rightTensorIdeal_restrictScalars_eq_range, sup_comm]

end HopfIdeal

end TensorIdeals

section TensorIdealQuotient

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [Algebra R H]

namespace HopfIdeal

/-- The kernel of tensoring the quotient map on the right is the right tensor ideal. -/
theorem ker_tensorProduct_map_id_quotient (I : Ideal H) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I)) =
      rightTensorIdeal (R := R) (H := H) I := by
  rw [Algebra.TensorProduct.lTensor_ker (A := H) (Ideal.Quotient.mkₐ R I)
    (Ideal.Quotient.mkₐ_surjective R I)]
  rw [← RingHom.ker_coe_toRingHom (Ideal.Quotient.mkₐ R I),
    Ideal.Quotient.mkₐ_ker R I]
  -- `lTensor_ker` uses the algebra-hom coercion for `includeRight`, while
  -- `rightTensorIdeal` uses its `toRingHom`; after unfolding they are definitionally equal.
  rw [rightTensorIdeal_def]
  rfl

end HopfIdeal

end TensorIdealQuotient

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- A Hopf ideal in a Hopf algebra over a commutative semiring.

The comultiplication condition is stated in the ambient tensor product algebra as
`Δ(I) ⊆ I ⊗ H + H ⊗ I`. Over a commutative ring, the bridge instances
`HopfIdeal.instIsCoideal` and `HopfIdeal.instIsHopfIdeal` below let Mathlib endow the
quotient `H ⧸ I.toIdeal` with its Hopf-algebra structure. -/
structure HopfIdeal where
  /-- The underlying ideal. -/
  carrier : Ideal H
  /-- The underlying ideal is two-sided. -/
  isTwoSided' : carrier.IsTwoSided
  /-- The comultiplication of an element of the ideal lies in `I ⊗ H + H ⊗ I`. -/
  comul_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier →
      Coalgebra.comul (R := R) x ∈
        HopfIdeal.leftTensorIdeal (R := R) (H := H) carrier ⊔
          HopfIdeal.rightTensorIdeal (R := R) (H := H) carrier
  /-- The counit vanishes on the ideal. -/
  counit_eq_zero' : ∀ ⦃x : H⦄, x ∈ carrier → Coalgebra.counit (R := R) x = 0
  /-- The antipode preserves the ideal. -/
  antipode_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier → HopfAlgebra.antipode R x ∈ carrier

namespace HopfIdeal

variable {R H}

instance : SetLike (HopfIdeal R H) H where
  coe I := I.carrier
  coe_injective I J h := by
    cases I with
    | mk carrier htwo hcomul hcounit hantipode =>
    cases J with
    | mk carrier' htwo' hcomul' hcounit' hantipode' =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (HopfIdeal R H) H where
  add_mem {I} := I.carrier.add_mem
  zero_mem I := I.carrier.zero_mem

instance : SMulMemClass (HopfIdeal R H) H H where
  smul_mem {I} h {_} hx := I.carrier.mul_mem_left h hx

instance : PartialOrder (HopfIdeal R H) :=
  .ofSetLike (HopfIdeal R H) H

/-- The underlying ideal of a Hopf ideal. -/
@[expose] def toIdeal (I : HopfIdeal R H) : Ideal H :=
  I.carrier

instance (I : HopfIdeal R H) : I.toIdeal.IsTwoSided :=
  I.isTwoSided'

@[simp]
theorem mem_carrier {I : HopfIdeal R H} {x : H} : x ∈ I.carrier ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem mem_toIdeal {I : HopfIdeal R H} {x : H} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

theorem toIdeal_carrier (I : HopfIdeal R H) : I.toIdeal = I.carrier :=
  rfl

theorem le_def {I J : HopfIdeal R H} : I ≤ J ↔ ∀ ⦃x : H⦄, x ∈ I → x ∈ J :=
  Iff.rfl

theorem toIdeal_le_toIdeal {I J : HopfIdeal R H} :
    I.toIdeal ≤ J.toIdeal ↔ I ≤ J :=
  Iff.rfl

/-- Two Hopf ideals are equal when they contain the same elements. -/
@[ext]
theorem ext {I J : HopfIdeal R H} (h : ∀ x : H, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

/-- Constructor from an ideal and the three Hopf-ideal closure conditions. -/
@[expose] def ofIdeal (I : Ideal H) [I.IsTwoSided]
    (hcomul :
      ∀ ⦃x : H⦄, x ∈ I →
        Coalgebra.comul (R := R) x ∈
          leftTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) I)
    (hcounit : ∀ ⦃x : H⦄, x ∈ I → Coalgebra.counit (R := R) x = 0)
    (hantipode : ∀ ⦃x : H⦄, x ∈ I → HopfAlgebra.antipode R x ∈ I) :
    HopfIdeal R H where
  carrier := I
  isTwoSided' := inferInstance
  comul_mem' := hcomul
  counit_eq_zero' := hcounit
  antipode_mem' := hantipode

@[simp]
theorem ofIdeal_carrier (I : Ideal H) [I.IsTwoSided] (hcomul hcounit hantipode) :
    (ofIdeal (R := R) (H := H) I hcomul hcounit hantipode).carrier = I :=
  rfl

@[simp]
theorem mem_ofIdeal {I : Ideal H} [I.IsTwoSided] {hcomul hcounit hantipode} {x : H} :
    x ∈ ofIdeal (R := R) (H := H) I hcomul hcounit hantipode ↔ x ∈ I :=
  Iff.rfl

/-- The comultiplication of an element of a Hopf ideal lies in `I ⊗ H + H ⊗ I`. -/
theorem comul_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := H) I.toIdeal ⊔
        rightTensorIdeal (R := R) (H := H) I.toIdeal :=
  I.comul_mem' hx

/-- The counit vanishes on a Hopf ideal. -/
theorem counit_eq_zero (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.counit (R := R) x = 0 :=
  I.counit_eq_zero' hx

/-- The antipode preserves a Hopf ideal. -/
theorem antipode_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    HopfAlgebra.antipode R x ∈ I :=
  I.antipode_mem' hx

/-- A Hopf ideal absorbs multiplication on the right as well as on the left. -/
theorem mul_mem_right (I : HopfIdeal R H) {x : H} (hx : x ∈ I) (y : H) :
    x * y ∈ I :=
  I.toIdeal.mul_mem_right y hx

/-- The zero ideal as a Hopf ideal. -/
instance instBot : Bot (HopfIdeal R H) where
  bot :=
    { carrier := ⊥
      isTwoSided' := inferInstance
      comul_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      counit_eq_zero' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      antipode_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp }

@[simp]
theorem bot_toIdeal : (⊥ : HopfIdeal R H).toIdeal = (⊥ : Ideal H) :=
  rfl

@[simp]
theorem mem_bot {x : H} : x ∈ (⊥ : HopfIdeal R H) ↔ x = 0 :=
  Ideal.mem_bot

/-- The zero Hopf ideal is contained in every Hopf ideal. -/
instance : OrderBot (HopfIdeal R H) where
  bot := ⊥
  bot_le I x hx := by
    rw [mem_bot] at hx
    rw [hx]
    exact zero_mem I

/-- The sum of two Hopf ideals is a Hopf ideal. -/
instance instMax : Max (HopfIdeal R H) where
  max I J :=
    { carrier := I.toIdeal ⊔ J.toIdeal
      isTwoSided' := by
        refine ⟨fun {x} b hx => ?_⟩
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [add_mul]
        exact Submodule.add_mem_sup (I.mul_mem_right hy b) (J.mul_mem_right hz b)
      comul_mem' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [map_add]
        refine add_mem ?_ ?_
        · exact
            (sup_le_sup
                (leftTensorIdeal_mono (R := R) (H := H) (I := I.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_left)
                (rightTensorIdeal_mono (R := R) (H := H) (I := I.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_left))
              (I.comul_mem hy)
        · exact
            (sup_le_sup
                (leftTensorIdeal_mono (R := R) (H := H) (I := J.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_right)
                (rightTensorIdeal_mono (R := R) (H := H) (I := J.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_right))
              (J.comul_mem hz)
      counit_eq_zero' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        simp [I.counit_eq_zero hy, J.counit_eq_zero hz]
      antipode_mem' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [map_add]
        exact Submodule.add_mem_sup (I.antipode_mem hy) (J.antipode_mem hz) }

/-- The underlying ideal of the join of two Hopf ideals is the join of their underlying
ideals. -/
@[simp]
theorem sup_toIdeal (I J : HopfIdeal R H) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl

/-- Membership in the join of two Hopf ideals. -/
theorem mem_sup {I J : HopfIdeal R H} {x : H} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  rw [← mem_toIdeal, sup_toIdeal, Submodule.mem_sup]
  rfl

/-- Hopf ideals form a semilattice under ideal sum, with `⊔` given by the sum
construction. -/
instance instSemilatticeSup : SemilatticeSup (HopfIdeal R H) where
  sup := (· ⊔ ·)
  le_sup_left I J := by
    intro x hx
    exact Ideal.mem_sup_left hx
  le_sup_right I J := by
    intro x hx
    exact Ideal.mem_sup_right hx
  sup_le I J K hIK hJK := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    exact add_mem (hIK hy) (hJK hz)

/-- The supremum of a set of Hopf ideals has underlying ideal the supremum of the underlying
ideals. The four proof obligations are the implementation of this construction, so they are
discharged inline rather than as standalone lemmas. -/
instance instSupSet : SupSet (HopfIdeal R H) where
  sSup S :=
    { carrier := ⨆ I : S, (I : HopfIdeal R H).toIdeal
      isTwoSided' := by
        classical
        refine ⟨fun {x} b hx => ?_⟩
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, Finset.sum_mul]
        exact Submodule.sum_mem _ fun I _ =>
          Submodule.mem_iSup_of_mem I ((I : HopfIdeal R H).mul_mem_right (hf I) b)
      comul_mem' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        refine Submodule.sum_mem _ fun I _ => ?_
        exact sup_le_sup
          (leftTensorIdeal_mono (R := R) (H := H)
            (le_iSup (fun I : S => (I : HopfIdeal R H).toIdeal) I))
          (rightTensorIdeal_mono (R := R) (H := H)
            (le_iSup (fun I : S => (I : HopfIdeal R H).toIdeal) I))
          ((I : HopfIdeal R H).comul_mem (hf I))
      counit_eq_zero' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        exact Finset.sum_eq_zero fun I _ => (I : HopfIdeal R H).counit_eq_zero (hf I)
      antipode_mem' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        exact Submodule.sum_mem _ fun I _ =>
          Submodule.mem_iSup_of_mem I ((I : HopfIdeal R H).antipode_mem (hf I)) }

/-- The underlying ideal of a supremum of a set of Hopf ideals is the supremum of the
underlying ideals indexed by that set. -/
@[simp]
theorem sSup_toIdeal (S : Set (HopfIdeal R H)) :
    (sSup S).toIdeal = ⨆ I : S, (I : HopfIdeal R H).toIdeal :=
  rfl

/-- Membership in the supremum of a set of Hopf ideals. -/
theorem mem_sSup {S : Set (HopfIdeal R H)} {x : H} :
    x ∈ sSup S ↔
      ∃ f : S →₀ H, (∀ I : S, f I ∈ (I : HopfIdeal R H)) ∧ f.sum (fun _ y => y) = x := by
  rw [← mem_toIdeal, sSup_toIdeal]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun I : S => (I : HopfIdeal R H).toIdeal) x

/-- The underlying ideal of a supremum of a family of Hopf ideals is the supremum of the
underlying ideals. -/
@[simp]
theorem iSup_toIdeal {ι : Sort*} (I : ι → HopfIdeal R H) :
    (⨆ i, I i).toIdeal = ⨆ i, (I i).toIdeal := by
  rw [iSup, sSup_toIdeal]
  ext x
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of Hopf ideals. -/
theorem mem_iSup {ι : Type*} {I : ι → HopfIdeal R H} {x : H} :
    x ∈ ⨆ i, I i ↔ ∃ f : ι →₀ H, (∀ i, f i ∈ I i) ∧ f.sum (fun _ y => y) = x := by
  rw [← mem_toIdeal, iSup_toIdeal]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (I i).toIdeal) x

/-- Hopf ideals have arbitrary suprema, computed on underlying ideals. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (HopfIdeal R H) where
  sSup := sSup
  isLUB_sSup S :=
    ⟨fun I hI x hx => by
      rw [← mem_toIdeal, sSup_toIdeal]
      exact Submodule.mem_iSup_of_mem ⟨I, hI⟩ ((mem_toIdeal).2 hx),
    fun I hI x hx => by
      rw [← mem_toIdeal, sSup_toIdeal] at hx
      rw [← mem_toIdeal]
      have hle : (⨆ J : S, (J : HopfIdeal R H).toIdeal) ≤ I.toIdeal :=
        iSup_le fun J : S => toIdeal_le_toIdeal.2 (hI J.2)
      exact hle hx⟩

end HopfIdeal

section Bridge

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

namespace HopfIdeal

/-- A `HopfIdeal` gives Mathlib's coideal structure on the underlying `R`-submodule, so that
Mathlib's quotient `Coalgebra`/`Bialgebra` instances fire on `H ⧸ I.toIdeal`. -/
instance instIsCoideal (I : HopfIdeal R H) :
    (I.toIdeal.restrictScalars R).IsCoideal := by
  rw [Submodule.isCoideal_iff_comul_mem]
  refine ⟨fun _ hx => I.counit_eq_zero hx, fun _ hx => ?_⟩
  have := I.comul_mem hx
  rwa [← Submodule.restrictScalars_mem R, comul_mem_sup_restrictScalars_eq_range] at this

/-- A `HopfIdeal` gives Mathlib's `Ideal.IsHopfIdeal`, so that Mathlib's quotient
`HopfAlgebra` instance fires on `H ⧸ I.toIdeal`. -/
instance instIsHopfIdeal (I : HopfIdeal R H) : I.toIdeal.IsHopfIdeal R where
  __ := instIsCoideal I
  antipode_mem := fun _ hx => I.antipode_mem hx

end HopfIdeal

end Bridge

end TauCeti
