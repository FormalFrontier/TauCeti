/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental

/-!
# The Galois action on the places lying over a place

Let `F' / F` be an extension of fields and let `k` be a subfield of `F`. An `F`-automorphism `σ`
of `F'` transports the places of `F' / k`: the valuation `v_P ∘ σ⁻¹` is again normalized and
trivial on the constants, so `σ • P` is a place, and `v_{σ • P} (σ x) = v_P x`. Since `σ` fixes
`F` pointwise, `σ • P` lies over the same place of `F / k` as `P` does, with the same
ramification index and the same relative degree.

The main theorem is that when `F' / F` is a finite Galois extension this action is transitive on
each fibre: two places of `F' / k` lie over the same place of `F / k` exactly when one is carried
to the other by an automorphism (Stichtenoth, Theorem 3.7.1). The proof is the classical one:
weak approximation produces a function `z` with a zero at one of the two places and no zero or
pole anywhere on either orbit, and the norm `N_{F'/F} (z) = ∏ σ, σ z` — an element of `F` —
then has order `0` at one place of the fibre and order `> 0` at another, which is impossible
because on `F` the order at a place of `F'` is a positive multiple of the order at the place
below.

Consequently the ramification index and the relative degree are constant on a fibre, and the
fundamental identity of `TauCeti/FieldTheory/FunctionField/Place/Extension/Fundamental.lean` —
which applies because a Galois extension is separable — takes the product form
`r · e · f = [F' : F]` (Stichtenoth, Corollary 3.7.2). The stabilizer of a place is the
decomposition group, and is identified with Mathlib's `ValuationSubring.decompositionSubgroup`.

## Main definitions

* the `MulAction (F' ≃ₐ[F] F') (Place k F')` instance: the action of the automorphism group of
  `F' / F` on the places of `F' / k`, with `TauCeti.Place.valuation_smul` its defining property
  and `TauCeti.Place.integers_smul` the induced action on valuation rings.

## Main results

* `TauCeti.Place.restrict_smul`, `TauCeti.Place.ramificationIdx_smul` and
  `TauCeti.Place.relativeDegree_smul`: the action preserves the fibres of
  `TauCeti.Place.restrict` and the two invariants attached to a place of a fibre.
* `TauCeti.Place.exists_smul_eq_of_restrict_eq` and the packaged
  `TauCeti.Place.restrict_eq_iff_exists_smul_eq`: **the Galois group acts transitively on the
  places over a place** (Stichtenoth, Theorem 3.7.1), with
  `TauCeti.Place.setOf_restrict_eq_eq_orbit` restating a fibre as an orbit.
* `TauCeti.Place.ramificationIdx_eq_of_restrict_eq` and
  `TauCeti.Place.relativeDegree_eq_of_restrict_eq`: `e` and `f` are constant on a fibre, whence
  `TauCeti.Place.ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank`, the product form
  `r · e · f = [F' : F]` of the fundamental identity (Stichtenoth, Corollary 3.7.2).
* `TauCeti.Place.stabilizer_eq_decompositionSubgroup`: the stabilizer of a place is the
  decomposition group of its valuation ring.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.7.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Action

/-- **The action of the automorphism group of `F' / F` on the places of `F' / k`**: an
`F`-automorphism `σ` carries a place `P` to the place `σ • P` whose valuation is `v_P ∘ σ⁻¹`.
Normalization is preserved because `σ` is bijective, and triviality on the constants because
`σ` fixes `F`, hence `k`, pointwise. -/
instance instMulActionAlgEquiv : MulAction (F' ≃ₐ[F] F') (Place k F') where
  smul σ P :=
    { valuation := P.valuation.comap (σ.symm : F' →+* F')
      valuation_surjective := fun y ↦ by
        obtain ⟨x, hx⟩ := P.valuation_surjective y
        exact ⟨σ x, by simpa using hx⟩
      isTrivialOn :=
        { eq_one := fun c hc ↦ by
            have hfix : (σ.symm : F' →+* F') (algebraMap k F' c) = algebraMap k F' c := by
              rw [IsScalarTower.algebraMap_apply k F F']
              simp
            rw [Valuation.comap_apply, hfix]
            exact P.isTrivialOn.eq_one c hc } }
  one_smul P := Place.ext (Valuation.ext fun _ ↦ rfl)
  mul_smul σ τ P := Place.ext (Valuation.ext fun _ ↦ rfl)

variable (σ : F' ≃ₐ[F] F') (P : Place k F')

/-- **The defining property of the action**: the valuation of `σ • P` is the valuation of `P`
composed with `σ⁻¹`. -/
@[simp]
theorem valuation_smul (x : F') : (σ • P).valuation x = P.valuation (σ.symm x) := rfl

/-- The action moves the valuation along `σ`. -/
theorem valuation_smul_apply (x : F') : (σ • P).valuation (σ x) = P.valuation x := by
  simp

/-- The order function of `σ • P` is the order function of `P` composed with `σ⁻¹`. -/
@[simp]
theorem ord_smul (x : F') : (σ • P).ord x = P.ord (σ.symm x) := by
  rw [ord_def, ord_def, valuation_smul]

/-- The action moves the order function along `σ`. -/
theorem ord_smul_apply (x : F') : (σ • P).ord (σ x) = P.ord x := by
  simp

/-- Membership in the valuation ring of `σ • P`, read off at `P`. -/
theorem mem_integers_smul_iff {x : F'} : x ∈ (σ • P).integers ↔ σ.symm x ∈ P.integers := by
  simp

/-- The valuation ring of `σ • P` is the image of the valuation ring of `P` under `σ`, for
Mathlib's pointwise action on valuation subrings. -/
theorem integers_smul : (σ • P).integers = σ • P.integers := by
  ext x
  rw [mem_integers_smul_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- **The stabilizer of a place is the decomposition group** of its valuation ring
(Stichtenoth, Definition 3.8.1). -/
theorem stabilizer_eq_decompositionSubgroup :
    MulAction.stabilizer (F' ≃ₐ[F] F') P = P.integers.decompositionSubgroup F := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← integers_smul]
  exact ⟨fun h ↦ by rw [h], fun h ↦ integers_injective h⟩

/-- Two equal places have the same valuation ring; the isomorphism between the two carriers is
the identity on representatives. -/
private def integersEquivOfEq {P Q : Place k F} (h : P = Q) : P.integers ≃+* Q.integers where
  toFun x := ⟨(x : F), by rw [← h]; exact x.2⟩
  invFun x := ⟨(x : F), by rw [h]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
private theorem coe_integersEquivOfEq {P Q : Place k F} (h : P = Q) (x : P.integers) :
    ((integersEquivOfEq h x : Q.integers) : F) = (x : F) := rfl

/-- The automorphism `σ⁻¹` carries the valuation ring of `σ • P` isomorphically onto the
valuation ring of `P`. -/
private def integersEquivSmul : (σ • P).integers ≃+* P.integers where
  toFun x := ⟨σ.symm x, (mem_integers_smul_iff σ P).mp x.2⟩
  invFun y := ⟨σ y, (mem_integers_smul_iff σ P).mpr (by simp)⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp]
private theorem coe_integersEquivSmul (x : (σ • P).integers) :
    ((integersEquivSmul σ P x : P.integers) : F') = σ.symm (x : F') := rfl

end Action

section Restrict

variable [Algebra.IsIntegral F F'] (σ : F' ≃ₐ[F] F') (P : Place k F')

/-- **The action preserves the fibres of restriction**: `σ • P` lies over the same place of
`F / k` as `P` does, because `σ` fixes `F` pointwise. -/
@[simp]
theorem restrict_smul : (σ • P).restrict k F = P.restrict k F := by
  rw [restrict_eq_iff_exists_ord_eq]
  refine ⟨ramificationIdx F P, ramificationIdx_pos F P, fun f ↦ ?_⟩
  rw [ord_smul, AlgEquiv.commutes, ord_algebraMap_restrict k F P f]

/-- The ramification index is invariant under the action. -/
@[simp]
theorem ramificationIdx_smul : ramificationIdx F (σ • P) = ramificationIdx F P := by
  refine ramificationIdx_eq_of_forall_ord_eq k F (σ • P) fun f ↦ ?_
  rw [restrict_smul, ord_smul, AlgEquiv.commutes, ord_algebraMap_restrict k F P f]

/-- The relative degree is invariant under the action: `σ⁻¹` induces an isomorphism of the
residue field of `σ • P` with the residue field of `P` over the residue field of the place
below, which is the same for both. -/
@[simp]
theorem relativeDegree_smul : relativeDegree k F (σ • P) = relativeDegree k F P := by
  rw [relativeDegree_def k F (σ • P), relativeDegree_def k F P]
  refine Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (integersEquivOfEq (restrict_smul σ P)))
    (IsLocalRing.ResidueField.mapEquiv (integersEquivSmul σ P)) (RingHom.ext fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := ((σ • P).restrict k F).integers) z
  have hAB : algebraMap (P.restrict k F).integers P.integers
        (integersEquivOfEq (restrict_smul σ P) x) =
      integersEquivSmul σ P (algebraMap ((σ • P).restrict k F).integers (σ • P).integers x) :=
    Subtype.ext (by simp)
  simpa [IsLocalRing.ResidueField.map_residue] using congrArg (IsLocalRing.residue _) hAB

end Restrict

section Galois

variable [FiniteDimensional F F'] [IsGalois F F']

/-- **The Galois group acts transitively on the places over a place** (Stichtenoth,
Theorem 3.7.1): if two places of `F' / k` lie over the same place of `F / k`, then some
`F`-automorphism of `F'` carries one to the other. -/
theorem exists_smul_eq_of_restrict_eq {P Q : Place k F'} (h : P.restrict k F = Q.restrict k F) :
    ∃ σ : F' ≃ₐ[F] F', σ • P = Q := by
  classical
  by_contra hcon
  have hcon' : ∀ σ : F' ≃ₐ[F] F', σ • P ≠ Q := fun σ hσ ↦ hcon ⟨σ, hσ⟩
  set s : Finset (Place k F') :=
    (Finset.univ.image fun σ : F' ≃ₐ[F] F' ↦ σ • P) ∪
      (Finset.univ.image fun σ : F' ≃ₐ[F] F' ↦ σ • Q) with hs
  obtain ⟨z, hz⟩ := exists_forall_mem_ord_eq s fun X ↦ if X = Q then 1 else 0
  have hQmem : Q ∈ s :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ Q⟩)
  have hQz : Q.ord z = 1 := by simpa using hz Q hQmem
  have hz0 : z ≠ 0 := by rintro rfl; simp at hQz
  have hσz : ∀ σ : F' ≃ₐ[F] F', σ z ≠ 0 := fun σ ↦ by simpa using hz0
  -- the norm of `z`, an element of `F`, is the product of the conjugates of `z`
  have hprod : algebraMap F F' (Algebra.norm F z) = ∏ σ : F' ≃ₐ[F] F', σ z :=
    Algebra.norm_eq_prod_automorphisms F z
  -- at `P` every conjugate of `z` has order `0`, since no place of the orbit of `P` is `Q`
  have hPord : P.ord (algebraMap F F' (Algebra.norm F z)) = 0 := by
    rw [hprod, P.ord_prod Finset.univ fun σ _ ↦ hσz σ]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    have hmem : σ.symm • P ∈ s :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨σ.symm, Finset.mem_univ _, rfl⟩)
    have hval : (σ.symm • P).ord z = P.ord (σ z) := by simp
    rw [← hval, hz _ hmem]
    simp [hcon' σ.symm]
  -- hence the norm has order `0` at the place below
  have hbelow : (P.restrict k F).ord (Algebra.norm F z) = 0 := by
    rw [ord_algebraMap_restrict k F P] at hPord
    have := ramificationIdx_pos (F := F) P
    exact (mul_eq_zero.mp hPord).resolve_left (by exact_mod_cast this.ne')
  -- but at `Q` the conjugates of `z` have nonnegative orders, and the one at `σ = 1` is positive
  have hQord : 0 < Q.ord (algebraMap F F' (Algebra.norm F z)) := by
    rw [hprod, Q.ord_prod Finset.univ fun σ _ ↦ hσz σ]
    refine Finset.sum_pos' (fun σ _ ↦ ?_) ⟨1, Finset.mem_univ _, by simp [hQz]⟩
    have hmem : σ.symm • Q ∈ s :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨σ.symm, Finset.mem_univ _, rfl⟩)
    have hval : (σ.symm • Q).ord z = Q.ord (σ z) := by simp
    rw [← hval, hz _ hmem]
    split <;> norm_num
  rw [ord_algebraMap_restrict k F Q, ← h, hbelow, mul_zero] at hQord
  exact hQord.false

/-- **The fibres of restriction are the orbits of the Galois group** (Stichtenoth,
Theorem 3.7.1). -/
theorem restrict_eq_iff_exists_smul_eq {P Q : Place k F'} :
    P.restrict k F = Q.restrict k F ↔ ∃ σ : F' ≃ₐ[F] F', σ • P = Q :=
  ⟨exists_smul_eq_of_restrict_eq, by rintro ⟨σ, rfl⟩; rw [restrict_smul]⟩

/-- The places lying over the place below `P` are exactly the places in the orbit of `P`. -/
theorem setOf_restrict_eq_eq_orbit (P : Place k F') :
    {Q : Place k F' | Q.restrict k F = P.restrict k F} = MulAction.orbit (F' ≃ₐ[F] F') P := by
  ext Q
  refine ⟨fun hQ ↦ restrict_eq_iff_exists_smul_eq.mp hQ.symm, ?_⟩
  rintro ⟨σ, rfl⟩
  exact restrict_smul σ P

/-- **The ramification index is constant on a fibre** (Stichtenoth, Corollary 3.7.2). -/
theorem ramificationIdx_eq_of_restrict_eq {P Q : Place k F'}
    (h : P.restrict k F = Q.restrict k F) : ramificationIdx F P = ramificationIdx F Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_restrict_eq h
  rw [ramificationIdx_smul]

/-- **The relative degree is constant on a fibre** (Stichtenoth, Corollary 3.7.2). -/
theorem relativeDegree_eq_of_restrict_eq {P Q : Place k F'}
    (h : P.restrict k F = Q.restrict k F) : relativeDegree k F P = relativeDegree k F Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_restrict_eq h
  rw [relativeDegree_smul]

/-- **The fundamental identity in product form** (Stichtenoth, Corollary 3.7.2): for a finite
Galois extension the `r` places over a place all share one ramification index `e` and one relative
degree `f`, and `r · e · f = [F' : F]`.

A Galois extension is separable, so the fundamental identity applies with no further
hypothesis. -/
theorem ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank (P : Place k F') :
    {Q : Place k F' | Q.restrict k F = P.restrict k F}.ncard *
        (ramificationIdx F P * relativeDegree k F P) = Module.finrank F F' := by
  have hfin := finite_setOf_restrict_eq (k' := k) (F' := F') k F (P.restrict k F)
  have heq := sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F
    (P.restrict k F) (s := hfin.toFinset) fun Q ↦ hfin.mem_toFinset
  rw [Finset.sum_congr rfl fun Q hQ ↦ ?_] at heq
  · rwa [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin] at heq
  · rw [← ramificationIdx_eq_of_restrict_eq (hfin.mem_toFinset.mp hQ),
      ← relativeDegree_eq_of_restrict_eq (hfin.mem_toFinset.mp hQ)]

end Galois

end Place

end TauCeti
