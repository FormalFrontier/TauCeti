/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# The decomposition group and the decomposition field of a place

Let `F' / F` be a finite Galois extension of fields, `k` a subfield of `F`, and `P` a place of
`F' / k`.  The Galois group acts on the places of `F' / k` and is transitive on each fibre of
restriction, so the fibre through `P` is the orbit of `P` and the stabilizer of `P` — Mathlib's
`ValuationSubring.decompositionSubgroup` of the valuation ring of `P` — has index the number of
places over `P ∩ F`.  Comparing that count with the fundamental identity `r · e · f = [F' : F]`
gives the order of the decomposition group,
`TauCeti.Place.card_decompositionSubgroup`: it is `e(P ∣ P ∩ F) · f(P ∣ P ∩ F)`.

The **decomposition field** `Z` of `P` is the subfield of `F'` fixed by that group.  The Galois
group of `F'` over `Z` is again the decomposition group, so every automorphism of `F'` over `Z`
fixes `P`, and transitivity then forces `P` to be the *only* place of `F'` over its restriction
to `Z`.  With the
fibre a single point, the fundamental identity over the decomposition field reads
`e(P ∣ P ∩ Z) · f(P ∣ P ∩ Z) = [F' : Z] = e(P ∣ P ∩ F) · f(P ∣ P ∩ F)`, and multiplicativity in
the tower `F ⊆ Z ⊆ F'` then splits off `e = f = 1` below `Z`: the whole of the ramification and
of the residue extension of `P` over `F` happens over the decomposition field.

This is Stichtenoth, Definition 3.8.1 and the first half of Theorem 3.8.2.  The second half —
that the decomposition group surjects onto the automorphism group of the separable part of the
residue extension, with kernel the inertia group `ValuationSubring.inertiaSubgroup` — is not
proved here.

## Main definitions

* `TauCeti.Place.decompositionField`: the subfield of `F'` fixed by the decomposition group of a
  place, an `IntermediateField F F'`.

## Main results

* `TauCeti.Place.card_decompositionSubgroup`: the decomposition group of `P` has order
  `e(P ∣ P ∩ F) · f(P ∣ P ∩ F)`, and `TauCeti.Place.finrank_decompositionField` restates this as
  the degree of `F'` over the decomposition field.
* `TauCeti.Place.eq_of_restrict_decompositionField_eq` and
  `TauCeti.Place.setOfPred_restrict_decompositionField_eq_singleton`: **a place is the only
  place of `F'` above its restriction to its decomposition field**.
* `TauCeti.Place.ramificationIdx_restrict_decompositionField` and
  `TauCeti.Place.relativeDegree_restrict_decompositionField`: below the decomposition field the
  ramification index and the relative degree are `1`, so by
  `TauCeti.Place.ramificationIdx_decompositionField` and
  `TauCeti.Place.relativeDegree_decompositionField` both are unchanged above it.
* `TauCeti.Place.decompositionSubgroup_integers_smul` and
  `TauCeti.Place.decompositionField_smul`: conjugate places have conjugate decomposition groups
  and decomposition fields.
* `TauCeti.Place.decompositionField_eq_top_iff_isSplitCompletely`: the decomposition field is
  everything exactly when the place below splits completely.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.8.1 and Theorem 3.8.2.
-/

public section

namespace TauCeti

/-- Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K S L` for an
intermediate field `S` of `L / K`; a place of `F' / k` restricted to an intermediate field of
`F' / F` needs the same statement over the constant field `k` sitting below `F`. -/
instance instIsScalarTowerIntermediateField {k F F' : Type*} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
    (E : IntermediateField F F') : IsScalarTower k E F' :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F'] [FiniteDimensional F F'] [IsGalois F F']

variable (F)

/-- **The order of the decomposition group** (Stichtenoth, Theorem 3.8.2): the stabilizer of a
place `P` in a finite Galois extension has order `e(P ∣ P ∩ F) · f(P ∣ P ∩ F)`.

The fibre of `P` is its orbit, so the orbit--stabilizer count and the fundamental identity
`r · e · f = [F' : F]` differ only by the common factor `r`. -/
theorem card_decompositionSubgroup (P : Place k F') :
    Nat.card (P.integers.decompositionSubgroup F) =
      ramificationIdx F P * relativeDegree k F P := by
  have hfin := finite_setOf_restrict_eq (k' := k) (F' := F') k F (P.restrict k F)
  have hpos : 0 < {Q : Place k F' | Q.restrict k F = P.restrict k F}.ncard :=
    (Set.ncard_pos hfin).mpr ⟨P, rfl⟩
  have hstab := ncard_mul_card_stabilizer_eq_finrank (F := F) P
  rw [stabilizer_eq_decompositionSubgroup] at hstab
  have hfund := ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank (F := F) P
  rw [← hstab] at hfund
  exact (Nat.eq_of_mul_eq_mul_left hpos hfund).symm

/-- **The decomposition field** of a place `P` of `F' / k` in a finite Galois extension `F' / F`
(Stichtenoth, Definition 3.8.1): the subfield of `F'` fixed by the decomposition group of `P`. -/
def decompositionField (P : Place k F') : IntermediateField F F' :=
  IntermediateField.fixedField (P.integers.decompositionSubgroup F)

omit [Algebra.IsIntegral F F'] [FiniteDimensional F F'] [IsGalois F F'] in
/-- **The two actions on places agree**: restricting the scalars of an automorphism of `F'` over
an intermediate field `E` down to `F` does not change the place it produces. -/
theorem restrictScalars_smul (E : IntermediateField F F') (τ : F' ≃ₐ[E] F') (Q : Place k F') :
    τ.restrictScalars F • Q = τ • Q := rfl

omit [Algebra.IsIntegral F F'] [IsGalois F F'] in
/-- An automorphism of `F'` over the decomposition field of `P`, read as an automorphism over
`F`, fixes `P`. -/
theorem restrictScalars_smul_eq_self (P : Place k F') (τ : F' ≃ₐ[decompositionField F P] F') :
    τ.restrictScalars F • P = P := by
  refine MulAction.mem_stabilizer_iff.mp ?_
  rw [stabilizer_eq_decompositionSubgroup,
    ← IntermediateField.fixingSubgroup_fixedField (P.integers.decompositionSubgroup F)]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ τ.commutes ⟨x, hx⟩

omit [Algebra.IsIntegral F F'] in
/-- **A place is the only place of `F'` above its restriction to its decomposition field**
(Stichtenoth, Theorem 3.8.2). -/
theorem eq_of_restrict_decompositionField_eq {P Q : Place k F'}
    (h : restrict k (decompositionField F P) Q = restrict k (decompositionField F P) P) :
    Q = P := by
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_restrict_eq (F := (decompositionField F P : Type v')) h
  refine MulAction.injective (τ.restrictScalars F) ?_
  change τ.restrictScalars F • Q = τ.restrictScalars F • P
  rw [restrictScalars_smul F _ τ Q, hτ, restrictScalars_smul_eq_self F P τ]

omit [Algebra.IsIntegral F F'] in
/-- The fibre of a place over its restriction to its decomposition field is a single point. -/
theorem setOfPred_restrict_decompositionField_eq_singleton (P : Place k F') :
    {Q : Place k F' | restrict k (decompositionField F P) Q =
      restrict k (decompositionField F P) P} = {P} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun _ h ↦ eq_of_restrict_decompositionField_eq F h⟩

/-- **The degree of `F'` over the decomposition field** (Stichtenoth, Theorem 3.8.2): it is the
order of the decomposition group, that is `e(P ∣ P ∩ F) · f(P ∣ P ∩ F)`. -/
theorem finrank_decompositionField (P : Place k F') :
    Module.finrank (decompositionField F P) F' =
      ramificationIdx F P * relativeDegree k F P := by
  rw [decompositionField, IntermediateField.finrank_fixedField_eq_card,
    card_decompositionSubgroup]

/-- **The ramification index and the relative degree are unchanged over the decomposition field**
(Stichtenoth, Theorem 3.8.2), in the product form the fundamental identity supplies. -/
theorem ramificationIdx_mul_relativeDegree_decompositionField (P : Place k F') :
    ramificationIdx (decompositionField F P) P *
        relativeDegree k (decompositionField F P) P =
      ramificationIdx F P * relativeDegree k F P := by
  have h := ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank
    (F := (decompositionField F P : Type v')) P
  rw [setOfPred_restrict_decompositionField_eq_singleton, Set.ncard_singleton, one_mul,
    finrank_decompositionField] at h
  exact h

private theorem eq_one_of_restrict_decompositionField (P : Place k F') :
    ramificationIdx F (restrict k (decompositionField F P) P) = 1 ∧
      relativeDegree k F (restrict k (decompositionField F P) P) = 1 := by
  have he : ramificationIdx F P = ramificationIdx (decompositionField F P) P *
      ramificationIdx F (restrict k (decompositionField F P) P) :=
    ramificationIdx_restrict_mul (k₁ := k) (F₀ := F)
      (F₁ := (decompositionField F P : Type v')) P
  have hf : relativeDegree k F P = relativeDegree k (decompositionField F P) P *
      relativeDegree k F (restrict k (decompositionField F P) P) :=
    relativeDegree_restrict_mul (k₀ := k) (k₁ := k) (F₀ := F)
      (F₁ := (decompositionField F P : Type v')) P
  have hmul := ramificationIdx_mul_relativeDegree_decompositionField F P
  have hpos : 0 < ramificationIdx (decompositionField F P) P *
      relativeDegree k (decompositionField F P) P :=
    Nat.mul_pos (ramificationIdx_pos _ P) (one_le_relativeDegree k _ P)
  rw [he, hf] at hmul
  have hcancel : ramificationIdx (decompositionField F P) P *
        relativeDegree k (decompositionField F P) P * 1 =
      ramificationIdx (decompositionField F P) P *
        relativeDegree k (decompositionField F P) P *
        (ramificationIdx F (restrict k (decompositionField F P) P) *
          relativeDegree k F (restrict k (decompositionField F P) P)) := by
    rw [mul_one]
    exact hmul.trans (by ring)
  have hone := (Nat.eq_of_mul_eq_mul_left hpos hcancel).symm
  exact ⟨Nat.dvd_one.mp ⟨_, hone.symm⟩,
    Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact hone.symm⟩⟩

/-- **A place is unramified over its decomposition field** (Stichtenoth, Theorem 3.8.2). -/
theorem ramificationIdx_restrict_decompositionField (P : Place k F') :
    ramificationIdx F (restrict k (decompositionField F P) P) = 1 :=
  (eq_one_of_restrict_decompositionField F P).1

/-- **The residue extension below the decomposition field is trivial** (Stichtenoth,
Theorem 3.8.2). -/
theorem relativeDegree_restrict_decompositionField (P : Place k F') :
    relativeDegree k F (restrict k (decompositionField F P) P) = 1 :=
  (eq_one_of_restrict_decompositionField F P).2

/-- **The ramification index is unchanged over the decomposition field** (Stichtenoth,
Theorem 3.8.2). -/
theorem ramificationIdx_decompositionField (P : Place k F') :
    ramificationIdx (decompositionField F P) P = ramificationIdx F P := by
  rw [ramificationIdx_restrict_mul (k₁ := k) (F₀ := F)
    (F₁ := (decompositionField F P : Type v')) P,
    ramificationIdx_restrict_decompositionField, mul_one]

/-- **The relative degree is unchanged over the decomposition field** (Stichtenoth,
Theorem 3.8.2). -/
theorem relativeDegree_decompositionField (P : Place k F') :
    relativeDegree k (decompositionField F P) P = relativeDegree k F P := by
  have hf : relativeDegree k F P = relativeDegree k (decompositionField F P) P *
      relativeDegree k F (restrict k (decompositionField F P) P) :=
    relativeDegree_restrict_mul (k₀ := k) (k₁ := k) (F₀ := F)
      (F₁ := (decompositionField F P : Type v')) P
  rw [hf, relativeDegree_restrict_decompositionField, mul_one]

omit [Algebra.IsIntegral F F'] [FiniteDimensional F F'] [IsGalois F F'] in
/-- **The decomposition group of a conjugate place is the conjugate decomposition group**
(Stichtenoth, Theorem 3.8.2). -/
theorem decompositionSubgroup_integers_smul (σ : F' ≃ₐ[F] F') (P : Place k F') :
    (σ • P).integers.decompositionSubgroup F =
      (P.integers.decompositionSubgroup F).map (MulAut.conj σ).toMonoidHom := by
  rw [← stabilizer_eq_decompositionSubgroup, ← stabilizer_eq_decompositionSubgroup,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]

omit [Algebra.IsIntegral F F'] [FiniteDimensional F F'] [IsGalois F F'] in
private theorem fixedField_map_conj (H : Subgroup (F' ≃ₐ[F] F')) (σ : F' ≃ₐ[F] F') :
    IntermediateField.fixedField (H.map (MulAut.conj σ).toMonoidHom) =
      (IntermediateField.fixedField H).map σ.toAlgHom := by
  ext x
  simp only [IntermediateField.mem_fixedField_iff, IntermediateField.mem_map]
  constructor
  · intro h
    refine ⟨σ.symm x, fun g hg ↦ ?_, by simp⟩
    have hx := h (MulAut.conj σ g) (Subgroup.mem_map_of_mem _ hg)
    exact σ.injective (by simpa using hx)
  · rintro ⟨y, hy, rfl⟩ g ⟨h, hh, rfl⟩
    simpa using congrArg σ (hy h hh)

omit [Algebra.IsIntegral F F'] [FiniteDimensional F F'] [IsGalois F F'] in
/-- **The decomposition field of a conjugate place is the image of the decomposition field**
(Stichtenoth, Theorem 3.8.2). -/
theorem decompositionField_smul (σ : F' ≃ₐ[F] F') (P : Place k F') :
    decompositionField F (σ • P) = (decompositionField F P).map σ.toAlgHom := by
  rw [decompositionField, decompositionSubgroup_integers_smul, fixedField_map_conj,
    decompositionField]

/-- **The degree of the decomposition field over `F`** (Stichtenoth, Theorem 3.8.2): it is the
number of places of `F' / k` lying over the place below `P`. -/
theorem finrank_decompositionField_eq_ncard_setOfPred_restrict_eq (P : Place k F') :
    Module.finrank F (decompositionField F P) =
      {Q : Place k F' | Q.restrict k F = P.restrict k F}.ncard := by
  have htower := Module.finrank_mul_finrank F (decompositionField F P : Type v') F'
  rw [finrank_decompositionField] at htower
  have hfund := ncard_mul_ramificationIdx_mul_relativeDegree_eq_finrank (F := F) P
  refine Nat.eq_of_mul_eq_mul_right ?_ (htower.trans hfund.symm)
  exact Nat.mul_pos (ramificationIdx_pos F P) (one_le_relativeDegree k F P)

/-- **A place splits completely exactly when its decomposition field is everything**
(Stichtenoth, Definition 3.1.13 and Theorem 3.8.2). -/
theorem decompositionField_eq_top_iff_isSplitCompletely (P : Place k F') :
    decompositionField F P = ⊤ ↔
      IsSplitCompletely (k' := k) (F' := F') (restrict k F P) := by
  rw [isSplitCompletely_iff_decompositionSubgroup_eq_bot]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← IntermediateField.fixingSubgroup_fixedField (P.integers.decompositionSubgroup F),
      ← decompositionField, h, IntermediateField.fixingSubgroup_top]
  · rw [decompositionField, h, IntermediateField.fixedField_bot]

end Place

end TauCeti
