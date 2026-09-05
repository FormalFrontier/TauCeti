/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# Orthogonal complements and quotients of an orthogonal direct sum

Let `A` and `B` be finite bilinear modules and let `H ≤ A`, `K ≤ B` be additive subgroups. The
pairing of the orthogonal direct sum `A ⊥ B` has no cross terms, so orthogonality of a vector
against the product subgroup `H × K` is orthogonality of each component against its own factor:

```text
(H × K)⊥ = H⊥ × K⊥.
```

The Lagrangian condition is componentwise for the same reason — as is isotropy, proved in
`TauCeti.LinearAlgebra.FiniteBilinearModule.Basic` — and the orthogonal quotient splits:

```text
(H × K)⊥ / ((H × K) ∩ (H × K)⊥) ≅
  (H⊥ / (H ∩ H⊥)) ⊥ (K⊥ / (K ∩ K⊥)).
```

The same statements hold for finite quadratic modules, whose orthogonal quotient is taken along a
quadratic-isotropic subgroup; there the quadratic values, not only the pairings, add across the
two factors. The quadratic splitting is the bilinear one: the underlying bilinear module of a
quadratic orthogonal quotient is the bilinear orthogonal quotient, so only the preservation of
quadratic values has to be checked.

These are the componentwise laws that the gluing theory of integral lattices needs: the
discriminant module of an orthogonal direct sum of lattices is the orthogonal direct sum of the
discriminant modules, and an overlattice glued along a product subgroup is the orthogonal direct
sum of the two glued overlattices, so its discriminant module must split the same way.

## Main declarations

* `TauCeti.FiniteBilinearModule.orthogonalComplement_prod`: `(H × K)⊥ = H⊥ × K⊥`.
* `TauCeti.FiniteBilinearModule.isLagrangian_prod_iff`: the Lagrangian condition is componentwise.
* `TauCeti.FiniteBilinearModule.orthogonalQuotientProdIsometry`: the isometry
  `(H × K)⊥ / ((H × K) ∩ (H × K)⊥) ≅
    (H⊥ / (H ∩ H⊥)) ⊥ (K⊥ / (K ∩ K⊥))`.
* `TauCeti.FiniteQuadraticModule.isLagrangian_prod_iff` and
  `TauCeti.FiniteQuadraticModule.orthogonalQuotientProdIsometry`: the quadratic counterparts.
  An orthogonal direct sum of quadratic isometries is Mathlib's
  `QuadraticMap.IsometryEquiv.prod`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u v

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u}) (B : FiniteBilinearModule.{v})

/-! ## Orthogonal complements of a product subgroup -/

/-- A vector of `A ⊥ B` is orthogonal to `H × K` exactly when each of its components is
orthogonal to the corresponding factor. -/
theorem mem_orthogonalComplement_prod_iff (H : AddSubgroup A) (K : AddSubgroup B)
    (x : A.carrier × B.carrier) :
    x ∈ (A.prod B).orthogonalComplement (H.prod K) ↔
      x.1 ∈ A.orthogonalComplement H ∧ x.2 ∈ B.orthogonalComplement K := by
  rw [(A.prod B).mem_orthogonalComplement_iff, A.mem_orthogonalComplement_iff,
    B.mem_orthogonalComplement_iff]
  constructor
  · intro hx
    refine ⟨fun y hy ↦ ?_, fun z hz ↦ ?_⟩
    · have h := hx (y, 0) (AddSubgroup.mem_prod.mpr ⟨hy, K.zero_mem⟩)
      rwa [A.prod_pairing B, B.pairing_zero_right, add_zero] at h
    · have h := hx (0, z) (AddSubgroup.mem_prod.mpr ⟨H.zero_mem, hz⟩)
      rwa [A.prod_pairing B, A.pairing_zero_right, zero_add] at h
  · rintro ⟨hxA, hxB⟩ y hy
    rw [AddSubgroup.mem_prod] at hy
    rw [A.prod_pairing B, hxA y.1 hy.1, hxB y.2 hy.2, add_zero]

/-- **The orthogonal complement of a product subgroup is the product of the complements.** -/
@[simp]
theorem orthogonalComplement_prod (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).orthogonalComplement (H.prod K) =
      (A.orthogonalComplement H).prod (B.orthogonalComplement K) := by
  ext x
  rw [AddSubgroup.mem_prod]
  exact A.mem_orthogonalComplement_prod_iff B H K x

/-- **The Lagrangian condition on a product subgroup is componentwise.** -/
@[simp]
theorem isLagrangian_prod_iff (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).IsLagrangian (H.prod K) ↔ A.IsLagrangian H ∧ B.IsLagrangian K := by
  rw [(A.prod B).isLagrangian_def, A.isLagrangian_def, B.isLagrangian_def,
    A.orthogonalComplement_prod B]
  constructor
  · intro h
    refine ⟨AddSubgroup.ext fun x ↦ ?_, AddSubgroup.ext fun y ↦ ?_⟩
    · have hx : (x, (0 : B.carrier)) ∈ H.prod K ↔
          (x, (0 : B.carrier)) ∈
            (A.orthogonalComplement H).prod (B.orthogonalComplement K) := by
        rw [h]
      simpa only [AddSubgroup.mem_prod, K.zero_mem,
        (B.orthogonalComplement K).zero_mem, and_true] using hx
    · have hy : ((0 : A.carrier), y) ∈ H.prod K ↔
          ((0 : A.carrier), y) ∈
            (A.orthogonalComplement H).prod (B.orthogonalComplement K) := by
        rw [h]
      simpa only [AddSubgroup.mem_prod, H.zero_mem,
        (A.orthogonalComplement H).zero_mem, true_and] using hy
  · intro h
    exact congrArg₂ AddSubgroup.prod h.1 h.2

/-! ## The orthogonal quotient of an orthogonal direct sum -/

variable {A B}

/-- The first component of a vector of `A ⊥ B` orthogonal to `H × K`, as a vector of `A`
orthogonal to `H`. -/
def orthogonalComplementProdFst (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).orthogonalComplement (H.prod K) →+ A.orthogonalComplement H where
  toFun x := ⟨(x : A.carrier × B.carrier).1,
    ((A.mem_orthogonalComplement_prod_iff B H K x).mp x.2).1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The second component of a vector of `A ⊥ B` orthogonal to `H × K`, as a vector of `B`
orthogonal to `K`. -/
def orthogonalComplementProdSnd (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).orthogonalComplement (H.prod K) →+ B.orthogonalComplement K where
  toFun x := ⟨(x : A.carrier × B.carrier).2,
    ((A.mem_orthogonalComplement_prod_iff B H K x).mp x.2).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Taking the first component of a vector of `(H × K)⊥` and then forgetting that it lies in `H⊥`
is taking the first component in `A ⊥ B`. -/
@[simp]
theorem coe_orthogonalComplementProdFst (H : AddSubgroup A) (K : AddSubgroup B)
    (x : (A.prod B).orthogonalComplement (H.prod K)) :
    (orthogonalComplementProdFst H K x : A) = (x : A.carrier × B.carrier).1 := (rfl)

/-- Taking the second component of a vector of `(H × K)⊥` and then forgetting that it lies in `K⊥`
is taking the second component in `A ⊥ B`. -/
@[simp]
theorem coe_orthogonalComplementProdSnd (H : AddSubgroup A) (K : AddSubgroup B)
    (x : (A.prod B).orthogonalComplement (H.prod K)) :
    (orthogonalComplementProdSnd H K x : B) = (x : A.carrier × B.carrier).2 := (rfl)

/-- The identification `(H × K)⊥ ≃ H⊥ × K⊥` underlying the quotient splitting. -/
private def orthogonalComplementProdEquiv (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).orthogonalComplement (H.prod K) ≃ₗ[ℤ]
      A.orthogonalComplement H × B.orthogonalComplement K where
  toFun x := (orthogonalComplementProdFst H K x, orthogonalComplementProdSnd H K x)
  invFun x := ⟨((x.1 : A), (x.2 : B)),
    (A.mem_orthogonalComplement_prod_iff B H K _).mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Under `(H × K)⊥ ≃ H⊥ × K⊥`, the denominator is the product of the two
denominators. -/
private theorem map_addSubgroupOf_orthogonalComplement_prod (H : AddSubgroup A)
    (K : AddSubgroup B) :
    ((H.prod K).addSubgroupOf
        ((A.prod B).orthogonalComplement (H.prod K))).toIntSubmodule.map
      (orthogonalComplementProdEquiv H K : _ →ₗ[ℤ] _) =
      (H.addSubgroupOf (A.orthogonalComplement H)).toIntSubmodule.prod
        (K.addSubgroupOf (B.orthogonalComplement K)).toIntSubmodule := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_prod]
  -- The source subgroup is represented inside the complement subtype, so expose the coercion
  -- applied by the inverse complement equivalence before using `AddSubgroup.mem_prod`.
  change ((orthogonalComplementProdEquiv H K).symm x : A.carrier × B.carrier) ∈ H.prod K ↔
    (x.1 : A) ∈ H ∧ (x.2 : B) ∈ K
  rw [AddSubgroup.mem_prod]
  rfl

/-- The canonical linear equivalence splitting the orthogonal quotient of a product. -/
private noncomputable def orthogonalQuotientProdLinearEquiv (H : AddSubgroup A)
    (K : AddSubgroup B) :
    (A.prod B).orthogonalQuotient (H.prod K) ≃ₗ[ℤ]
      (A.orthogonalQuotient H).carrier × (B.orthogonalQuotient K).carrier :=
  (Submodule.Quotient.equiv _ _ (orthogonalComplementProdEquiv H K)
      (map_addSubgroupOf_orthogonalComplement_prod H K)).trans
    (Submodule.quotientProdEquiv
      (H.addSubgroupOf (A.orthogonalComplement H)).toIntSubmodule
      (K.addSubgroupOf (B.orthogonalComplement K)).toIntSubmodule)

@[simp]
private theorem orthogonalQuotientProdLinearEquiv_orthogonalQuotientMk
    (H : AddSubgroup A) (K : AddSubgroup B)
    (x : (A.prod B).orthogonalComplement (H.prod K)) :
    orthogonalQuotientProdLinearEquiv H K
        ((A.prod B).orthogonalQuotientMk (H.prod K) x) =
      (A.orthogonalQuotientMk H (orthogonalComplementProdFst H K x),
        B.orthogonalQuotientMk K (orthogonalComplementProdSnd H K x)) := by
  rw [(A.prod B).orthogonalQuotientMk_apply]
  -- The linear equivalence is a composite of the transported-complement quotient equivalence and
  -- the quotient-product equivalence; expose that composite to apply their representative lemmas.
  change (Submodule.quotientProdEquiv _ _)
      ((Submodule.Quotient.equiv _ _ (orthogonalComplementProdEquiv H K)
        (map_addSubgroupOf_orthogonalComplement_prod H K)) (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    Submodule.quotientProdEquiv_apply_mk, A.orthogonalQuotientMk_apply,
    B.orthogonalQuotientMk_apply]
  rfl

/-- **The orthogonal quotient of an orthogonal direct sum splits.** For subgroups `H ≤ A` and
`K ≤ B`, the orthogonal quotient of `A ⊥ B` by `H × K` is the orthogonal direct sum of the two
orthogonal quotients:

```text
(H × K)⊥ / ((H × K) ∩ (H × K)⊥) ≅
  (H⊥ / (H ∩ H⊥)) ⊥ (K⊥ / (K ∩ K⊥)).
```

No isotropy hypothesis is needed, exactly as for the orthogonal quotient itself. -/
noncomputable def orthogonalQuotientProdIsometry (H : AddSubgroup A) (K : AddSubgroup B) :
    Isometry ((A.prod B).orthogonalQuotient (H.prod K))
      ((A.orthogonalQuotient H).prod (B.orthogonalQuotient K)) where
  toAddEquiv := (orthogonalQuotientProdLinearEquiv H K).toAddEquiv
  map_pairing' q r := by
    induction q using orthogonalQuotient_induction_on with
    | mk x =>
      induction r using orthogonalQuotient_induction_on with
      | mk y =>
        -- The isometry stores the linear equivalence above as an additive equivalence; expose that
        -- wrapper equality so its representative theorem rewrites both arguments.
        change ((A.orthogonalQuotient H).prod (B.orthogonalQuotient K)).pairing
            (orthogonalQuotientProdLinearEquiv H K _) (orthogonalQuotientProdLinearEquiv H K _) = _
        rw [orthogonalQuotientProdLinearEquiv_orthogonalQuotientMk,
          orthogonalQuotientProdLinearEquiv_orthogonalQuotientMk, prod_pairing,
          A.orthogonalQuotient_pairing_mk, B.orthogonalQuotient_pairing_mk,
          (A.prod B).orthogonalQuotient_pairing_mk, prod_pairing,
          coe_orthogonalComplementProdFst, coe_orthogonalComplementProdFst,
          coe_orthogonalComplementProdSnd, coe_orthogonalComplementProdSnd]

/-- **The splitting of an orthogonal quotient on representatives.** -/
@[simp]
theorem orthogonalQuotientProdIsometry_orthogonalQuotientMk (H : AddSubgroup A)
    (K : AddSubgroup B) (x : (A.prod B).orthogonalComplement (H.prod K)) :
    orthogonalQuotientProdIsometry H K ((A.prod B).orthogonalQuotientMk (H.prod K) x) =
      (A.orthogonalQuotientMk H (orthogonalComplementProdFst H K x),
        B.orthogonalQuotientMk K (orthogonalComplementProdSnd H K x)) :=
  orthogonalQuotientProdLinearEquiv_orthogonalQuotientMk H K x

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v})

/-! ## The quadratic Lagrangian condition on a product subgroup -/

/-- **The quadratic Lagrangian condition on a product subgroup is componentwise.** -/
@[simp]
theorem isLagrangian_prod_iff (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).IsLagrangian (H.prod K) ↔ A.IsLagrangian H ∧ B.IsLagrangian K := by
  constructor
  · intro h
    have hisotropic := (A.isIsotropic_prod_iff B H K).mp (IsLagrangian.isIsotropic _ h)
    have hlagrangian := (FiniteBilinearModule.isLagrangian_prod_iff
      A.toFiniteBilinearModule B.toFiniteBilinearModule H K).mp
      (IsLagrangian.toFiniteBilinearModule _ h)
    exact ⟨(A.isLagrangian_def H).mpr ⟨hisotropic.1, hlagrangian.1⟩,
      (B.isLagrangian_def K).mpr ⟨hisotropic.2, hlagrangian.2⟩⟩
  · intro h
    refine ((A.prod B).isLagrangian_def (H.prod K)).mpr
      ⟨(A.isIsotropic_prod_iff B H K).mpr
        ⟨IsLagrangian.isIsotropic _ h.1, IsLagrangian.isIsotropic _ h.2⟩, ?_⟩
    exact (FiniteBilinearModule.isLagrangian_prod_iff
      A.toFiniteBilinearModule B.toFiniteBilinearModule H K).mpr
      ⟨IsLagrangian.toFiniteBilinearModule _ h.1,
        IsLagrangian.toFiniteBilinearModule _ h.2⟩

/-! ## The orthogonal quotient of an orthogonal direct sum -/

variable {A B}

/-- The additive equivalence splitting a quadratic orthogonal quotient of `A ⊥ B` along a product
subgroup. It *is* the bilinear splitting: the underlying bilinear module of a quadratic orthogonal
quotient is the bilinear orthogonal quotient, and an orthogonal direct sum of quadratic modules
has the orthogonal direct sum of the polar pairings, so the two source and target modules agree. -/
private noncomputable def orthogonalQuotientProdAddEquiv {H : AddSubgroup A} {K : AddSubgroup B}
    (hH : A.IsIsotropic H) (hK : B.IsIsotropic K) :
    (A.prod B).orthogonalQuotient (H.prod K) ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩) ≃+
      (A.orthogonalQuotient H hH).prod (B.orthogonalQuotient K hK) :=
  (((A.prod B).orthogonalQuotientUnderlyingEquiv (H.prod K)
      ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩)).trans
    (FiniteBilinearModule.orthogonalQuotientProdIsometry (A := A.toFiniteBilinearModule)
      (B := B.toFiniteBilinearModule) H K).toAddEquiv).trans
    ((A.orthogonalQuotientUnderlyingEquiv H hH).symm.prodCongr
      (B.orthogonalQuotientUnderlyingEquiv K hK).symm)

@[simp]
private theorem orthogonalQuotientProdAddEquiv_orthogonalQuotientMk {H : AddSubgroup A}
    {K : AddSubgroup B} (hH : A.IsIsotropic H) (hK : B.IsIsotropic K)
    (x : (A.prod B).toFiniteBilinearModule.orthogonalComplement (H.prod K)) :
    orthogonalQuotientProdAddEquiv hH hK
        ((A.prod B).orthogonalQuotientMk (H.prod K)
          ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩) x) =
      (A.orthogonalQuotientMk H hH (FiniteBilinearModule.orthogonalComplementProdFst H K x),
        B.orthogonalQuotientMk K hK
          (FiniteBilinearModule.orthogonalComplementProdSnd H K x)) := by
  rw [orthogonalQuotientProdAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    (A.prod B).orthogonalQuotientUnderlyingEquiv_orthogonalQuotientMk]
  let x' : (A.toFiniteBilinearModule.prod B.toFiniteBilinearModule).orthogonalComplement
      (H.prod K) := by
    simpa only [A.prod_toFiniteBilinearModule B] using x
  have hx : (A.prod B).toFiniteBilinearModule.orthogonalQuotientMk (H.prod K) x =
      (A.toFiniteBilinearModule.prod B.toFiniteBilinearModule).orthogonalQuotientMk
        (H.prod K) x' := by
    rfl
  rw [hx]
  have hsplit :
      (FiniteBilinearModule.orthogonalQuotientProdIsometry
          (A := A.toFiniteBilinearModule) (B := B.toFiniteBilinearModule) H K).toAddEquiv
          ((A.toFiniteBilinearModule.prod B.toFiniteBilinearModule).orthogonalQuotientMk
            (H.prod K) x') =
        (A.toFiniteBilinearModule.orthogonalQuotientMk H
            (FiniteBilinearModule.orthogonalComplementProdFst H K x'),
          B.toFiniteBilinearModule.orthogonalQuotientMk K
            (FiniteBilinearModule.orthogonalComplementProdSnd H K x')) :=
    FiniteBilinearModule.orthogonalQuotientProdIsometry_orthogonalQuotientMk H K x'
  rw [hsplit]
  -- The final transport is the componentwise product of the two inverse underlying-quotient
  -- equivalences; expose its pointwise action before applying their representative formulas.
  change
    ((A.orthogonalQuotientUnderlyingEquiv H hH).symm
        (A.toFiniteBilinearModule.orthogonalQuotientMk H
          (FiniteBilinearModule.orthogonalComplementProdFst H K x')),
      (B.orthogonalQuotientUnderlyingEquiv K hK).symm
        (B.toFiniteBilinearModule.orthogonalQuotientMk K
          (FiniteBilinearModule.orthogonalComplementProdSnd H K x'))) = _
  rw [A.orthogonalQuotientUnderlyingEquiv_symm_orthogonalQuotientMk,
    B.orthogonalQuotientUnderlyingEquiv_symm_orthogonalQuotientMk]
  rfl

/-- **The quadratic orthogonal quotient of an orthogonal direct sum splits.** For
quadratic-isotropic subgroups `H ≤ A` and `K ≤ B`, the orthogonal quotient of `A ⊥ B` by the
quadratic-isotropic subgroup `H × K` is the orthogonal direct sum of the two orthogonal
quotients:

```text
(H × K)⊥ / (H × K) ≅ (H⊥ / H) ⊥ (K⊥ / K).
```

The underlying additive equivalence is `TauCeti.FiniteBilinearModule`'s splitting of the same
quotient; only the preservation of quadratic values is new. -/
noncomputable def orthogonalQuotientProdIsometry {H : AddSubgroup A} {K : AddSubgroup B}
    (hH : A.IsIsotropic H) (hK : B.IsIsotropic K) :
    Isometry
      ((A.prod B).orthogonalQuotient (H.prod K) ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩))
      ((A.orthogonalQuotient H hH).prod (B.orthogonalQuotient K hK)) where
  toLinearEquiv := (orthogonalQuotientProdAddEquiv hH hK).toIntLinearEquiv
  map_app' q := by
    induction q using orthogonalQuotient_induction_on with
    | mk x =>
      simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
      rw [orthogonalQuotientProdAddEquiv_orthogonalQuotientMk,
        prod_quadratic, A.orthogonalQuotient_quadratic_mk H hH,
        B.orthogonalQuotient_quadratic_mk K hK,
        (A.prod B).orthogonalQuotient_quadratic_mk (H.prod K)
          ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩) x,
        FiniteBilinearModule.coe_orthogonalComplementProdFst,
        FiniteBilinearModule.coe_orthogonalComplementProdSnd, prod_quadratic]

/-- **The splitting of a quadratic orthogonal quotient on representatives.** -/
@[simp]
theorem orthogonalQuotientProdIsometry_orthogonalQuotientMk {H : AddSubgroup A}
    {K : AddSubgroup B} (hH : A.IsIsotropic H) (hK : B.IsIsotropic K)
    (x : (A.prod B).toFiniteBilinearModule.orthogonalComplement (H.prod K)) :
    orthogonalQuotientProdIsometry hH hK
        ((A.prod B).orthogonalQuotientMk (H.prod K)
          ((A.isIsotropic_prod_iff B H K).mpr ⟨hH, hK⟩) x) =
      (A.orthogonalQuotientMk H hH (FiniteBilinearModule.orthogonalComplementProdFst H K x),
        B.orthogonalQuotientMk K hK
          (FiniteBilinearModule.orthogonalComplementProdSnd H K x)) :=
  orthogonalQuotientProdAddEquiv_orthogonalQuotientMk hH hK x

end FiniteQuadraticModule

end TauCeti
