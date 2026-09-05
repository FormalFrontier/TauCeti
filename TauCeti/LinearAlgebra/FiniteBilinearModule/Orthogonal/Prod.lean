/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

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
(H × K)⊥ / (H × K) ≅ (H⊥ / H) ⊥ (K⊥ / K).
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
  `(H × K)⊥ / (H × K) ≅ (H⊥ / H) ⊥ (K⊥ / K)`.
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

/-- Two product subgroups of a product group are equal exactly when their factors are. -/
private theorem prod_eq_prod_iff {H H' : AddSubgroup A} {K K' : AddSubgroup B} :
    H.prod K = H'.prod K' ↔ H = H' ∧ K = K' := by
  constructor
  · intro h
    refine ⟨AddSubgroup.ext fun x ↦ ?_, AddSubgroup.ext fun y ↦ ?_⟩
    · have hx : (x, (0 : B.carrier)) ∈ H.prod K ↔ (x, (0 : B.carrier)) ∈ H'.prod K' := by
        rw [h]
      simpa only [AddSubgroup.mem_prod, K.zero_mem, K'.zero_mem, and_true] using hx
    · have hy : ((0 : A.carrier), y) ∈ H.prod K ↔ ((0 : A.carrier), y) ∈ H'.prod K' := by
        rw [h]
      simpa only [AddSubgroup.mem_prod, H.zero_mem, H'.zero_mem, true_and] using hy
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The Lagrangian condition on a product subgroup is componentwise.** -/
@[simp]
theorem isLagrangian_prod_iff (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).IsLagrangian (H.prod K) ↔ A.IsLagrangian H ∧ B.IsLagrangian K := by
  rw [(A.prod B).isLagrangian_def, A.isLagrangian_def, B.isLagrangian_def,
    A.orthogonalComplement_prod B, A.prod_eq_prod_iff B]

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

/-- The map splitting the orthogonal quotient of `A ⊥ B` by a product subgroup into the two
orthogonal quotients, as a `ℤ`-linear map. -/
private noncomputable def orthogonalQuotientProdMap (H : AddSubgroup A) (K : AddSubgroup B) :
    (A.prod B).orthogonalQuotient (H.prod K) →ₗ[ℤ]
      (A.orthogonalQuotient H).carrier × (B.orthogonalQuotient K).carrier :=
  Submodule.liftQ
    ((H.prod K).addSubgroupOf ((A.prod B).orthogonalComplement (H.prod K))).toIntSubmodule
    (((A.orthogonalQuotientMk H).comp (orthogonalComplementProdFst H K)).prod
      ((B.orthogonalQuotientMk K).comp (orthogonalComplementProdSnd H K))).toIntLinearMap
    (by
      intro x hx
      have hx' : (x : A.carrier × B.carrier) ∈ H.prod K := hx
      rw [AddSubgroup.mem_prod] at hx'
      rw [LinearMap.mem_ker]
      refine Prod.ext ?_ ?_
      · exact (A.orthogonalQuotientMk_eq_zero_iff H _).mpr hx'.1
      · exact (B.orthogonalQuotientMk_eq_zero_iff K _).mpr hx'.2)

@[simp]
private theorem orthogonalQuotientProdMap_orthogonalQuotientMk (H : AddSubgroup A)
    (K : AddSubgroup B) (x : (A.prod B).orthogonalComplement (H.prod K)) :
    orthogonalQuotientProdMap H K ((A.prod B).orthogonalQuotientMk (H.prod K) x) =
      (A.orthogonalQuotientMk H (orthogonalComplementProdFst H K x),
        B.orthogonalQuotientMk K (orthogonalComplementProdSnd H K x)) := by
  rw [(A.prod B).orthogonalQuotientMk_apply, orthogonalQuotientProdMap]
  exact Submodule.liftQ_apply _ _ x

private theorem orthogonalQuotientProdMap_bijective (H : AddSubgroup A) (K : AddSubgroup B) :
    Function.Bijective (orthogonalQuotientProdMap H K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using orthogonalQuotient_induction_on with
    | mk x =>
      rw [orthogonalQuotientProdMap_orthogonalQuotientMk] at hz
      rw [(A.prod B).orthogonalQuotientMk_eq_zero_iff, AddSubgroup.mem_prod]
      exact ⟨(A.orthogonalQuotientMk_eq_zero_iff H _).mp (congrArg Prod.fst hz),
        (B.orthogonalQuotientMk_eq_zero_iff K _).mp (congrArg Prod.snd hz)⟩
  · rintro ⟨p, q⟩
    obtain ⟨y, rfl⟩ := A.orthogonalQuotientMk_surjective H p
    obtain ⟨z, rfl⟩ := B.orthogonalQuotientMk_surjective K q
    refine ⟨(A.prod B).orthogonalQuotientMk (H.prod K)
      ⟨((y : A), (z : B)), (A.mem_orthogonalComplement_prod_iff B H K _).mpr ⟨y.2, z.2⟩⟩, ?_⟩
    rw [orthogonalQuotientProdMap_orthogonalQuotientMk]
    exact Prod.ext
      (congrArg (A.orthogonalQuotientMk H)
        (Subtype.ext (coe_orthogonalComplementProdFst H K _)))
      (congrArg (B.orthogonalQuotientMk K)
        (Subtype.ext (coe_orthogonalComplementProdSnd H K _)))

/-- **The orthogonal quotient of an orthogonal direct sum splits.** For subgroups `H ≤ A` and
`K ≤ B`, the orthogonal quotient of `A ⊥ B` by `H × K` is the orthogonal direct sum of the two
orthogonal quotients:

```text
(H × K)⊥ / (H × K) ≅ (H⊥ / H) ⊥ (K⊥ / K).
```

No isotropy hypothesis is needed, exactly as for the orthogonal quotient itself. -/
noncomputable def orthogonalQuotientProdIsometry (H : AddSubgroup A) (K : AddSubgroup B) :
    Isometry ((A.prod B).orthogonalQuotient (H.prod K))
      ((A.orthogonalQuotient H).prod (B.orthogonalQuotient K)) where
  toAddEquiv := AddEquiv.ofBijective (orthogonalQuotientProdMap H K).toAddMonoidHom
    (orthogonalQuotientProdMap_bijective H K)
  map_pairing' q r := by
    induction q using orthogonalQuotient_induction_on with
    | mk x =>
      induction r using orthogonalQuotient_induction_on with
      | mk y =>
        -- `AddEquiv.ofBijective` has no `coe` simp lemma, so name the underlying linear map
        -- explicitly; the two are the same function by definition.
        change ((A.orthogonalQuotient H).prod (B.orthogonalQuotient K)).pairing
            (orthogonalQuotientProdMap H K _) (orthogonalQuotientProdMap H K _) = _
        rw [orthogonalQuotientProdMap_orthogonalQuotientMk,
          orthogonalQuotientProdMap_orthogonalQuotientMk, prod_pairing,
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
  orthogonalQuotientProdMap_orthogonalQuotientMk H K x

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
  (FiniteBilinearModule.orthogonalQuotientProdIsometry (A := A.toFiniteBilinearModule)
    (B := B.toFiniteBilinearModule) H K).toAddEquiv

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
  rw [(A.prod B).orthogonalQuotientMk_apply, A.orthogonalQuotientMk_apply,
    B.orthogonalQuotientMk_apply]
  have h := FiniteBilinearModule.orthogonalQuotientProdIsometry_orthogonalQuotientMk
    (A := A.toFiniteBilinearModule) (B := B.toFiniteBilinearModule) H K x
  rwa [FiniteBilinearModule.orthogonalQuotientMk_apply,
    FiniteBilinearModule.orthogonalQuotientMk_apply,
    FiniteBilinearModule.orthogonalQuotientMk_apply] at h

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
