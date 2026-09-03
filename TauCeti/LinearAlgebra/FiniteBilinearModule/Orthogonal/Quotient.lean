/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Complement

/-!
# Orthogonal quotients of finite bilinear modules

Let `A` be a finite bilinear module and let `H` be an additive subgroup of it.  The pairing of
`A` restricted to `H⊥` kills the vectors of `H` that lie in `H⊥`, so it descends to the quotient

```text
H⊥ / (H ∩ H⊥).
```

For an isotropic `H`, where `H ≤ H⊥`, this is the classical orthogonal quotient `H⊥ / H`.  The
construction itself needs no isotropy hypothesis, and is given here without one; isotropy is
assumed exactly in the two places where it is used, namely the squared-order corollary and the
Lagrangian criterion.

The results are the ones the gluing theory of integral lattices asks of this quotient.  It is
nondegenerate precisely when `H` swallows the radical of `A`, which for nondegenerate `A` is
automatic.  Its order is the index of `H ∩ H⊥` in `H⊥`, so for nondegenerate `A` and isotropic
`H` the double-complement cardinality identity `|H| |H⊥| = |A|` of
`TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Complement` turns into

```text
|H⊥ / H| · |H|² = |A|.
```

The quotient is trivial exactly when `H⊥ ≤ H`, hence — for isotropic `H` — exactly when `H` is
Lagrangian.  Read through the discriminant form of an integral lattice, that last statement is
the module-level form of "an overlattice glued along a Lagrangian subgroup is unimodular".

The quadratic refinement `TauCeti.FiniteQuadraticModule.orthogonalQuotient` of
`TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic` carries a quadratic map on the same
quotient group, and its underlying bilinear module is definitionally the construction of this
file; `TauCeti.FiniteQuadraticModule.orthogonalQuotient_toFiniteBilinearModule` records that
identification.

## Main declarations

* `TauCeti.FiniteBilinearModule.orthogonalQuotient`: the finite bilinear module induced on
  `H⊥ / (H ∩ H⊥)`.
* `TauCeti.FiniteBilinearModule.orthogonalQuotient_pairing_mk`: its pairing, on representatives.
* `TauCeti.FiniteBilinearModule.radical_orthogonalQuotient`: its radical, as the image of the
  restricted radical.
* `TauCeti.FiniteBilinearModule.isNondegenerate_orthogonalQuotient_iff`: it is nondegenerate
  exactly when `rad(A) ≤ H`.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_card_sq`: the order
  computation `|H⊥ / H| · |H|² = |A|`, for a nondegenerate module and an isotropic subgroup.
* `TauCeti.FiniteBilinearModule.card_orthogonalQuotient_eq_one_iff_isLagrangian`: the quotient of
  an isotropic subgroup is trivial exactly when that subgroup is Lagrangian.
* `TauCeti.FiniteBilinearModule.Isometry.orthogonalQuotientEquiv`: transport of orthogonal
  quotients along an isometry carrying one subgroup onto another.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u v

variable (A : FiniteBilinearModule.{u})

/-! ## The induced pairing on `H⊥ / (H ∩ H⊥)` -/

/-- **The orthogonal quotient of a finite bilinear module.**  The pairing of `A` is restricted to
`H⊥` and then divided by the part of `H` lying in `H⊥`, which is degenerate for the restricted
pairing by
`TauCeti.FiniteBilinearModule.addSubgroupOf_orthogonalComplement_le_radical_restrict`.

No isotropy hypothesis is needed: `H ∩ H⊥` is always killed by the restricted pairing.  When `H`
is isotropic, so that `H ≤ H⊥`, this is the classical `H⊥ / H`.

Exposed for the same reason as `quotientOfLeRadical`, on which it is built: so that its carrier
reduces to the `Submodule` quotient and maps out of it are definable with `Submodule.liftQ`,
`Submodule.mapQ` and `Submodule.Quotient.equiv`, and so that this package is definitionally the
underlying bilinear module of `TauCeti.FiniteQuadraticModule.orthogonalQuotient`. -/
@[expose] noncomputable def orthogonalQuotient (H : AddSubgroup A) : FiniteBilinearModule :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The quotient map from `H⊥` onto the orthogonal quotient. -/
noncomputable def orthogonalQuotientMk (H : AddSubgroup A) :
    A.orthogonalComplement H →+ A.orthogonalQuotient H :=
  quotientOfLeRadicalMk (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The orthogonal-quotient map sends an element to its quotient class. -/
theorem orthogonalQuotientMk_apply (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = Submodule.Quotient.mk x := by
  unfold orthogonalQuotientMk
  exact quotientOfLeRadicalMk_apply _ _ _ _

/-- The pairing of the orthogonal quotient is the pairing of `A` on representatives. -/
@[simp]
theorem orthogonalQuotient_pairing_mk (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    (A.orthogonalQuotient H).pairing (A.orthogonalQuotientMk H x)
      (A.orthogonalQuotientMk H y) = A.pairing x.1 y.1 :=
  quotientOfLeRadical_pairing_mk (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x y

/-- The quotient map onto the orthogonal quotient is surjective. -/
theorem orthogonalQuotientMk_surjective (H : AddSubgroup A) :
    Function.Surjective (A.orthogonalQuotientMk H) :=
  quotientOfLeRadicalMk_surjective (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- Every element of the orthogonal quotient is the class of an element of `H⊥`. -/
@[elab_as_elim]
theorem orthogonalQuotient_induction_on (H : AddSubgroup A)
    {motive : A.orthogonalQuotient H → Prop} (q : A.orthogonalQuotient H)
    (mk : ∀ x : A.orthogonalComplement H, motive (A.orthogonalQuotientMk H x)) : motive q := by
  obtain ⟨x, rfl⟩ := A.orthogonalQuotientMk_surjective H q
  exact mk x

/-- **The radical of the orthogonal quotient** is the image of the radical of the restricted
pairing. -/
@[simp]
theorem radical_orthogonalQuotient (H : AddSubgroup A) :
    (A.orthogonalQuotient H).radical =
      ((H ⊔ A.radical).addSubgroupOf (A.orthogonalComplement H)).map
        (A.orthogonalQuotientMk H) := by
  unfold orthogonalQuotient orthogonalQuotientMk
  rw [radical_quotientOfLeRadical, A.radical_restrict_orthogonalComplement]

/-- **The kernel of the quotient map** onto the orthogonal quotient is the part of `H` that lies
in `H⊥`. -/
@[simp]
theorem orthogonalQuotientMk_ker (H : AddSubgroup A) :
    (A.orthogonalQuotientMk H).ker = H.addSubgroupOf (A.orthogonalComplement H) :=
  quotientOfLeRadicalMk_ker (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- An element of `H⊥` has zero class in the orthogonal quotient exactly when it lies in `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_zero_iff (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = 0 ↔ (x : A) ∈ H :=
  quotientOfLeRadicalMk_eq_zero_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x

/-- Two elements of `H⊥` have the same class in the orthogonal quotient exactly when they differ
by an element of `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_iff (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = A.orthogonalQuotientMk H y ↔ (x : A) - y ∈ H :=
  quotientOfLeRadicalMk_eq_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x y

/-- Equal subgroups induce the same orthogonal quotient, up to the canonical isometry. -/
noncomputable def orthogonalQuotientCongr {H K : AddSubgroup A} (h : H = K) :
    Isometry (A.orthogonalQuotient H) (A.orthogonalQuotient K) := by
  subst h
  exact Isometry.refl _

/-- The canonical isometry between orthogonal quotients along equal subgroups is the identity on
representatives. -/
@[simp]
theorem orthogonalQuotientCongr_orthogonalQuotientMk {H K : AddSubgroup A} (h : H = K)
    (x : A.orthogonalComplement H) :
    A.orthogonalQuotientCongr h (A.orthogonalQuotientMk H x) =
      A.orthogonalQuotientMk K ⟨x.1, h ▸ x.2⟩ := by
  subst h
  simp only [orthogonalQuotientCongr, Isometry.refl_apply]

/-! ## Nondegeneracy -/

/-- **Nondegeneracy of the orthogonal quotient.** The quotient `H⊥ / (H ∩ H⊥)` is
nondegenerate exactly when `H` contains the radical of `A`.

Only the radical can survive: an element of `H⊥` orthogonal to all of `H⊥` lies in `H⊥⊥`, which
is `H` enlarged by the radical. -/
theorem isNondegenerate_orthogonalQuotient_iff (H : AddSubgroup A) :
    (A.orthogonalQuotient H).IsNondegenerate ↔ A.radical ≤ H := by
  have hiff := isNondegenerate_quotientOfLeRadical_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)
  rw [A.radical_restrict_orthogonalComplement] at hiff
  refine hiff.trans ⟨fun hle x hx ↦ ?_, fun hle ↦ ?_⟩
  · have hxperp : x ∈ A.orthogonalComplement H := by
      rw [A.mem_orthogonalComplement_iff]
      exact fun y _ ↦ (A.mem_radical_iff x).mp hx y
    exact hle (x := ⟨x, hxperp⟩) (AddSubgroup.mem_addSubgroupOf.mpr (AddSubgroup.mem_sup_right hx))
  · rw [sup_eq_left.mpr hle]

/-- The orthogonal quotient of a nondegenerate finite bilinear module is nondegenerate. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    (H : AddSubgroup A) : (A.orthogonalQuotient H).IsNondegenerate :=
  (A.isNondegenerate_orthogonalQuotient_iff H).mpr (hA.radical_eq_bot ▸ bot_le)

/-! ## Order -/

/-- The order of the orthogonal quotient is the index of `H ∩ H⊥` in `H⊥`. -/
theorem card_orthogonalQuotient (H : AddSubgroup A) :
    Nat.card (A.orthogonalQuotient H) = (H.addSubgroupOf (A.orthogonalComplement H)).index :=
  card_quotientOfLeRadical (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- **The general order formula for an orthogonal quotient.** In a nondegenerate finite bilinear
module, the orders of `H⊥ / (H ∩ H⊥)`, `H ∩ H⊥`, and `H` multiply to the order of the
ambient module. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_addSubgroupOf_mul_card
    (hA : A.IsNondegenerate) (H : AddSubgroup A) :
    Nat.card (A.orthogonalQuotient H) *
        Nat.card (H.addSubgroupOf (A.orthogonalComplement H)) * Nat.card H = Nat.card A := by
  rw [A.card_orthogonalQuotient H,
    (H.addSubgroupOf (A.orthogonalComplement H)).index_mul_card, mul_comm]
  exact IsNondegenerate.card_mul_card_orthogonalComplement A hA H

/-- **The order of the orthogonal quotient of an isotropic subgroup.**  In a nondegenerate finite
bilinear module, `|H⊥ / H| · |H|² = |A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_sq (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) * Nat.card H ^ 2 = Nat.card A := by
  have hle : H ≤ A.orthogonalComplement H := (A.isIsotropic_iff_le_orthogonalComplement H).mp hH
  have hcard : Nat.card (H.addSubgroupOf (A.orthogonalComplement H)) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  simpa only [hcard, pow_two, mul_assoc] using
    (IsNondegenerate.card_orthogonalQuotient_mul_card_addSubgroupOf_mul_card A hA H)

/-! ## The Lagrangian criterion -/

/-- The orthogonal quotient is trivial exactly when `H⊥` is contained in `H`.  No hypothesis on
`A` or on `H` is needed. -/
theorem card_orthogonalQuotient_eq_one_iff (H : AddSubgroup A) :
    Nat.card (A.orthogonalQuotient H) = 1 ↔ A.orthogonalComplement H ≤ H := by
  rw [A.card_orthogonalQuotient H, AddSubgroup.index_eq_one, AddSubgroup.addSubgroupOf_eq_top]

/-- **The Lagrangian criterion.**  The orthogonal quotient of an isotropic subgroup is trivial
exactly when that subgroup is Lagrangian. -/
theorem card_orthogonalQuotient_eq_one_iff_isLagrangian {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) = 1 ↔ A.IsLagrangian H := by
  rw [A.card_orthogonalQuotient_eq_one_iff H, A.isLagrangian_def H]
  exact ⟨fun h ↦ le_antisymm ((A.isIsotropic_iff_le_orthogonalComplement H).mp hH) h,
    fun h ↦ h ▸ le_rfl⟩

/-! ## Transport along isometries -/

namespace Isometry

variable {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}

/-- An isometry maps the part of `H` in `H⊥` onto the part of its image in the corresponding
orthogonal complement. -/
private theorem map_toIntSubmodule_addSubgroupOf_orthogonalComplement
    (f : Isometry A B) (H : AddSubgroup A) :
    (H.addSubgroupOf (A.orthogonalComplement H)).toIntSubmodule.map
        ((Isometry.orthogonalComplementEquiv A f H).toIntLinearEquiv :
          A.orthogonalComplement H →ₗ[ℤ]
            B.orthogonalComplement (H.map f.toAddEquiv)) =
      ((H.map f.toAddEquiv).addSubgroupOf
        (B.orthogonalComplement (H.map f.toAddEquiv))).toIntSubmodule := by
  ext y
  rw [Submodule.mem_map_equiv]
  -- `mem_map_equiv` exposes membership in the underlying `ℤ`-submodules; normalize those
  -- coercions to the corresponding `AddSubgroup.addSubgroupOf` memberships so its public lemma
  -- and the representative formula for `orthogonalComplementEquiv` can be used.
  change (Isometry.orthogonalComplementEquiv A f H).symm y ∈
      H.addSubgroupOf (A.orthogonalComplement H) ↔
    y ∈ (H.map f.toAddEquiv).addSubgroupOf
      (B.orthogonalComplement (H.map f.toAddEquiv))
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf,
    Isometry.coe_orthogonalComplementEquiv_symm_apply A f H]
  constructor
  · intro hy
    exact ⟨f.symm (y : B), hy, f.apply_symm_apply (y : B)⟩
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    rw [← Isometry.coe_toAddEquiv (f := f.symm), Isometry.symm_toAddEquiv]
    -- The preceding isometry lemmas leave an application through the induced `AddEquiv`; expose
    -- it explicitly so the standard inverse/application cancellation lemma matches.
    change f.toAddEquiv.symm (f.toAddEquiv x) ∈ H
    rw [f.toAddEquiv.symm_apply_apply]
    exact hx

/-- The additive equivalence of orthogonal quotients when the target subgroup is exactly the
image. -/
private noncomputable def orthogonalQuotientAddEquiv (f : Isometry A B) (H : AddSubgroup A) :
    A.orthogonalQuotient H ≃+ B.orthogonalQuotient (H.map f.toAddEquiv) :=
  (Submodule.Quotient.equiv _ _
    (Isometry.orthogonalComplementEquiv A f H).toIntLinearEquiv
    (map_toIntSubmodule_addSubgroupOf_orthogonalComplement f H)).toAddEquiv

/-- The image-subgroup additive equivalence sends the class of `x ∈ H⊥` to the class of
`f x`. -/
@[simp]
private theorem orthogonalQuotientAddEquiv_orthogonalQuotientMk (f : Isometry A B)
    (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    f.orthogonalQuotientAddEquiv H (A.orthogonalQuotientMk H x) =
      B.orthogonalQuotientMk (H.map f.toAddEquiv)
        (Isometry.orthogonalComplementEquiv A f H x) := by
  have hx : A.orthogonalQuotientMk H x =
      (Submodule.Quotient.mk x : A.orthogonalQuotient H) := by
    unfold orthogonalQuotientMk
    exact quotientOfLeRadicalMk_apply _ _ _ _
  have hfx : B.orthogonalQuotientMk (H.map f.toAddEquiv)
      (Isometry.orthogonalComplementEquiv A f H x) =
      (Submodule.Quotient.mk (Isometry.orthogonalComplementEquiv A f H x) :
        B.orthogonalQuotient (H.map f.toAddEquiv)) := by
    unfold orthogonalQuotientMk
    exact quotientOfLeRadicalMk_apply _ _ _ _
  rw [hx, hfx]
  -- After replacing the packaged quotient constructors by `Submodule.Quotient.mk`, expose the
  -- underlying quotient equivalence so Mathlib's `equiv_apply` and `mapQ_apply` lemmas match.
  change (Submodule.Quotient.equiv _ _
      (Isometry.orthogonalComplementEquiv A f H).toIntLinearEquiv
      (map_toIntSubmodule_addSubgroupOf_orthogonalComplement f H))
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  congr 1

/-- The isometry of orthogonal quotients when the target subgroup is exactly the image. -/
private noncomputable def orthogonalQuotientMap (f : Isometry A B) (H : AddSubgroup A) :
    Isometry (A.orthogonalQuotient H) (B.orthogonalQuotient (H.map f.toAddEquiv)) where
  toAddEquiv := f.orthogonalQuotientAddEquiv H
  map_pairing' q r := by
    induction q using orthogonalQuotient_induction_on with
    | mk x =>
      induction r using orthogonalQuotient_induction_on with
      | mk y =>
        rw [orthogonalQuotientAddEquiv_orthogonalQuotientMk,
          orthogonalQuotientAddEquiv_orthogonalQuotientMk,
          B.orthogonalQuotient_pairing_mk, A.orthogonalQuotient_pairing_mk,
          Isometry.coe_orthogonalComplementEquiv_apply A f H,
          Isometry.coe_orthogonalComplementEquiv_apply A f H,
          f.map_pairing]

/-- The image-subgroup transport sends the class of `x ∈ H⊥` to the class of `f x`. -/
@[simp]
private theorem orthogonalQuotientMap_orthogonalQuotientMk (f : Isometry A B)
    (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    f.orthogonalQuotientMap H (A.orthogonalQuotientMk H x) =
      B.orthogonalQuotientMk (H.map f.toAddEquiv)
        (Isometry.orthogonalComplementEquiv A f H x) := by
  rw [orthogonalQuotientMap]
  exact orthogonalQuotientAddEquiv_orthogonalQuotientMk f H x

/-- **Transport of an orthogonal quotient along an isometry.** An isometry `f : A ≅ B` carrying
`H` onto `K` induces an isometry `H⊥ / (H ∩ H⊥) ≅ K⊥ / (K ∩ K⊥)`. -/
noncomputable def orthogonalQuotientEquiv (f : Isometry A B) {H : AddSubgroup A}
    {K : AddSubgroup B} (h : H.map f.toAddEquiv = K) :
    Isometry (A.orthogonalQuotient H) (B.orthogonalQuotient K) :=
  (f.orthogonalQuotientMap H).trans (B.orthogonalQuotientCongr h)

/-- **The representative formula for a transported orthogonal quotient.** The transported
isometry sends the class of `x ∈ H⊥` to the class of `f x ∈ K⊥`. -/
@[simp]
theorem orthogonalQuotientEquiv_orthogonalQuotientMk (f : Isometry A B)
    {H : AddSubgroup A} {K : AddSubgroup B} (h : H.map f.toAddEquiv = K)
    (x : A.orthogonalComplement H) :
    f.orthogonalQuotientEquiv h (A.orthogonalQuotientMk H x) =
      B.orthogonalQuotientMk K
        ⟨f (x : A), Isometry.map_mem_orthogonalComplement_of_map_eq A f h x.2⟩ := by
  rw [orthogonalQuotientEquiv, trans_apply, orthogonalQuotientMap_orthogonalQuotientMk,
    B.orthogonalQuotientCongr_orthogonalQuotientMk]
  apply congrArg (B.orthogonalQuotientMk K)
  exact Subtype.ext (Isometry.coe_orthogonalComplementEquiv_apply A f H x)

/-- **The inverse representative formula for a transported orthogonal quotient.** The inverse
transport sends the class of `y ∈ K⊥` to the class of `f⁻¹ y ∈ H⊥`. -/
@[simp]
theorem orthogonalQuotientEquiv_symm_orthogonalQuotientMk (f : Isometry A B)
    {H : AddSubgroup A} {K : AddSubgroup B} (h : H.map f.toAddEquiv = K)
    (y : B.orthogonalComplement K) :
    (f.orthogonalQuotientEquiv h).symm (B.orthogonalQuotientMk K y) =
      A.orthogonalQuotientMk H
        ⟨f.symm (y : B), by
          rw [A.mem_orthogonalComplement_iff]
          intro x hx
          rw [← f.map_pairing, f.apply_symm_apply]
          exact (B.mem_orthogonalComplement_iff K (y : B)).mp y.2 (f x)
            (h ▸ ⟨x, hx, rfl⟩)⟩ := by
  have hforward :
      f.orthogonalQuotientEquiv h
          (A.orthogonalQuotientMk H ⟨f.symm (y : B), by
            rw [A.mem_orthogonalComplement_iff]
            intro x hx
            rw [← f.map_pairing, f.apply_symm_apply]
            exact (B.mem_orthogonalComplement_iff K (y : B)).mp y.2 (f x)
              (h ▸ ⟨x, hx, rfl⟩)⟩) =
        B.orthogonalQuotientMk K y := by
    rw [orthogonalQuotientEquiv_orthogonalQuotientMk]
    apply congrArg (B.orthogonalQuotientMk K)
    exact Subtype.ext (f.apply_symm_apply (y : B))
  rw [← hforward, (f.orthogonalQuotientEquiv h).symm_apply_apply]

end Isometry

end TauCeti.FiniteBilinearModule
