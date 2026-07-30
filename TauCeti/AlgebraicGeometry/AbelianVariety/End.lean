/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Int.Cast.Lemmas

/-!
# The endomorphism ring of an abelian variety

The endomorphisms of an abelian variety `A` over a field `K` form a ring: addition is the
pointwise group law of `A`, multiplication is composition. This file constructs that ring and the
multiplication-by-`n` endomorphism `[n] : A ⟶ A` as the image of `n : ℤ` in it.

The pointwise group law on homomorphisms of abelian varieties is written *multiplicatively* in
`TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup`, matching the multiplicative encoding
(`GrpObj`, `μ`, `η`, `ι`) of a group object. A ring is written additively, so the endomorphism ring
is the additive reindexing `Additive (A ⟶ A)` of that group rather than the hom-set itself; this
keeps the multiplicative convention on all hom-sets intact. (Declaring `AbelianVariety K`
`CategoryTheory.Preadditive` instead would replace that convention by an additive one on every
hom-set, which is a separate change.) `AbelianVariety.End.toHom` and `AbelianVariety.End.ofHom`
translate between the two views, and the `toHom_*` lemmas turn every ring operation into a group or
categorical operation on morphisms.

* `AbelianVariety.End A`: the endomorphism ring, with `AbelianVariety.End.instRing`;
* `AbelianVariety.mulBy A n`: the endomorphism `[n]`, with `AbelianVariety.mulBy_eq_zpow`
  identifying it with the `n`-th power map and `AbelianVariety.mulBy_comp` recording that every
  homomorphism of abelian varieties commutes with it;
* `AbelianVariety.End.congr`: an isomorphism of abelian varieties conjugates one endomorphism ring
  isomorphically onto the other;
* `AbelianVariety.End.instUniqueTrivial`: the trivial abelian variety has the zero ring as its
  endomorphism ring, so `[n]` there is the identity for every `n`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", and its item "`[n]` as an
isogeny" — the endomorphism ring is where `[n]` lives, and where the homomorphism produced by
Layer F's universal property of the Abel–Jacobi map is compared with others. That `[n]` *is* an
isogeny needs the dimension and torsion theory of Layer E and is not proved here. No external
mathematics is vendored; the ring is assembled from Tau Ceti's homomorphism-group API and
Mathlib's `Additive` type synonym, following the shape of Mathlib's
`CategoryTheory.End` monoid and its `Ring` instance for preadditive categories.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

open scoped Hom

variable {K : Type u} [Field K]

/-- The endomorphism ring of an abelian variety `A`: the endomorphisms of `A`, with addition the
pointwise group law of `A` and multiplication composition.

Since the pointwise group law on `A ⟶ A` is written multiplicatively (see
`AbelianVariety.Hom.instCommGroup`) while a ring is written additively, this is the additive
reindexing of the group `A ⟶ A`; use `AbelianVariety.End.toHom` and `AbelianVariety.End.ofHom` to
pass between an element of the ring and the endomorphism it denotes. -/
def End (A : AbelianVariety K) : Type u := Additive (A ⟶ A)

namespace End

variable {A B C : AbelianVariety K}

noncomputable section

/-- The endomorphism of `A` denoted by an element of the endomorphism ring `End A`. -/
def toHom (x : End A) : A ⟶ A := Additive.toMul x

/-- An endomorphism of `A`, viewed as an element of the endomorphism ring `End A`. -/
def ofHom (f : A ⟶ A) : End A := Additive.ofMul f

@[simp] lemma toHom_ofHom (f : A ⟶ A) : toHom (ofHom f) = f := (rfl)

@[simp] lemma ofHom_toHom (x : End A) : ofHom (toHom x) = x := (rfl)

lemma toHom_injective : Function.Injective (toHom : End A → (A ⟶ A)) := fun x y h => by
  rw [← ofHom_toHom x, ← ofHom_toHom y, h]

@[ext] lemma ext {x y : End A} (h : toHom x = toHom y) : x = y := toHom_injective h

@[simp] lemma toHom_inj {x y : End A} : toHom x = toHom y ↔ x = y := toHom_injective.eq_iff

/-! ### The additive group

Addition in `End A` is the pointwise group law of the target, so each additive operation
translates into the corresponding multiplicative one on morphisms. -/

instance instAddCommGroup (A : AbelianVariety K) : AddCommGroup (End A) :=
  inferInstanceAs (AddCommGroup (Additive (A ⟶ A)))

@[simp] lemma toHom_zero : toHom (0 : End A) = 1 := _root_.toMul_zero

@[simp] lemma toHom_add (x y : End A) : toHom (x + y) = toHom x * toHom y :=
  _root_.toMul_add x y

@[simp] lemma toHom_neg (x : End A) : toHom (-x) = (toHom x)⁻¹ := _root_.toMul_neg x

@[simp] lemma toHom_sub (x y : End A) : toHom (x - y) = toHom x / toHom y :=
  _root_.toMul_sub x y

/-! The two scalar-multiplication lemmas are deliberately not `@[simp]`, unlike the rest of this
section: `simp` rewrites a scalar multiple in a ring to a product (`nsmul_eq_mul`, `zsmul_eq_mul`),
so their left-hand sides are not in `simp` normal form. Use `AbelianVariety.End.toHom_natCast` or
`AbelianVariety.End.toHom_intCast` together with `AbelianVariety.End.toHom_mul` instead. -/

lemma toHom_nsmul (n : ℕ) (x : End A) : toHom (n • x) = toHom x ^ n :=
  _root_.toMul_nsmul n x

lemma toHom_zsmul (n : ℤ) (x : End A) : toHom (n • x) = toHom x ^ n :=
  _root_.toMul_zsmul n x

/-! ### The multiplicative monoid

Multiplication in `End A` is composition, in the order of `Function.comp` rather than of
`CategoryTheory.CategoryStruct.comp`, matching Mathlib's `CategoryTheory.End`. -/

instance instOne (A : AbelianVariety K) : One (End A) := ⟨ofHom (𝟙 A)⟩

instance instMul (A : AbelianVariety K) : Mul (End A) :=
  ⟨fun x y => ofHom (toHom y ≫ toHom x)⟩

@[simp] lemma toHom_one : toHom (1 : End A) = 𝟙 A := (rfl)

@[simp] lemma toHom_mul (x y : End A) : toHom (x * y) = toHom y ≫ toHom x := (rfl)

/-- Composing two endomorphisms is multiplying them in the endomorphism ring, in the reversed
order. -/
lemma ofHom_comp (f g : A ⟶ A) : ofHom (f ≫ g) = ofHom g * ofHom f := (rfl)

instance instMonoid (A : AbelianVariety K) : Monoid (End A) where
  mul_assoc x y z := by ext; simp
  one_mul x := by ext; simp
  mul_one x := by ext; simp

/-! ### The ring

Composition of homomorphisms of abelian varieties is bimultiplicative for the pointwise group law
(`AbelianVariety.Hom.mul_comp` and `AbelianVariety.Hom.comp_mul`), which is exactly
distributivity of multiplication over addition in `End A`. -/

instance instSemiring (A : AbelianVariety K) : Semiring (End A) :=
  { instMonoid A with
    zero_mul := fun x => by ext; simp
    mul_zero := fun x => by ext; simp
    left_distrib := fun x y z => by ext; simp
    right_distrib := fun x y z => by ext; simp }

instance instRing (A : AbelianVariety K) : Ring (End A) :=
  { instSemiring A, instAddCommGroup A with
    neg_add_cancel := neg_add_cancel }

/-- The natural number `n` acts in the endomorphism ring as the `n`-th power of the identity for
the pointwise group law. -/
lemma toHom_natCast (n : ℕ) : toHom (n : End A) = 𝟙 A ^ n := by
  have hn : (n : End A) = n • (1 : End A) := by rw [nsmul_eq_mul, mul_one]
  rw [hn, toHom_nsmul, toHom_one]

/-- The integer `n` acts in the endomorphism ring as the `n`-th power of the identity for the
pointwise group law. -/
lemma toHom_intCast (n : ℤ) : toHom (n : End A) = 𝟙 A ^ n := by
  have hn : (n : End A) = n • (1 : End A) := by rw [zsmul_eq_mul, mul_one]
  rw [hn, toHom_zsmul, toHom_one]

/-! ### Transport along an isomorphism -/

/-- Conjugation by an isomorphism `e : A ≅ B` of abelian varieties, as an isomorphism of
endomorphism rings `End A ≃+* End B`. -/
def congr (e : A ≅ B) : End A ≃+* End B where
  toFun x := ofHom (e.inv ≫ toHom x ≫ e.hom)
  invFun y := ofHom (e.hom ≫ toHom y ≫ e.inv)
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

@[simp] lemma toHom_congr (e : A ≅ B) (x : End A) :
    toHom (congr e x) = e.inv ≫ toHom x ≫ e.hom :=
  (rfl)

@[simp] lemma toHom_congr_symm (e : A ≅ B) (y : End B) :
    toHom ((congr e).symm y) = e.hom ≫ toHom y ≫ e.inv :=
  (rfl)

@[simp] lemma congr_refl (A : AbelianVariety K) :
    congr (Iso.refl A) = RingEquiv.refl (End A) := by
  ext x
  simp

lemma congr_trans (e : A ≅ B) (f : B ≅ C) :
    congr (e.trans f) = (congr e).trans (congr f) := by
  ext x
  simp

/-! ### The trivial abelian variety -/

/-- The trivial abelian variety has a unique endomorphism, so its endomorphism ring is the zero
ring. -/
instance instUniqueTrivial : Unique (End (trivial K)) :=
  inferInstanceAs (Unique (Additive (trivial K ⟶ trivial K)))

end

end End

noncomputable section

/-- The multiplication-by-`n` endomorphism `[n] : A ⟶ A` of an abelian variety, that is, the image
of `n : ℤ` in the endomorphism ring `AbelianVariety.End A`.

The name is the standard one for abelian varieties, whose group law is conventionally written
additively. Here the group law on morphisms is written multiplicatively, so `[n]` is concretely the
`n`-th power map for that law: see `AbelianVariety.mulBy_eq_zpow`. -/
def mulBy (A : AbelianVariety K) (n : ℤ) : A ⟶ A := End.toHom (n : End A)

variable {A B : AbelianVariety K}

/-- `[n]` is the `n`-th power map for the pointwise group law on endomorphisms. -/
lemma mulBy_eq_zpow (A : AbelianVariety K) (n : ℤ) : mulBy A n = 𝟙 A ^ n :=
  End.toHom_intCast n

/-- `[0]` is the constant endomorphism through the unit section, the identity of the pointwise
group law. -/
@[simp] lemma mulBy_zero (A : AbelianVariety K) : mulBy A 0 = 1 := by
  simp [mulBy]

/-- `[1]` is the identity. -/
@[simp] lemma mulBy_one (A : AbelianVariety K) : mulBy A 1 = 𝟙 A := by
  simp [mulBy]

lemma mulBy_add (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m + n) = mulBy A m * mulBy A n := by
  simp [mulBy]

@[simp] lemma mulBy_neg (A : AbelianVariety K) (n : ℤ) : mulBy A (-n) = (mulBy A n)⁻¹ := by
  simp [mulBy]

lemma mulBy_sub (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m - n) = mulBy A m / mulBy A n := by
  simp [mulBy]

/-- `[m * n]` is `[m]` composed with `[n]`. -/
lemma mulBy_mul (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m * n) = mulBy A n ≫ mulBy A m := by
  simp [mulBy]

/-- Every homomorphism of abelian varieties commutes with multiplication by `n`. -/
lemma mulBy_comp (n : ℤ) (f : A ⟶ B) : mulBy A n ≫ f = f ≫ mulBy B n := by
  rw [mulBy_eq_zpow, mulBy_eq_zpow, Hom.zpow_comp, Hom.comp_zpow, Category.id_comp,
    Category.comp_id]

/-- Conjugating `[n]` by an isomorphism of abelian varieties gives `[n]`. -/
@[simp] lemma congr_ofHom_mulBy (e : A ≅ B) (n : ℤ) :
    End.congr e (End.ofHom (mulBy A n)) = End.ofHom (mulBy B n) := by
  ext
  rw [End.toHom_congr, End.toHom_ofHom, End.toHom_ofHom, mulBy_comp, Iso.inv_hom_id_assoc]

/-- Every endomorphism of the trivial abelian variety, in particular every `[n]`, is the
identity. -/
@[simp] lemma mulBy_trivial (n : ℤ) :
    mulBy (trivial K) n = 𝟙 (trivial K) := by
  rw [← mulBy_one (trivial K)]
  exact congrArg End.toHom (Subsingleton.elim _ _)

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
