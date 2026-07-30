/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Conj
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
`CategoryTheory.Preadditive` instead would put an `AddCommGroup (A ⟶ B)` on the very hom-sets that
already carry `AbelianVariety.Hom.instCommGroup` for the same operation — the situation `Additive`
exists to avoid — and would mean re-deriving that group law additively rather than transporting
Mathlib's multiplicative `CategoryTheory.MonObj.Hom.commGroup`; that is a change to already-merged
material, not part of this file.) Reindexing only the additive structure leaves `End A` the same
type as Mathlib's `CategoryTheory.End A`, so the multiplicative monoid here *is* Mathlib's, and
conjugation by an isomorphism is Mathlib's `CategoryTheory.Iso.conj`.
`AbelianVariety.End.toHom` and `AbelianVariety.End.ofHom` translate between the two views, and the
`toHom_*` lemmas turn every ring operation into a group or categorical operation on morphisms.

* `AbelianVariety.End A`: the endomorphism ring, with `AbelianVariety.End.instRing`, and
  `AbelianVariety.End.instUnique` recognizing it as the zero ring when `A` has one endomorphism;
* `AbelianVariety.mulBy A n`: the endomorphism `[n]`, with `AbelianVariety.mulBy_eq_zpow`
  identifying it with the `n`-th power map and `AbelianVariety.mulBy_comp` recording that every
  homomorphism of abelian varieties commutes with it;
* `AbelianVariety.End.congr`: an isomorphism of abelian varieties conjugates one endomorphism ring
  isomorphically onto the other.

The specialization to the trivial abelian variety is in
`TauCeti.AlgebraicGeometry.AbelianVariety.End.Trivial`, which is where the trivial-variety theory
gets imported.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", and its item "`[n]` as an
isogeny" — the endomorphism ring is where `[n]` lives, and where the homomorphism produced by
Layer F's universal property of the Abel–Jacobi map is compared with others. That `[n]` *is* an
isogeny needs the dimension and torsion theory of Layer E and is not proved here. No external
mathematics is vendored; the ring is assembled from Tau Ceti's homomorphism-group API, Mathlib's
`Additive` type synonym, Mathlib's `CategoryTheory.End` monoid and `CategoryTheory.Iso.conj`, with
only the distributivity supplied by `AbelianVariety.Hom.mul_comp` and `AbelianVariety.Hom.comp_mul`
proved here — the same assembly as Mathlib's `Ring (CategoryTheory.End X)` for preadditive
categories.
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
`CategoryTheory.CategoryStruct.comp`. Since `End A` reindexes only the *additive* structure of
`A ⟶ A`, it is the same type as Mathlib's `CategoryTheory.End A`, so the multiplicative monoid is
Mathlib's `CategoryTheory.End.monoid` rather than a new one. -/

instance instMonoid (A : AbelianVariety K) : Monoid (End A) :=
  inferInstanceAs (Monoid (CategoryTheory.End A))

@[simp] lemma toHom_one : toHom (1 : End A) = 𝟙 A := (rfl)

@[simp] lemma toHom_mul (x y : End A) : toHom (x * y) = toHom y ≫ toHom x := (rfl)

/-- Composing two endomorphisms is multiplying them in the endomorphism ring, in the reversed
order. -/
lemma ofHom_comp (f g : A ⟶ A) : ofHom (f ≫ g) = ofHom g * ofHom f := (rfl)

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

/-- An abelian variety with only one endomorphism has the zero ring as its endomorphism ring.

This is Mathlib's `Unique (Additive α)` instance; it is stated here, rather than reproved wherever a
hom-set is known to be a singleton, because unfolding `End A` to `Additive (A ⟶ A)` is only possible
in this module. -/
instance instUnique [Unique (A ⟶ A)] : Unique (End A) :=
  inferInstanceAs (Unique (Additive (A ⟶ A)))

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
endomorphism rings `End A ≃+* End B`.

The multiplicative part is Mathlib's `CategoryTheory.Iso.conj`; only additivity — that conjugation
respects the pointwise group law — has to be proved here. -/
def congr (e : A ≅ B) : End A ≃+* End B where
  __ := e.conj
  -- Mathlib's `e.conj` lives on `CategoryTheory.End`, of which `End A` is the definitional
  -- synonym `Additive (A ⟶ A)`, so the `map_add'` goal mixes the two views: it applies `e.conj` to
  -- elements of `End A` and takes `toHom` of a categorical composite. That mismatch cannot be
  -- bridged by a rewrite lemma, because a statement about `toHom (e.conj x)` for `x : End A` does
  -- not elaborate: the coercion of `e.conj` fixes its argument type to `CategoryTheory.End A`.
  -- So the goal is moved into the morphism view once, definitionally, and `simp` closes it from
  -- `Hom.mul_comp` and `Hom.comp_mul`.
  map_add' x y := toHom_injective <| by
    change e.inv ≫ toHom (x + y) ≫ e.hom
      = (e.inv ≫ toHom x ≫ e.hom) * (e.inv ≫ toHom y ≫ e.hom)
    simp

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

end

end End

noncomputable section

/-- The multiplication-by-`n` endomorphism `[n] : A ⟶ A` of an abelian variety, that is, the image
of `n : ℤ` in the endomorphism ring `AbelianVariety.End A`.

The name is the standard one for abelian varieties, whose group law is conventionally written
additively. Here the group law on morphisms is written multiplicatively, so `[n]` is concretely the
`n`-th power map for that law: see `AbelianVariety.mulBy_eq_zpow`. -/
def mulBy (A : AbelianVariety K) (n : ℤ) : A ⟶ A := End.toHom (n : End A)

/-- Viewed back in the endomorphism ring, `[n]` is the integer `n`. -/
@[simp] lemma End.ofHom_mulBy (A : AbelianVariety K) (n : ℤ) :
    End.ofHom (mulBy A n) = (n : End A) :=
  End.ofHom_toHom _

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

/-- `[m + n]` is the pointwise product of `[m]` and `[n]`. -/
@[simp] lemma mulBy_add (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m + n) = mulBy A m * mulBy A n := by
  simp [mulBy]

@[simp] lemma mulBy_neg (A : AbelianVariety K) (n : ℤ) : mulBy A (-n) = (mulBy A n)⁻¹ := by
  simp [mulBy]

/-- `[m - n]` is the pointwise quotient of `[m]` and `[n]`. -/
@[simp] lemma mulBy_sub (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m - n) = mulBy A m / mulBy A n := by
  simp [mulBy]

/-- `[m * n]` is `[m]` composed with `[n]`. -/
@[simp] lemma mulBy_mul (A : AbelianVariety K) (m n : ℤ) :
    mulBy A (m * n) = mulBy A n ≫ mulBy A m := by
  simp [mulBy]

/-- Every homomorphism of abelian varieties commutes with multiplication by `n`. -/
lemma mulBy_comp (n : ℤ) (f : A ⟶ B) : mulBy A n ≫ f = f ≫ mulBy B n := by
  simp [mulBy_eq_zpow]

/-- Conjugating `[n]` by an isomorphism of abelian varieties gives `[n]`.

Deliberately not `@[simp]`: `AbelianVariety.End.ofHom_mulBy` rewrites both sides to an integer cast,
so this left-hand side is not in `simp` normal form, and what is left is Mathlib's `map_intCast`. -/
lemma congr_ofHom_mulBy (e : A ≅ B) (n : ℤ) :
    End.congr e (End.ofHom (mulBy A n)) = End.ofHom (mulBy B n) := by
  simp

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
