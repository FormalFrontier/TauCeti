/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Lie

/-!
# The derivation Lie algebra of a non-associative algebra

A **derivation** of an algebra `A` is a linear map `D` obeying the Leibniz rule
`D (x * y) = D x * y + x * D y`.  Nothing in that rule asks the multiplication to be associative,
commutative or unital, and the derivations of any algebra are closed under the commutator
`⁅D, E⁆ = D ∘ E - E ∘ D`, so they always form a Lie algebra `Der A`.  Mathlib has this construction
twice over, but only in special cases: `Derivation R A M` needs `A` commutative and associative, and
`LieDerivation R L M` needs the multiplication to be a Lie bracket.  The exceptional Lie algebras
are derivation algebras of algebras of neither kind -- `G₂ = Der 𝕆` for the octonions
(`TauCeti.Octonion`) and `F₄ = Der H₃(𝕆)` for the Albert algebra -- so this file builds `Der A` for
an arbitrary non-unital non-associative algebra, and records that both Mathlib constructions are
instances of it.

## Main definitions

* `TauCeti.derivationLieAlgebra R A`: the derivations of `A`, as a Lie subalgebra of
  `Module.End R A`.
* `TauCeti.derivationLieAlgebraCongr`: an isomorphism of algebras induces an isomorphism of their
  derivation Lie algebras, by conjugation.

## Main results

* `TauCeti.derivationLieAlgebra.apply_mul` and `TauCeti.derivationLieAlgebra.lie_mul`: the Leibniz
  rule, as an identity of linear maps and in the notation of the Lie action of `Der A` on `A`; and
  `TauCeti.derivationLieAlgebra.apply_one`: a derivation of a unital algebra kills the unit, and
  `TauCeti.derivationLieAlgebra.apply_mul_eq_zero`: its constants are closed under multiplication.
* `TauCeti.ad_mem_derivationLieAlgebra_commutatorRing`: the adjoint action of a Lie algebra is by
  derivations -- the Jacobi identity in Leibniz form.
* `TauCeti.derivationLieEquiv`: for a commutative associative algebra, `Der A` is Mathlib's
  `Derivation R A A` with its Lie structure.
* `TauCeti.commutatorRingDerivationLieEquiv`: for a Lie algebra `L`, the derivations of the
  underlying non-associative algebra `CommutatorRing L` are Mathlib's `LieDerivation R L L`.

## Implementation notes

`Der A` is a *bundled Lie subalgebra* of `Module.End R A` rather than a fresh carrier type with
hand-built instances: the `LieRing` and `LieAlgebra R` structures, the `Module R`-structure, the
action of `Der A` on `A` as a Lie module, and the lattice API then all come from Mathlib's
`LieSubalgebra`, and the only thing left to prove is that the commutator of two derivations is a
derivation.  This is also why the base is a `CommRing` and `A` a `NonUnitalNonAssocRing`: a Lie ring
is an additive *group*, so the semiring-level hypotheses under which the Leibniz rule still makes
sense do not suffice to make `Der A` one.

The Lie bracket of `Module.End R A` is the ring commutator, which Mathlib deliberately keeps out of
the global instance set (`LieRing.ofAssociativeRing`) because it clashes with the module action; it
is a local instance here, exactly as in `Mathlib/Algebra/Lie/OfAssociative.lean`.  A file consuming
`derivationLieAlgebra` needs the same `attribute [local instance 100] LieRing.ofAssociativeRing`
line in order to *state* facts about `Module.End R A` as a Lie algebra, but not in order to use
`↥(derivationLieAlgebra R A)`, whose own Lie structure is carried by the subalgebra.

The simp-normal form of the action of a derivation is the application `(D : Module.End R A) x` of
the underlying linear map, into which `TauCeti.derivationLieAlgebra.lie_apply` rewrites the Lie
bracket `⁅D, x⁆`.

## References

* [Highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 8, whose `derivationLieAlgebra` this is: the derivation algebra through which the split
  octonions and the Albert algebra produce `G₂` and `F₄`.
* N. Jacobson, *Lie Algebras* (1962), Chapter I, §2, and Chapter VII.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

section Defs

variable (R : Type u) (A : Type v) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- **The derivation Lie algebra** `Der A` of a non-unital non-associative `R`-algebra `A`: the
`R`-linear maps `D : A → A` satisfying the Leibniz rule `D (x * y) = D x * y + x * D y`, a Lie
subalgebra of `Module.End R A` under the commutator bracket.

The Leibniz rule is preserved by sums and by scalar multiples because the multiplication of `A` is
`R`-bilinear, and by the commutator because the "second derivative" terms `D (E x) * y` and
`x * D (E y)` that the composite `D ∘ E` contributes cancel against those of `E ∘ D`. -/
def derivationLieAlgebra : LieSubalgebra R (Module.End R A) where
  carrier := {D | ∀ x y : A, D (x * y) = D x * y + x * D y}
  add_mem' hD hE x y := by
    simp only [LinearMap.add_apply, hD x y, hE x y, add_mul, mul_add]
    abel
  zero_mem' x y := by simp
  smul_mem' r _ hD x y := by
    simp only [LinearMap.smul_apply, hD x y, smul_add, smul_mul_assoc, mul_smul_comm]
  lie_mem' hD hE x y := by
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, hE x y, hD x y, map_add,
      hD _ y, hD x _, hE _ y, hE x _, sub_mul, mul_sub]
    abel

variable {R A}

@[simp]
theorem mem_derivationLieAlgebra {D : Module.End R A} :
    D ∈ derivationLieAlgebra R A ↔ ∀ x y : A, D (x * y) = D x * y + x * D y :=
  Iff.rfl

namespace derivationLieAlgebra

/-- The Lie action of `Der A` on `A`, inherited from `Module.End R A`, is the application of the
underlying linear map. -/
@[simp]
theorem lie_apply (D : derivationLieAlgebra R A) (x : A) : ⁅D, x⁆ = (D : Module.End R A) x :=
  rfl

/-- **The Leibniz rule**: a derivation differentiates each factor of a product. -/
theorem apply_mul (D : derivationLieAlgebra R A) (x y : A) :
    (D : Module.End R A) (x * y)
      = (D : Module.End R A) x * y + x * (D : Module.End R A) y :=
  D.2 x y

/-- **The Leibniz rule, read as a compatibility of the Lie action of `Der A` with the
multiplication of `A`.**  This is `TauCeti.derivationLieAlgebra.apply_mul` written in the notation
of the `Der A`-module `A`, and is the sense in which that module is one whose bracket acts by
derivations; it is stated separately because `TauCeti.derivationLieAlgebra.lie_apply` normalises
the bracket away, so `simp` never produces this shape on its own. -/
theorem lie_mul (D : derivationLieAlgebra R A) (x y : A) :
    ⁅D, x * y⁆ = ⁅D, x⁆ * y + x * ⁅D, y⁆ :=
  D.2 x y

/-- The commutator of two derivations, evaluated. -/
theorem bracket_apply (D E : derivationLieAlgebra R A) (x : A) :
    (⁅D, E⁆ : Module.End R A) x
      = (D : Module.End R A) ((E : Module.End R A) x)
        - (E : Module.End R A) ((D : Module.End R A) x) :=
  rfl

/-- **The constants of a derivation are closed under multiplication**: if `D` kills `x` and `y`
then it kills `x * y`.  Together with linearity this says that the kernel of a derivation is a
subalgebra of `A`. -/
theorem apply_mul_eq_zero {D : derivationLieAlgebra R A} {x y : A}
    (hx : (D : Module.End R A) x = 0) (hy : (D : Module.End R A) y = 0) :
    (D : Module.End R A) (x * y) = 0 := by
  rw [apply_mul, hx, hy, zero_mul, mul_zero, add_zero]

/-- A derivation is determined by its values. -/
@[ext]
theorem ext {D E : derivationLieAlgebra R A}
    (h : ∀ x : A, (D : Module.End R A) x = (E : Module.End R A) x) : D = E :=
  Subtype.ext (LinearMap.ext h)

end derivationLieAlgebra

end Defs

section Unital

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- **A derivation of a unital algebra kills the unit**: `1 = 1 * 1` forces `D 1 = D 1 + D 1`.
Only unitality is used, not associativity. -/
@[simp]
theorem derivationLieAlgebra.apply_one (D : derivationLieAlgebra R A) :
    (D : Module.End R A) 1 = 0 := by
  have h := derivationLieAlgebra.apply_mul D 1 1
  rw [mul_one, mul_one, one_mul] at h
  nth_rewrite 1 [← add_zero ((D : Module.End R A) 1)] at h
  exact (add_left_cancel h).symm

end Unital


section Congr

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R]
  [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

/-- **Derivation algebras are transported along isomorphisms of algebras.**  A multiplicative
`R`-linear equivalence `e : A ≃ₗ[R] B` conjugates derivations of `A` to derivations of `B`, and the
resulting map is an isomorphism of Lie algebras.  This is the tool that identifies a concretely
built `Der A` with an abstractly presented Lie algebra.

The hypothesis is an unbundled multiplicativity condition on a `LinearEquiv` because Mathlib has no
equivalence class for non-unital non-associative algebras; `he` says exactly that `e` is an algebra
map, and no unitality is used. -/
def derivationLieAlgebraCongr (e : A ≃ₗ[R] B) (he : ∀ x y : A, e (x * y) = e x * e y) :
    derivationLieAlgebra R A ≃ₗ⁅R⁆ derivationLieAlgebra R B where
  toFun D := ⟨(e : A →ₗ[R] B) ∘ₗ (D : Module.End R A) ∘ₗ (e.symm : B →ₗ[R] A), fun x y => by
    have hsymm : e.symm (x * y) = e.symm x * e.symm y :=
      e.injective (by rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply])
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm,
      D.2 (e.symm x) (e.symm y), map_add, he, e.apply_symm_apply]⟩
  invFun D := ⟨(e.symm : B →ₗ[R] A) ∘ₗ (D : Module.End R B) ∘ₗ (e : A →ₗ[R] B), fun x y => by
    have hsymm : ∀ u v : B, e.symm (u * v) = e.symm u * e.symm v := fun u v =>
      e.injective (by rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply])
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, he,
      D.2 (e x) (e y), map_add, hsymm, e.symm_apply_apply]⟩
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp
  map_lie' := by intro D E; ext x; simp
  left_inv _ := by ext x; simp
  right_inv _ := by ext x; simp

@[simp]
theorem derivationLieAlgebraCongr_apply (e : A ≃ₗ[R] B) (he : ∀ x y : A, e (x * y) = e x * e y)
    (D : derivationLieAlgebra R A) (x : B) :
    (derivationLieAlgebraCongr e he D : Module.End R B) x
      = e ((D : Module.End R A) (e.symm x)) :=
  (rfl)

end Congr

section Commutative

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- **Mathlib's `Derivation R A A` is `Der A`.**  For a commutative associative algebra the two
Leibniz rules `D (x * y) = D x * y + x * D y` and `D (x * y) = x • D y + y • D x` say the same
thing, and both Lie structures are the commutator of `Module.End R A`, so the identity on
underlying linear maps is an isomorphism of Lie algebras. -/
def derivationLieEquiv : Derivation R A A ≃ₗ⁅R⁆ derivationLieAlgebra R A where
  toFun D := ⟨(D : A →ₗ[R] A), fun x y => by
    simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
    ring⟩
  invFun D := Derivation.mk' (D : Module.End R A) fun x y => by
    rw [D.2 x y]
    simp only [smul_eq_mul]
    ring
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem derivationLieEquiv_apply (D : Derivation R A A) (x : A) :
    (derivationLieEquiv D : Module.End R A) x = D x :=
  (rfl)

@[simp]
theorem derivationLieEquiv_symm_apply (D : derivationLieAlgebra R A) (x : A) :
    derivationLieEquiv.symm D x = (D : Module.End R A) x :=
  (rfl)

end Commutative

section Lie

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The Leibniz rule in `CommutatorRing L`**, spelled with the bracket.  Regarding a Lie algebra
as a non-associative algebra with `x * y = ⁅x, y⁆` turns the defining condition of
`derivationLieAlgebra` into `D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`. -/
theorem mem_derivationLieAlgebra_commutatorRing {D : Module.End R L} :
    D ∈ derivationLieAlgebra R (CommutatorRing L) ↔
      ∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆ :=
  Iff.rfl

/-- The two spellings of the Leibniz rule on a Lie algebra agree: the symmetric form
`⁅D x, y⁆ + ⁅x, D y⁆` that `derivationLieAlgebra` inherits from the multiplication, and the form
`⁅x, D y⁆ - ⁅y, D x⁆` that `LieDerivation` is stated with because a Lie algebra carries no right
action.  They differ by skew symmetry alone. -/
theorem leibniz_add_iff_leibniz_sub {D : Module.End R L} :
    (∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆) ↔
      ∀ x y : L, D ⁅x, y⁆ = ⁅x, D y⁆ - ⁅y, D x⁆ := by
  have key : ∀ x y : L, ⁅D x, y⁆ = -⁅y, D x⁆ := fun x y => (lie_skew (D x) y).symm
  constructor <;> intro h x y <;> rw [h x y, key x y] <;> abel

/-- Membership in `Der (CommutatorRing L)` is exactly the defining condition of a
`LieDerivation R L L`. -/
theorem mem_derivationLieAlgebra_commutatorRing_iff {D : Module.End R L} :
    D ∈ derivationLieAlgebra R (CommutatorRing L) ↔
      ∀ x y : L, D ⁅x, y⁆ = ⁅x, D y⁆ - ⁅y, D x⁆ :=
  mem_derivationLieAlgebra_commutatorRing.trans leibniz_add_iff_leibniz_sub

/-- **The adjoint action is by derivations**: `ad x` lies in `Der (CommutatorRing L)`, which is
exactly the Jacobi identity in Leibniz form.  This is the inner-derivation half of
`TauCeti.commutatorRingDerivationLieEquiv`. -/
theorem ad_mem_derivationLieAlgebra_commutatorRing (x : L) :
    LieAlgebra.ad R L x ∈ derivationLieAlgebra R (CommutatorRing L) :=
  mem_derivationLieAlgebra_commutatorRing.mpr fun y z => leibniz_lie x y z

/-- **Mathlib's `LieDerivation R L L` is `Der (CommutatorRing L)`.**  For the non-associative
algebra underlying a Lie algebra the two Leibniz rules agree by
`TauCeti.leibniz_add_iff_leibniz_sub`, and both Lie structures are the commutator of the
endomorphism ring, so the identity on underlying linear maps is an isomorphism of Lie algebras. -/
def commutatorRingDerivationLieEquiv :
    derivationLieAlgebra R (CommutatorRing L) ≃ₗ⁅R⁆ LieDerivation R L L where
  toFun D := ⟨D.1, mem_derivationLieAlgebra_commutatorRing_iff.mp D.2⟩
  invFun D := ⟨(D : L →ₗ[R] L),
    mem_derivationLieAlgebra_commutatorRing_iff.mpr fun x y => D.apply_lie_eq_sub x y⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem commutatorRingDerivationLieEquiv_apply
    (D : derivationLieAlgebra R (CommutatorRing L)) (x : L) :
    commutatorRingDerivationLieEquiv D x = D.1 x :=
  (rfl)

end Lie

end TauCeti
