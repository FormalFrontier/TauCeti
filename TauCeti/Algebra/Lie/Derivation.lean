/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
public import Mathlib.RingTheory.Derivation.Lie

/-!
# The derivation Lie algebra of a non-associative algebra

A **derivation** of an algebra `A` is a linear map `D` obeying the Leibniz rule
`D (x * y) = D x * y + x * D y`.  Nothing in that rule asks the multiplication to be associative,
commutative or unital, and the derivations of any algebra are closed under the commutator
`⁅D, E⁆ = D ∘ E - E ∘ D`, so they always form a Lie algebra `Der A`.  Mathlib has this construction
twice over, but only in special cases: `Derivation R A M` needs `A` commutative and associative, and
`LieDerivation R L M` needs the multiplication to be a Lie bracket.  Two of the exceptional Lie
algebras are derivation algebras of algebras of neither kind -- `G₂ = Der 𝕆` for the octonions
(`TauCeti.Octonion`) and `F₄ = Der H₃(𝕆)` for the Albert algebra -- so this file builds `Der A` for
an arbitrary non-unital non-associative algebra, and records that both Mathlib constructions are
instances of it.

## Main definitions

* `TauCeti.derivationLieAlgebra R A`: the derivations of `A`, as a Lie subalgebra of
  `Module.End R A`.
* `TauCeti.derivationLieAlgebraCongr`: an isomorphism of algebras induces an isomorphism of their
  derivation Lie algebras, by conjugation.

## Main results

* `TauCeti.derivationLieAlgebra.apply_mul_eq_add`: the Leibniz rule;
  `TauCeti.derivationLieAlgebra.apply_one_eq_zero`: a derivation of a unital algebra kills the
  unit; and `TauCeti.derivationLieAlgebra.apply_mul_eq_zero`: its constants are closed under
  multiplication.
* `TauCeti.ad_mem_derivationLieAlgebra_commutatorRing`: the adjoint action of a Lie algebra is by
  derivations -- the Jacobi identity in Leibniz form.
* `TauCeti.derivationEquivDerivationLieAlgebra`: for a commutative associative algebra, `Der A` is
  Mathlib's `Derivation R A A` with its Lie structure.
* `TauCeti.derivationLieAlgebraCommutatorRingEquivLieDerivation`: for a Lie algebra `L`, the
  derivations of the underlying non-associative algebra `CommutatorRing L` are Mathlib's
  `LieDerivation R L L`.

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
the underlying linear map: Mathlib's `LieSubalgebra.coe_bracket_of_module` and
`Module.End.lie_apply` already rewrite the Lie bracket `⁅D, x⁆` into it, so no lemma of this file
needs to say so.

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

/-- **The Leibniz rule**: a derivation differentiates each factor of a product. -/
@[simp]
theorem apply_mul_eq_add (D : derivationLieAlgebra R A) (x y : A) :
    (D : Module.End R A) (x * y)
      = (D : Module.End R A) x * y + x * (D : Module.End R A) y :=
  D.2 x y

/-- The commutator of two derivations, evaluated. -/
@[simp]
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
  rw [apply_mul_eq_add, hx, hy, zero_mul, mul_zero, add_zero]

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
theorem derivationLieAlgebra.apply_one_eq_zero (D : derivationLieAlgebra R A) :
    (D : Module.End R A) 1 = 0 := by
  simpa using derivationLieAlgebra.apply_mul_eq_add D 1 1

end Unital


section Congr

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R]
  [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

omit [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B] in
/-- **The inverse of a multiplicative linear equivalence is multiplicative.**  The hypothesis is an
unbundled multiplicativity condition on a `LinearEquiv` because Mathlib has no equivalence class for
non-unital non-associative algebras; `he` says exactly that `e` is an algebra map, and no unitality
is used. -/
theorem symm_map_mul (e : A ≃ₗ[R] B) (he : ∀ x y : A, e (x * y) = e x * e y) (u v : B) :
    e.symm (u * v) = e.symm u * e.symm v :=
  e.injective (by simp [he])

/-- **Conjugation by a multiplicative linear equivalence carries derivations to derivations.** -/
theorem lieConj_mem_derivationLieAlgebra {e : A ≃ₗ[R] B}
    (he : ∀ x y : A, e (x * y) = e x * e y) {D : Module.End R A}
    (hD : D ∈ derivationLieAlgebra R A) : e.lieConj D ∈ derivationLieAlgebra R B :=
  mem_derivationLieAlgebra.mpr fun x y => by
    simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply, symm_map_mul e he,
      mem_derivationLieAlgebra.mp hD, map_add, he, LinearEquiv.apply_symm_apply]

/-- **Derivation algebras are transported along isomorphisms of algebras.**  A multiplicative
`R`-linear equivalence `e : A ≃ₗ[R] B` conjugates derivations of `A` to derivations of `B`, and the
resulting map is an isomorphism of Lie algebras.  This is the tool that transports `Der` between two
models of the same algebra -- two constructions of the split octonions, say. -/
def derivationLieAlgebraCongr (e : A ≃ₗ[R] B) (he : ∀ x y : A, e (x * y) = e x * e y) :
    derivationLieAlgebra R A ≃ₗ⁅R⁆ derivationLieAlgebra R B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  refine SetLike.ext fun D => ⟨?_, fun hD => ?_⟩
  · rintro ⟨E, hE, rfl⟩
    exact lieConj_mem_derivationLieAlgebra he hE
  · exact ⟨e.lieConj.symm D, lieConj_mem_derivationLieAlgebra (symm_map_mul e he) hD,
      e.lieConj.apply_symm_apply D⟩

@[simp]
theorem derivationLieAlgebraCongr_apply (e : A ≃ₗ[R] B) (he : ∀ x y : A, e (x * y) = e x * e y)
    (D : derivationLieAlgebra R A) (x : B) :
    (derivationLieAlgebraCongr e he D : Module.End R B) x
      = e ((D : Module.End R A) (e.symm x)) :=
  (rfl)

@[simp]
theorem derivationLieAlgebraCongr_symm_apply (e : A ≃ₗ[R] B)
    (he : ∀ x y : A, e (x * y) = e x * e y) (D : derivationLieAlgebra R B) (x : A) :
    ((derivationLieAlgebraCongr e he).symm D : Module.End R A) x
      = e.symm ((D : Module.End R B) (e x)) :=
  (rfl)

end Congr

section Commutative

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- **Mathlib's `Derivation R A A` is `Der A`.**  For a commutative associative algebra the two
Leibniz rules `D (x * y) = D x * y + x * D y` and `D (x * y) = x • D y + y • D x` say the same
thing, and both Lie structures are the commutator of `Module.End R A`, so the identity on
underlying linear maps is an isomorphism of Lie algebras. -/
def derivationEquivDerivationLieAlgebra : Derivation R A A ≃ₗ⁅R⁆ derivationLieAlgebra R A where
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
theorem derivationEquivDerivationLieAlgebra_apply (D : Derivation R A A) (x : A) :
    (derivationEquivDerivationLieAlgebra D : Module.End R A) x = D x :=
  (rfl)

@[simp]
theorem derivationEquivDerivationLieAlgebra_symm_apply (D : derivationLieAlgebra R A) (x : A) :
    derivationEquivDerivationLieAlgebra.symm D x = (D : Module.End R A) x :=
  (rfl)

end Commutative

section Lie

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The two spellings of the Leibniz rule on a Lie ring agree: the symmetric form
`⁅D x, y⁆ + ⁅x, D y⁆` that `derivationLieAlgebra` inherits from the multiplication of
`CommutatorRing L`, and the form `⁅x, D y⁆ - ⁅y, D x⁆` that `LieDerivation` is stated with because a
Lie algebra carries no right action.  They differ by skew symmetry alone, so neither linearity of
`D` nor the base ring plays any part. -/
theorem leibniz_add_iff_leibniz_sub {D : L → L} :
    (∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆) ↔
      ∀ x y : L, D ⁅x, y⁆ = ⁅x, D y⁆ - ⁅y, D x⁆ := by
  have key : ∀ x y : L, ⁅D x, y⁆ = -⁅y, D x⁆ := fun x y => (lie_skew (D x) y).symm
  constructor <;> intro h x y <;> rw [h x y, key x y] <;> abel

/-- **Membership in `Der (CommutatorRing L)` is exactly the defining condition of a
`LieDerivation R L L`.**  Regarding a Lie algebra as a non-associative algebra with `x * y = ⁅x, y⁆`
turns the defining condition of `derivationLieAlgebra` into `D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`, which
`TauCeti.leibniz_add_iff_leibniz_sub` rewrites into the skew form. -/
theorem mem_derivationLieAlgebra_commutatorRing_iff_apply_lie_eq_sub {D : Module.End R L} :
    D ∈ derivationLieAlgebra R (CommutatorRing L) ↔
      ∀ x y : L, D ⁅x, y⁆ = ⁅x, D y⁆ - ⁅y, D x⁆ :=
  mem_derivationLieAlgebra.trans leibniz_add_iff_leibniz_sub

/-- **The adjoint action is by derivations**: `ad x` lies in `Der (CommutatorRing L)`, which is
exactly the Jacobi identity in Leibniz form.  This is the inner-derivation half of
`TauCeti.derivationLieAlgebraCommutatorRingEquivLieDerivation`. -/
theorem ad_mem_derivationLieAlgebra_commutatorRing (x : L) :
    LieAlgebra.ad R L x ∈ derivationLieAlgebra R (CommutatorRing L) :=
  mem_derivationLieAlgebra.mpr fun (y z : L) => leibniz_lie x y z

/-- **Mathlib's `LieDerivation R L L` is `Der (CommutatorRing L)`.**  For the non-associative
algebra underlying a Lie algebra the two Leibniz rules agree by
`TauCeti.mem_derivationLieAlgebra_commutatorRing_iff_apply_lie_eq_sub`, and both Lie structures are
the commutator of the endomorphism ring, so the identity on underlying linear maps is an isomorphism
of Lie algebras. -/
def derivationLieAlgebraCommutatorRingEquivLieDerivation :
    derivationLieAlgebra R (CommutatorRing L) ≃ₗ⁅R⁆ LieDerivation R L L where
  toFun D := ⟨D.1, mem_derivationLieAlgebra_commutatorRing_iff_apply_lie_eq_sub.mp D.2⟩
  invFun D := ⟨(D : L →ₗ[R] L),
    mem_derivationLieAlgebra_commutatorRing_iff_apply_lie_eq_sub.mpr fun x y =>
      D.apply_lie_eq_sub x y⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem derivationLieAlgebraCommutatorRingEquivLieDerivation_apply
    (D : derivationLieAlgebra R (CommutatorRing L)) (x : L) :
    derivationLieAlgebraCommutatorRingEquivLieDerivation D x = D.1 x :=
  (rfl)

@[simp]
theorem derivationLieAlgebraCommutatorRingEquivLieDerivation_symm_apply
    (D : LieDerivation R L L) (x : L) :
    (derivationLieAlgebraCommutatorRingEquivLieDerivation.symm D).1 x = D x :=
  (rfl)

end Lie

end TauCeti
