/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

public section

/-!
# The enveloping algebra of an abelian Lie algebra is its symmetric algebra

Let `L` be an abelian Lie algebra over a commutative ring `R`, that is, one whose bracket vanishes
identically (`IsLieAbelian L`). This file proves that the canonical map
`ι : L → UniversalEnvelopingAlgebra R L` exhibits `U(L)` as the **symmetric algebra** of the
`R`-module `L`, and reads off the resulting basis of `U(L)`.

## What this says

The defining relation of `U(L)` is `ι x * ι y - ι y * ι x = ι ⁅x, y⁆`, so for an abelian `L` it is
the commutativity relation and nothing else: `U(L)` is commutative
(`TauCeti.UniversalEnvelopingAlgebra.instCommRing`), and it is the *universal* commutative
`R`-algebra containing `L`, which is the symmetric algebra. Both algebras are therefore built by
the same universal property, and the comparison is the pair of lifts in either direction; nothing
finer, and in particular no Poincaré--Birkhoff--Witt input, is used.

The consequence that is not visible in the universal property is the **basis**. The symmetric
algebra of a free module is a polynomial algebra (Mathlib's
`SymmetricAlgebra.equivMvPolynomial`), so for a basis `b` of `L` the algebra `U(L)` is the
polynomial algebra on the `b i` (`TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv`) and the
monomials `∏ᵢ ι(b i) ^ nᵢ` are an `R`-basis of it
(`TauCeti.UniversalEnvelopingAlgebra.basisMonomials`). That is the Poincaré--Birkhoff--Witt
ordered-monomial theorem for an abelian Lie algebra: the ordering of a monomial carries no
information here, since the generators commute, so a monomial is recorded by its exponent
function `n : κ →₀ ℕ` rather than by a sorted word.

The comparison also makes `ι` injective on any abelian `L`
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective`), with no hypothesis on `L` as a module: it
identifies `ι` with the canonical map `L → S(L)`, which the square-zero extension `R ⊕ L` retracts.
For a general Lie algebra injectivity is instead a corollary of Poincaré--Birkhoff--Witt, which
over a commutative ring needs `L` to be free (or at least projective) as an `R`-module, and is
unconditional only over a field.

## Where it is used

A Cartan subalgebra `H` of a Lie algebra `L` with non-degenerate Killing form is abelian, by
Mathlib's `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`; that instance also asks that
`L` be free and finite as an `R`-module, that `R` be an integral domain and a principal ideal ring,
and that `L` be Artinian, all of which hold for a finite-dimensional Lie algebra over a field.
`TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv` then applies to `H` with no hypotheses
of its own beyond that abelianness, and identifies `U(H)` with `S(H)`. This identification is what
the Harish-Chandra projection of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` is stated against, and the abelian
case of the ordered-monomial basis of the Poincaré--Birkhoff--Witt sub-project of Layer 3, whose
spanning half is
`TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`. The general theorem
is not proved here: the argument below uses commutativity of `U(L)` throughout and says nothing
about a non-abelian `L`.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.instCommRing`: the enveloping algebra of an abelian Lie
  algebra is commutative.
* `TauCeti.UniversalEnvelopingAlgebra.isSymmetricAlgebra_ι` and
  `TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv`: **`ι : L → U(L)` exhibits `U(L)` as
  the symmetric algebra of `L`**, with the resulting algebra isomorphism `S(L) ≃ₐ[R] U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv`: for a basis of `L`, the identification of
  `U(L)` with a polynomial algebra.
* `TauCeti.UniversalEnvelopingAlgebra.ι_injective`: `ι` is injective, with no hypothesis on `L` as
  an `R`-module.
* `TauCeti.UniversalEnvelopingAlgebra.basisMonomials`: the monomial basis of `U(L)`, with
  `TauCeti.UniversalEnvelopingAlgebra.linearIndependent_ι_basis`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Chapter V, §17
  (the Poincaré--Birkhoff--Witt theorem; §17.2 is the abelian case).
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] [IsLieAbelian L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-! ### Commutativity -/

/-- **The enveloping algebra of an abelian Lie algebra is commutative.** The defining relation
`ι x * ι y - ι y * ι x = ι ⁅x, y⁆` of `U(L)` reads `ι x * ι y = ι y * ι x` when the bracket
vanishes, and `U(L)` is generated by the scalars and those generators. -/
instance instCommRing : CommRing U :=
  { (inferInstance : Ring U) with
    mul_comm := fun a b ↦ by
      -- the canonical generators commute, their commutator being the image of the bracket
      have hgen : ∀ x ∈ Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R (L := L)),
          ∀ y ∈ Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R (L := L)), x * y = y * x := by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        exact commute_of_lie_eq_zero (AlgHom.id R U) (trivial_lie_zero L L x y)
      -- and those generators generate `U(L)` as an `R`-algebra
      have hcomm := _root_.Algebra.isMulCommutative_adjoin R hgen
      rw [adjoin_range_ι R L] at hcomm
      exact setLike_mul_comm (s := (⊤ : Subalgebra R U)) _root_.Algebra.mem_top
        _root_.Algebra.mem_top }

/-! ### The comparison with the symmetric algebra -/

/-- The canonical map `L → S(L)` into the symmetric algebra, as a homomorphism of Lie algebras:
the bracket on `L` vanishes and the bracket on `S(L)` is the commutator of a commutative ring. -/
private def toSymmetricAlgebra : L →ₗ⁅R⁆ SymmetricAlgebra R L :=
  { SymmetricAlgebra.ι R L with
    map_lie' := fun {x y} => by
      simp [trivial_lie_zero L L x y, LieRing.of_associative_ring_bracket, mul_comm] }

private theorem toSymmetricAlgebra_apply (x : L) :
    toSymmetricAlgebra R L x = SymmetricAlgebra.ι R L x :=
  rfl

/-- The comparison `S(L) → U(L)`, the lift of `ι` through the universal property of the symmetric
algebra. It is the underlying algebra homomorphism of
`TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv`. -/
private def liftι : SymmetricAlgebra R L →ₐ[R] U :=
  SymmetricAlgebra.lift ((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U)

private theorem liftι_ι (x : L) :
    liftι R L (SymmetricAlgebra.ι R L x) = _root_.UniversalEnvelopingAlgebra.ι R x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- The comparison `U(L) → S(L)`, the lift of `toSymmetricAlgebra` through the universal property
of the enveloping algebra. -/
private def liftSym : U →ₐ[R] SymmetricAlgebra R L :=
  _root_.UniversalEnvelopingAlgebra.lift R (toSymmetricAlgebra R L)

private theorem liftSym_ι (x : L) :
    liftSym R L (_root_.UniversalEnvelopingAlgebra.ι R x) = SymmetricAlgebra.ι R L x :=
  (_root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x).trans (toSymmetricAlgebra_apply R L x)

-- `ext` is `SymmetricAlgebra.algHom_ext`: the two sides agree once they agree on the canonical
-- generators of `S(L)`.
private theorem liftSym_comp_liftι :
    (liftSym R L).comp (liftι R L) = AlgHom.id R (SymmetricAlgebra R L) := by
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_coe, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.coe_id, id_eq, liftι_ι, liftSym_ι]

private theorem liftSym_liftι (s : SymmetricAlgebra R L) : liftSym R L (liftι R L s) = s :=
  AlgHom.congr_fun (liftSym_comp_liftι R L) s

-- `ext` is `UniversalEnvelopingAlgebra.hom_ext`: the two sides agree once they agree on the
-- canonical generators of `U(L)`.
private theorem liftι_comp_liftSym : (liftι R L).comp (liftSym R L) = AlgHom.id R U := by
  ext x
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply, AlgHom.id_apply,
    liftSym_ι, liftι_ι]

private theorem liftι_liftSym (a : U) : liftι R L (liftSym R L a) = a :=
  AlgHom.congr_fun (liftι_comp_liftSym R L) a

/-- **The canonical map of an abelian Lie algebra into its enveloping algebra exhibits the
enveloping algebra as the symmetric algebra.** The two universal properties describe the same
object: an `R`-linear map out of `L` into a commutative `R`-algebra is the same thing as a Lie
algebra homomorphism, because the bracket on `L` and the commutator on the target both vanish. -/
theorem isSymmetricAlgebra_ι :
    IsSymmetricAlgebra ((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U) :=
  Function.bijective_iff_has_inverse.mpr ⟨liftSym R L, liftSym_liftι R L, liftι_liftSym R L⟩

/-- **The symmetric algebra of an abelian Lie algebra is its enveloping algebra**, as an algebra
isomorphism `S(L) ≃ₐ[R] U(L)` carrying the canonical generators to the canonical generators. -/
noncomputable def symmetricAlgebraEquiv : SymmetricAlgebra R L ≃ₐ[R] U :=
  (isSymmetricAlgebra_ι R L).equiv

/-- The comparison isomorphism sends the canonical generator `SymmetricAlgebra.ι R L x` of `S(L)`
to the canonical generator `UniversalEnvelopingAlgebra.ι R x` of `U(L)`. -/
@[simp]
theorem symmetricAlgebraEquiv_ι (x : L) :
    symmetricAlgebraEquiv R L (SymmetricAlgebra.ι R L x) =
      _root_.UniversalEnvelopingAlgebra.ι R x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- The inverse of the comparison isomorphism sends the canonical generator
`UniversalEnvelopingAlgebra.ι R x` of `U(L)` back to `SymmetricAlgebra.ι R L x`. This is the form
to quote by hand; the `simp`-normal form is
`TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_ι'`, because `simp` rewrites `ι` to
`mkAlgHom` by `UniversalEnvelopingAlgebra.ι_apply`. -/
theorem symmetricAlgebraEquiv_symm_ι (x : L) :
    (symmetricAlgebraEquiv R L).symm (_root_.UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R L x :=
  (isSymmetricAlgebra_ι R L).equiv_symm_apply x

/-- `TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_ι` with its left-hand side in
`simp`-normal form: the `simp` lemma `UniversalEnvelopingAlgebra.ι_apply` unfolds `ι R x` to
`mkAlgHom R L (TensorAlgebra.ι R x)`, so this is the shape `simp` actually meets. -/
@[simp]
theorem symmetricAlgebraEquiv_symm_ι' (x : L) :
    (symmetricAlgebraEquiv R L).symm
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      SymmetricAlgebra.ι R L x := by
  simpa using symmetricAlgebraEquiv_symm_ι R L x

/-- The canonical map of a module into its symmetric algebra is injective. The `R`-linear map
`x ↦ TrivSqZeroExt.inr x` into the square-zero extension `R ⊕ M`, which is a commutative
`R`-algebra, lifts to `S(M)` and retracts `SymmetricAlgebra.ι` along `TrivSqZeroExt.snd`. This is
the symmetric-algebra analogue of Mathlib's `TensorAlgebra.ι_leftInverse`. -/
private theorem symmetricAlgebra_ι_injective {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M]
    [Module S M] : Function.Injective (SymmetricAlgebra.ι S M) := by
  let : Module Sᵐᵒᵖ M := Module.compHom _ ((RingHom.id S).fromOpposite mul_comm)
  have : IsCentralScalar S M := ⟨fun _ _ ↦ rfl⟩
  exact Function.LeftInverse.injective (g := (TrivSqZeroExt.sndHom S M).comp
    (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom S M)).toLinearMap) fun x ↦ by simp

/-- **The canonical map of an abelian Lie algebra into its enveloping algebra is injective.** Under
the comparison it is the canonical map `L → S(L)`, which is injective for every module. For a
general Lie algebra injectivity is instead a corollary of the Poincaré--Birkhoff--Witt theorem,
which over a commutative ring needs `L` to be free (or at least projective) as an `R`-module. -/
theorem ι_injective :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : L → U) := fun x y h ↦
  symmetricAlgebra_ι_injective <| by
    rw [← symmetricAlgebraEquiv_symm_ι R L x, ← symmetricAlgebraEquiv_symm_ι R L y, h]

/-- The enveloping algebra of an abelian Lie algebra which is free as a module is free as a
module. -/
instance instModuleFree [Module.Free R L] : Module.Free R U :=
  Module.Free.of_equiv (symmetricAlgebraEquiv R L).toLinearEquiv

/-! ### The monomial basis -/

variable {κ : Type w}

/-- **The enveloping algebra of an abelian Lie algebra with a basis is a polynomial algebra** on
that basis. -/
noncomputable def mvPolynomialEquiv (b : Basis κ R L) : MvPolynomial κ R ≃ₐ[R] U :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.trans (symmetricAlgebraEquiv R L)

/-- The polynomial identification sends the variable `X i` to the canonical generator `ι R (b i)`
of `U(L)`. -/
@[simp]
theorem mvPolynomialEquiv_X (b : Basis κ R L) (i : κ) :
    mvPolynomialEquiv R L b (MvPolynomial.X i) = _root_.UniversalEnvelopingAlgebra.ι R (b i) := by
  simp [mvPolynomialEquiv]

/-- The inverse of the polynomial identification sends the canonical generator `ι R (b i)` of
`U(L)` back to the variable `X i`. This is the form to quote by hand; the `simp`-normal form is
`TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv_symm_ι'`, because `simp` rewrites `ι` to
`mkAlgHom` by `UniversalEnvelopingAlgebra.ι_apply`. -/
theorem mvPolynomialEquiv_symm_ι (b : Basis κ R L) (i : κ) :
    (mvPolynomialEquiv R L b).symm (_root_.UniversalEnvelopingAlgebra.ι R (b i)) =
      MvPolynomial.X i :=
  (mvPolynomialEquiv R L b).symm_apply_eq.mpr (mvPolynomialEquiv_X R L b i).symm

/-- `TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv_symm_ι` with its left-hand side in
`simp`-normal form: the `simp` lemma `UniversalEnvelopingAlgebra.ι_apply` unfolds `ι R (b i)` to
`mkAlgHom R L (TensorAlgebra.ι R (b i))`, so this is the shape `simp` actually meets. -/
@[simp]
theorem mvPolynomialEquiv_symm_ι' (b : Basis κ R L) (i : κ) :
    (mvPolynomialEquiv R L b).symm
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R (b i))) =
      MvPolynomial.X i := by
  simpa using mvPolynomialEquiv_symm_ι R L b i

/-- The polynomial identification is evaluation of a polynomial at the canonical generators. -/
theorem mvPolynomialEquiv_toAlgHom (b : Basis κ R L) :
    (mvPolynomialEquiv R L b : MvPolynomial κ R →ₐ[R] U) =
      MvPolynomial.aeval fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) :=
  MvPolynomial.algHom_ext fun i ↦ by simp

/-- The basis vector of Mathlib's `Module.Basis.symmetricAlgebra` at an exponent function `n` is
the monomial `∏ᵢ ι (b i) ^ nᵢ` in the canonical generators of the symmetric algebra. Mathlib
characterizes that basis only through its `Module.Basis.repr`. -/
private theorem basis_symmetricAlgebra_apply {S : Type*} [CommSemiring S] {M : Type*}
    [AddCommMonoid M] [Module S M] (b : Basis κ S M) (n : κ →₀ ℕ) :
    b.symmetricAlgebra n = n.prod fun i k ↦ SymmetricAlgebra.ι S M (b i) ^ k := by
  simp [Basis.symmetricAlgebra, MvPolynomial.monomial_eq, map_finsuppProd]

/-- **The monomials in a basis of an abelian Lie algebra are a basis of its enveloping algebra.**
This is the Poincaré--Birkhoff--Witt ordered-monomial theorem in the abelian case, where a monomial
is determined by its exponent function because the generators commute. -/
noncomputable def basisMonomials (b : Basis κ R L) : Basis (κ →₀ ℕ) R U :=
  b.symmetricAlgebra.map (symmetricAlgebraEquiv R L).toLinearEquiv

/-- The monomial basis vector at an exponent function `n` is the monomial `∏ᵢ ι (b i) ^ nᵢ` in the
canonical generators. -/
@[simp]
theorem basisMonomials_apply (b : Basis κ R L) (n : κ →₀ ℕ) :
    basisMonomials R L b n = n.prod fun i k ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ k := by
  simp only [basisMonomials, Basis.map_apply, basis_symmetricAlgebra_apply,
    AlgEquiv.toLinearEquiv_apply, map_finsuppProd, map_pow, symmetricAlgebraEquiv_ι]

/-- **The images of a basis of an abelian Lie algebra are linearly independent in the enveloping
algebra**: `ι` is an injective linear map. -/
theorem linearIndependent_ι_basis (b : Basis κ R L) :
    LinearIndependent R fun i : κ ↦ (_root_.UniversalEnvelopingAlgebra.ι R (b i) : U) := by
  have h := b.linearIndependent.map'
    ((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U)
    (LinearMap.ker_eq_bot_of_injective (ι_injective R L))
  simpa [Function.comp_def] using h

end TauCeti.UniversalEnvelopingAlgebra
