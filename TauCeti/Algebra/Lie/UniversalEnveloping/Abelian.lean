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
function `n : κ →₀ ℕ` rather than by a sorted word. In particular `ι` is injective on `L` when `L`
is free as an `R`-module (`TauCeti.UniversalEnvelopingAlgebra.ι_injective`); for a general Lie
algebra, injectivity is a corollary of Poincaré--Birkhoff--Witt, which over a commutative ring
still needs `L` to be free (or at least projective) as an `R`-module, and is unconditional only
over a field.

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
* `TauCeti.UniversalEnvelopingAlgebra.basisMonomials`: the monomial basis of `U(L)`, with
  `TauCeti.UniversalEnvelopingAlgebra.linearIndependent_ι_basis` and
  `TauCeti.UniversalEnvelopingAlgebra.ι_injective`.

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

private theorem liftSym_liftι (s : SymmetricAlgebra R L) : liftSym R L (liftι R L s) = s := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | ι x => rw [liftι_ι, liftSym_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem liftι_liftSym (a : U) : liftι R L (liftSym R L a) = a := by
  induction a using induction_ι R L with
  | ι x => rw [liftSym_ι, liftι_ι]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]

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

/-- The pointwise form of `TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv_toAlgHom`: the
polynomial identification evaluates a polynomial at the canonical generators. -/
theorem mvPolynomialEquiv_apply (b : Basis κ R L) (p : MvPolynomial κ R) :
    mvPolynomialEquiv R L b p =
      MvPolynomial.aeval (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i)) p :=
  AlgHom.congr_fun (mvPolynomialEquiv_toAlgHom R L b) p

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
  have hb : basisMonomials R L b n = mvPolynomialEquiv R L b (MvPolynomial.monomial n 1) := by
    simp [basisMonomials, mvPolynomialEquiv, Basis.symmetricAlgebra]
  rw [hb, mvPolynomialEquiv_apply, MvPolynomial.aeval_monomial, map_one, one_mul]

/-- **The images of a basis of an abelian Lie algebra are linearly independent in the enveloping
algebra**: they are the images of the variables under the polynomial identification. -/
theorem linearIndependent_ι_basis (b : Basis κ R L) :
    LinearIndependent R fun i : κ ↦ (_root_.UniversalEnvelopingAlgebra.ι R (b i) : U) := by
  have h := (MvPolynomial.linearIndependent_X (σ := κ) (R := R)).map'
    (mvPolynomialEquiv R L b).toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot_of_injective (mvPolynomialEquiv R L b).injective)
  simpa [Function.comp_def] using h

/-- **The canonical map of an abelian Lie algebra into its enveloping algebra is injective**, when
the Lie algebra is free as a module. For a general Lie algebra this is a corollary of the
Poincaré--Birkhoff--Witt theorem, which over a commutative ring `R` needs `L` to be free (or at
least projective) as an `R`-module; over a field it is unconditional. -/
theorem ι_injective [Module.Free R L] :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : L → U) := by
  obtain ⟨b⟩ : Nonempty (Basis (Module.Free.ChooseBasisIndex R L) R L) :=
    ⟨Module.Free.chooseBasis R L⟩
  have hconstr : (b.constr R fun i ↦ (_root_.UniversalEnvelopingAlgebra.ι R (b i) : U)) =
      ((_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U) : L →ₗ[R] U) :=
    b.constr_eq R fun _ ↦ rfl
  have h : Function.Injective
      ⇑(b.constr R fun i ↦ (_root_.UniversalEnvelopingAlgebra.ι R (b i) : U)) :=
    b.injective_constr_of_linearIndependent (linearIndependent_ι_basis R L b)
  rw [hconstr] at h
  exact h

end TauCeti.UniversalEnvelopingAlgebra
