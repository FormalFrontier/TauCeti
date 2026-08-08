/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis

/-!
# A finite field containing the roots of unity splits the centre of the group algebra

Let `G` be a finite group and `K` a finite field whose characteristic does not divide `|G|` and
whose multiplicative order kills `G`, that is `g ^ |K| = g` for every `g : G` -- equivalently, the
exponent of `G` divides `|K| - 1`, so that `K` already contains the roots of unity that the
eigenvalues of `G` need. This file proves that under exactly those hypotheses the centre of `K[G]`
is *split*: it is `K`-algebra isomorphic to a product of copies of `K`, one for each conjugacy
class of `G`.

The point is that `K` is not algebraically closed, so nothing forces the residue fields of
`Z(K[G])` to be `K` rather than proper extensions of it -- for a bad `K` they are proper
extensions, and the splitting genuinely fails. What rules that out is the following trace
argument, which is the whole content of the file.

For any `u : K[G]`, the trace of the matrix `M` of left multiplication by `u` in the group basis
is `|G|` times the coefficient of `u` at `1`, and over a finite field
`Matrix.trace (M ^ |K|) = (Matrix.trace M) ^ |K|` (`FiniteField.trace_pow_card`). Since
`a ^ |K| = a` in `K`, the coefficient at `1` is unchanged by raising to the `|K|`-th power, once
`|G|` is invertible. Now apply this to `u = y * g⁻¹` for a *central* `y`: there
`(y * g⁻¹) ^ |K| = y ^ |K| * g⁻¹`, because `y` is central and `g⁻¹ ^ |K| = g⁻¹`, so the identity
compares the coefficients of `y ^ |K|` and of `y` at each `g`. Hence `y ^ |K| = y`.

A commutative ring on which the `|K|`-th power map is the identity is reduced, and a finite domain
on which it is the identity is `K` itself; so the centre, being reduced and Artinian, is the
product of its residue fields, all of which are `K`. Counting `K`-dimensions against the class-sum
basis identifies the number of factors with the number of conjugacy classes.

This is the good-prime structure theorem of the Burnside--Dixon--Schneider algorithm, stated for a
general finite coefficient field; the specialization to `ZMod p` at a good Dixon prime is
`TauCeti/RepresentationTheory/CharacterTable/Dixon/Structure.lean`.

## Main results

* `TauCeti.pow_card_eq_self_of_mem_center`: the centre of `K[G]` is fixed by `x ↦ x ^ |K|`.
* `TauCeti.bijective_algebraMap_center_quotient`: every residue field of the centre is `K`.
* `TauCeti.centerAlgEquivPi`: the centre is the algebra of functions on its own maximal spectrum.
* `TauCeti.card_maximalSpectrum_center`: that spectrum has one point per conjugacy class.
* `TauCeti.nonempty_centerAlgEquiv_conjClasses`: `Z(K[G]) ≃ₐ[K] (ConjClasses G → K)`.

## Implementation notes

The left regular matrix is built here as `TauCeti.regularMatrix` rather than taken from Mathlib's
`Algebra.leftMulMatrix`, which is available only over a *commutative* algebra; the group algebra of
a nonabelian group is not one. On the centre, where `Algebra.leftMulMatrix` does apply, it is
already used for the class-multiplication matrices in
`TauCeti/RepresentationTheory/CharacterTable/ClassSum/MultiplicationMatrix.lean`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "The good-prime structure theorem".
-/

public section

namespace TauCeti

/-! ### The left regular matrix -/

section Regular

variable {k G : Type*} [CommRing k] [Group G] [Fintype G] [DecidableEq G]

/-- The left regular representation of a finite group algebra, as matrices in the group basis:
`regularMatrix u` is the matrix of multiplication by `u` on the left, in the basis `{g}_{g : G}`. -/
noncomputable def regularMatrix : MonoidAlgebra k G →ₐ[k] Matrix G G k :=
  (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G k)).toAlgHom.comp
    (Algebra.lmul k (MonoidAlgebra k G))

/-- The `(i, j)` entry of the left regular matrix of `u` is the coefficient of `u` at `i * j⁻¹`. -/
theorem regularMatrix_apply (u : MonoidAlgebra k G) (i j : G) :
    regularMatrix u i j = u.coeff (i * j⁻¹) := by
  simp [regularMatrix, LinearMap.toMatrixAlgEquiv_apply, MonoidAlgebra.basis]

/-- **The regular trace reads off the coefficient at the identity.** Every diagonal entry of the
left regular matrix of `u` is the coefficient of `u` at `1`, so the trace is `|G|` times it. -/
theorem trace_regularMatrix (u : MonoidAlgebra k G) :
    Matrix.trace (regularMatrix u) = (Fintype.card G : k) * u.coeff 1 := by
  simp [Matrix.trace, Matrix.diag, regularMatrix_apply, Finset.card_univ]

end Regular

/-! ### Frobenius fixes the centre -/

section Frobenius

variable {K G : Type*} [Field K] [Fintype K] [Group G] [Fintype G]

/-- **Raising to the `|K|`-th power fixes the coefficient at the identity.** Over a finite field
`K` whose characteristic does not divide `|G|`, the identity coefficient of `u ^ |K|` is that of
`u`, for *every* `u` in the group algebra.

This is the trace identity `tr (M ^ |K|) = (tr M) ^ |K|` for the left regular matrix `M` of `u`,
combined with `a ^ |K| = a` in `K`. -/
theorem coeff_one_pow_card (hG : (Fintype.card G : K) ≠ 0) (u : MonoidAlgebra K G) :
    (u ^ Fintype.card K).coeff 1 = u.coeff 1 := by
  classical
  have h := FiniteField.trace_pow_card (regularMatrix (k := K) (G := G) u)
  rw [← map_pow, trace_regularMatrix, trace_regularMatrix, mul_pow, FiniteField.pow_card,
    FiniteField.pow_card] at h
  exact mul_left_cancel₀ hG h

/-- **The centre of the group algebra is fixed by the Frobenius of `K`.** Let `K` be a finite field
whose characteristic does not divide `|G|` and whose multiplicative order kills `G`, that is
`g ^ |K| = g` for every `g` (equivalently, the exponent of `G` divides `|K| - 1`). Then every
central element `y` of `K[G]` satisfies `y ^ |K| = y`.

The proof tests `y` against the group elements: `(y * g⁻¹) ^ |K| = y ^ |K| * g⁻¹` because `y` is
central and `g⁻¹` is fixed by the `|K|`-th power map, so `TauCeti.coeff_one_pow_card` applied to
`y * g⁻¹` compares the coefficients of `y ^ |K|` and `y` at `g`. -/
theorem pow_card_eq_self_of_mem_center (hG : (Fintype.card G : K) ≠ 0)
    (hexp : ∀ g : G, g ^ Fintype.card K = g) {y : MonoidAlgebra K G}
    (hy : y ∈ Subalgebra.center K (MonoidAlgebra K G)) :
    y ^ Fintype.card K = y := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have hcomm : Commute y (MonoidAlgebra.single g⁻¹ (1 : K)) :=
    (Subalgebra.mem_center_iff.mp hy _).symm
  have key := coeff_one_pow_card hG (y * MonoidAlgebra.single g⁻¹ (1 : K))
  rw [hcomm.mul_pow, MonoidAlgebra.single_pow, hexp g⁻¹, one_pow,
    MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_mul_single_apply] at key
  simpa using key

end Frobenius

/-! ### Elementary consequences of `x ^ q = x` -/

section PowSelf

/-- A commutative ring in which `x ^ q = x` for some `q > 1` has no nonzero nilpotents: iterating
gives `x ^ q ^ m = x`, and `q ^ m` outruns any nilpotency exponent. -/
theorem isReduced_of_pow_eq_self {R : Type*} [CommRing R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  have key : ∀ m : ℕ, x ^ q ^ m = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, h]
  have hle : n ≤ q ^ n := (Nat.lt_pow_self hq).le
  calc x = x ^ q ^ n := (key n).symm
    _ = x ^ n * x ^ (q ^ n - n) := by rw [← pow_add]; congr 1; omega
    _ = 0 := by rw [hn, zero_mul]

/-- **A field extension in which `x ^ |K| = x` is `K` itself.** Every element of `L` is then a root
of `X ^ |K| - X`, a nonzero polynomial of degree `|K|`, so `L` has at most `|K|` elements; it has
at least that many because `K` embeds in it. -/
theorem bijective_algebraMap_of_pow_card_eq_self {K L : Type*} [Field K] [Fintype K] [CommRing L]
    [IsDomain L] [Finite L] [Algebra K L] (h : ∀ x : L, x ^ Fintype.card K = x) :
    Function.Bijective (algebraMap K L) := by
  classical
  have := Fintype.ofFinite L
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, le_antisymm ?_ ?_⟩
  · exact Fintype.card_le_of_injective _ hinj
  · have hcard : 1 < Fintype.card K := Fintype.one_lt_card
    have hdeg : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial L).natDegree =
        Fintype.card K := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hcard]
    have hne : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial L) ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hdeg
      omega
    have hsub : (Finset.univ : Finset L) ⊆
        (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial L).roots.toFinset := by
      intro x _
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
      simp [h x]
    calc Fintype.card L = (Finset.univ : Finset L).card := (Finset.card_univ).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial L).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial L).natDegree :=
          Polynomial.card_roots' _
      _ = Fintype.card K := hdeg

end PowSelf

/-! ### The splitting of the centre -/

section Finiteness

variable (K G : Type*) [CommRing K] [Finite K] [Group G] [Finite G]

/-- The centre of a finite group algebra over a finite coefficient ring is finite: it is a finitely
generated module over a finite ring, by its class-sum basis. -/
instance instFiniteCenterMonoidAlgebra : Finite (Subalgebra.center K (MonoidAlgebra K G)) :=
  Module.finite_of_finite K

/-- The centre of a finite group algebra over a finite field is an Artinian ring. -/
instance instIsArtinianRingCenterMonoidAlgebra [IsArtinianRing K] :
    IsArtinianRing (Subalgebra.center K (MonoidAlgebra K G)) :=
  IsArtinianRing.of_finite K _

end Finiteness

section Splitting

variable {K G : Type*} [Field K] [Fintype K] [Group G] [Fintype G]
variable (hG : (Fintype.card G : K) ≠ 0) (hexp : ∀ g : G, g ^ Fintype.card K = g)

include hG hexp

/-- The `|K|`-th power map is the identity on the centre of `K[G]`, in the bundled form used by
the structure theorem. -/
theorem center_pow_card (z : Subalgebra.center K (MonoidAlgebra K G)) :
    z ^ Fintype.card K = z :=
  Subtype.ext (by simpa using pow_card_eq_self_of_mem_center hG hexp z.2)

/-- The centre of `K[G]` is reduced. -/
theorem isReduced_center : IsReduced (Subalgebra.center K (MonoidAlgebra K G)) :=
  isReduced_of_pow_eq_self Fintype.one_lt_card (center_pow_card hG hexp)

/-- **Every residue field of the centre of `K[G]` is `K` itself.** This is the sense in which `K`
splits `K[G]`: no residue field of `Z(K[G])` is a proper extension of `K`. -/
theorem bijective_algebraMap_center_quotient
    (I : MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G))) :
    Function.Bijective
      (algebraMap K (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal)) := by
  have hmax := I.isMaximal
  have : Finite (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  refine bijective_algebraMap_of_pow_card_eq_self (K := K)
    (L := Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) fun x => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  calc Ideal.Quotient.mk I.asIdeal z ^ Fintype.card K
      = Ideal.Quotient.mk I.asIdeal (z ^ Fintype.card K) := (map_pow _ _ _).symm
    _ = Ideal.Quotient.mk I.asIdeal z := by rw [center_pow_card hG hexp]

/-- **The centre of `K[G]` is split.** For a finite field `K` whose characteristic does not divide
`|G|` and whose multiplicative order kills `G`, the centre of `K[G]` is a product of copies of `K`,
indexed by its own maximal ideals.

The centre is reduced, hence a product of its residue fields by Artinian structure theory, and each
residue field is `K` by `TauCeti.bijective_algebraMap_center_quotient`. -/
noncomputable def centerAlgEquivPi :
    Subalgebra.center K (MonoidAlgebra K G) ≃ₐ[K]
      (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)) → K) :=
  haveI : IsReduced (Subalgebra.center K (MonoidAlgebra K G)) := isReduced_center hG hexp
  haveI : IsScalarTower K (Subalgebra.center K (MonoidAlgebra K G))
      (Subalgebra.center K (MonoidAlgebra K G)) := IsScalarTower.right
  haveI : ∀ I : MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)),
      IsScalarTower K (Subalgebra.center K (MonoidAlgebra K G))
        (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) := fun _ => inferInstance
  ((IsArtinianRing.equivPi _).restrictScalars K).trans
    (AlgEquiv.piCongrRight fun I =>
      (AlgEquiv.ofBijective (Algebra.ofId K _)
        (bijective_algebraMap_center_quotient hG hexp I)).symm)

/-- **The number of blocks is the number of conjugacy classes.** Comparing `K`-dimensions in
`TauCeti.centerAlgEquivPi` with the class-sum basis of the centre. -/
theorem card_maximalSpectrum_center :
    Nat.card (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G))) =
      Nat.card (ConjClasses G) := by
  have := Fintype.ofFinite (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)))
  rw [← finrank_center_monoidAlgebra K G, (centerAlgEquivPi hG hexp).toLinearEquiv.finrank_eq,
    Module.finrank_pi, Nat.card_eq_fintype_card]

/-- **The good-splitting structure theorem for a finite coefficient field.** The centre of `K[G]`
is `K`-algebra isomorphic to the functions on the conjugacy classes of `G`.

The indexing is by cardinality only: the canonical indexing of the factors is by the maximal ideals
of the centre (`TauCeti.centerAlgEquivPi`), which `TauCeti.card_maximalSpectrum_center` counts. -/
theorem nonempty_centerAlgEquiv_conjClasses :
    Nonempty (Subalgebra.center K (MonoidAlgebra K G) ≃ₐ[K] (ConjClasses G → K)) := by
  have := Fintype.ofFinite (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)))
  have := Fintype.ofFinite (ConjClasses G)
  have hcard := card_maximalSpectrum_center hG hexp
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  exact ⟨(centerAlgEquivPi hG hexp).trans
    (AlgEquiv.piCongrLeft' K (fun _ => K) (Fintype.equivOfCardEq hcard))⟩

end Splitting

end TauCeti
