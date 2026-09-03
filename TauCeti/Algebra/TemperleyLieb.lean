/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Temperley-Lieb algebra

The Temperley-Lieb algebra `TemperleyLieb R δ n` on `n` strands, over a commutative semiring `R` and
with loop value `δ : R`, is the associative unital `R`-algebra on generators `e 0, …, e (n - 2)`
subject to

* `e i * e i = δ • e i`,
* `e i * e j * e i = e i` when the two generators share a strand, that is `|i - j| = 1`, and
* `e i * e j = e j * e i` when they are disjoint, that is `|i - j| ≥ 2`.

Geometrically `e i` is the planar tangle that caps off the strands `i` and `i + 1` at the top and
at the bottom, the first relation records that closing a loop multiplies by `δ`, and the second
records the isotopy that straightens a zig-zag.

The algebra is built here as a quotient of the free algebra by the relations, which is what makes
the universal property `TauCeti.TemperleyLieb.lift` available: an assignment of the
generators satisfying the three relations extends uniquely to an algebra map out of
`TemperleyLieb R δ n`. That universal property is the whole point of the construction.

## Indexing convention

`TemperleyLieb R δ n` is indexed by the number `n` of *strands*, so its generators are indexed by
`Fin (n - 1)`. In particular `TemperleyLieb R δ 0` and `TemperleyLieb R δ 1` are the base ring `R`
(`TauCeti.TemperleyLieb.algEquivOfLeOne`), and the adjacency relation is vacuous for `n ≤ 2`.

## Non-degeneracy

A presentation is only worth having if it does not collapse. Two theorems here rule that out:
the base ring embeds (`TauCeti.TemperleyLieb.algebraMap_injective`, from the
augmentation killing every generator), the generator of the two-strand algebra is nonzero over a
nontrivial base ring (`TauCeti.TemperleyLieb.e_ne_zero_two`, from an explicit
two-dimensional representation). The latter assumes `[Nontrivial R]`, as it must: over the zero
ring the whole algebra is zero.

That `e i ≠ 0` for *every* `n` over a nontrivial base ring — indeed that `TemperleyLieb R δ n` is
free of rank the Catalan number `catalan n` on the planar-matching diagrams, so that `TL_1` has
basis `1` and `TL_2` has basis `1, e 0` — is the fundamental structure theorem of the algebra, and
it is not proved here: it needs the diagram basis, which is a separate construction. The
two-strand case above is the part of it that the presentation alone can see.

## Main definitions

* `TauCeti.TemperleyLieb.Rel`: the three defining relations, as a relation on the free
  algebra.
* `TauCeti.TemperleyLieb`: the Temperley-Lieb algebra on `n` strands with loop value
  `δ`.
* `TauCeti.TemperleyLieb.e`: the generators.
* `TauCeti.TemperleyLieb.lift`: the universal property.
* `TauCeti.TemperleyLieb.aug`: the augmentation killing every generator.
* `TauCeti.TemperleyLieb.algEquivOfLeOne`: the algebra on at most one strand is the
  base ring.
* `TauCeti.TemperleyLieb.crossing`: the Kauffman-bracket expansion `α • 1 + β • e i`
  of a crossing.

## Main results

* `TauCeti.TemperleyLieb.e_mul_self`, `TauCeti.TemperleyLieb.e_mul_e_mul_e` and
  `TauCeti.TemperleyLieb.commute_e`: the three defining relations.
* `TauCeti.TemperleyLieb.lift_e` and `TauCeti.TemperleyLieb.hom_ext`: the
  computation rule and uniqueness half of the universal property.
* `TauCeti.TemperleyLieb.adjoin_range_e`: the generators generate.
* `TauCeti.TemperleyLieb.algebraMap_injective`: the base ring embeds.
* `TauCeti.TemperleyLieb.crossing_mul_crossing_swap_eq_one` and
  `TauCeti.TemperleyLieb.crossing_braid`: a crossing is invertible and crossings satisfy the braid
  relation under their respective scalar hypotheses.
* `TauCeti.TemperleyLieb.e_ne_zero_two`: non-degeneracy on two strands.

## References

* H. N. V. Temperley, E. H. Lieb, *Relations between the "percolation" and "colouring" problem …*,
  Proc. Roy. Soc. London Ser. A 322 (1971), 251-280.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103-111.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and Jones polynomial).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* The quotient presentation and universal-property API follow the construction pattern in
  `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`.

This is Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), whose knot-polynomial bullet asks for the Jones
polynomial "from the Kauffman bracket on a diagram and from the Temperley-Lieb / Jones
representation of a braid".
-/

public section

namespace TauCeti

variable (R : Type*) (δ : R) (n : ℕ)

namespace TemperleyLieb

/-- The defining relations of the Temperley-Lieb algebra on `n` strands with loop value `δ`, as a
relation on the free algebra over the generators `Fin (n - 1)`: a generator is idempotent up to
`δ`, two generators sharing a strand satisfy `e i * e j * e i = e i`, and two disjoint generators
commute. -/
inductive Rel [CommSemiring R] : FreeAlgebra R (Fin (n - 1)) → FreeAlgebra R (Fin (n - 1)) → Prop
  | mul_self (i : Fin (n - 1)) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R i) (δ • FreeAlgebra.ι R i)
  | adjacent {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j * FreeAlgebra.ι R i) (FreeAlgebra.ι R i)
  | distant {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j) (FreeAlgebra.ι R j * FreeAlgebra.ι R i)

end TemperleyLieb

/-- The Temperley-Lieb algebra on `n` strands over `R` with loop value `δ`: the free `R`-algebra
on `Fin (n - 1)` modulo `TauCeti.TemperleyLieb.Rel`. -/
@[expose] def TemperleyLieb [CommSemiring R] : Type _ := RingQuot (TemperleyLieb.Rel R δ n)

instance [CommSemiring R] : Semiring (TemperleyLieb R δ n) :=
  inferInstanceAs (Semiring (RingQuot (TemperleyLieb.Rel R δ n)))

instance {S : Type*} [CommRing S] (ε : S) (m : ℕ) : Ring (TemperleyLieb S ε m) :=
  inferInstanceAs (Ring (RingQuot (TemperleyLieb.Rel S ε m)))

instance [CommSemiring R] : Algebra R (TemperleyLieb R δ n) :=
  inferInstanceAs (Algebra R (RingQuot (TemperleyLieb.Rel R δ n)))

namespace TemperleyLieb

variable [CommSemiring R]

/-- The quotient map from the free algebra to the Temperley-Lieb algebra. -/
def mkAlgHom : FreeAlgebra R (Fin (n - 1)) →ₐ[R] TemperleyLieb R δ n :=
  RingQuot.mkAlgHom R (Rel R δ n)

variable {R n}

/-- The generator `e i` of the Temperley-Lieb algebra, the planar tangle capping off the strands
`i` and `i + 1` at the top and at the bottom. -/
def e (i : Fin (n - 1)) : TemperleyLieb R δ n :=
  mkAlgHom R δ n (FreeAlgebra.ι R i)

variable {δ}

/-- The quotient map takes each free-algebra generator to the corresponding Temperley-Lieb
generator. -/
@[simp]
theorem mkAlgHom_ι (i : Fin (n - 1)) : mkAlgHom R δ n (FreeAlgebra.ι R i) = e δ i := (rfl)

/-- Every element of the Temperley-Lieb algebra is represented by a free-algebra element. -/
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R δ n) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Related elements of the free algebra have the same image in the Temperley-Lieb algebra. -/
theorem mkAlgHom_rel {x y : FreeAlgebra R (Fin (n - 1))} (h : Rel R δ n x y) :
    mkAlgHom R δ n x = mkAlgHom R δ n y :=
  RingQuot.mkAlgHom_rel R h

/-- A generator is idempotent up to the loop value: closing a loop multiplies by `δ`. -/
@[simp]
theorem e_mul_self (i : Fin (n - 1)) : e δ i * e δ i = δ • e δ i := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using mkAlgHom_rel (Rel.mul_self (δ := δ) i)

/-- Two generators sharing a strand straighten a zig-zag. -/
theorem e_mul_e_mul_e {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    e δ i * e δ j * e δ i = e δ i := by
  simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.adjacent (R := R) (δ := δ) h)

/-- Two disjoint generators commute. -/
theorem commute_e {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (e δ i) (e δ j) := by
  rw [commute_iff_eq]
  simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.distant (R := R) (δ := δ) h)

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The universal property of the Temperley-Lieb presentation: a family in an `R`-algebra
satisfying the three defining relations extends to an algebra map out of `TemperleyLieb R δ n`. -/
def lift (f : Fin (n - 1) → A) (hself : ∀ i, f i * f i = δ • f i)
    (hadj : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i → f i * f j * f i = f i)
    (hdist : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → f i * f j = f j * f i) :
    TemperleyLieb R δ n →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R f, by
    rintro x y (i | @⟨i, j, h⟩ | @⟨i, j, h⟩)
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply] using hself i
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hadj h
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hdist h⟩

/-- The algebra map built by `TauCeti.TemperleyLieb.lift` takes each generator to its
prescribed value. -/
@[simp]
theorem lift_e (f : Fin (n - 1) → A) (hself) (hadj) (hdist) (i : Fin (n - 1)) :
    lift (δ := δ) f hself hadj hdist (e δ i) = f i := by
  have h : lift (δ := δ) f hself hadj hdist (e δ i) = FreeAlgebra.lift R f (FreeAlgebra.ι R i) :=
    RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _
  rw [h, FreeAlgebra.lift_ι_apply]

/-- Two algebra maps out of the Temperley-Lieb algebra agreeing on the generators are equal. -/
theorem hom_ext {F G : TemperleyLieb R δ n →ₐ[R] A} (h : ∀ i, F (e δ i) = G (e δ i)) :
    F = G :=
  RingQuot.ringQuot_ext' R F G <| FreeAlgebra.hom_ext (funext h)

end Lift

/-- The generators generate. -/
theorem adjoin_range_e : Algebra.adjoin R (Set.range (e δ (n := n))) = ⊤ := by
  have hrange : Set.range (e δ (n := n))
      = mkAlgHom R δ n '' Set.range (FreeAlgebra.ι R (X := Fin (n - 1))) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => mkAlgHom_ι i)
  rw [hrange, ← AlgHom.map_adjoin, FreeAlgebra.adjoin_range_ι, Algebra.map_top]
  exact (AlgHom.range_eq_top _).2 mkAlgHom_surjective

section Augmentation

/-- The augmentation of the Temperley-Lieb algebra, killing every generator. It is a retraction of
the structure map, so it witnesses that the presentation does not collapse the base ring. -/
def aug : TemperleyLieb R δ n →ₐ[R] R :=
  lift (fun _ => 0) (by simp) (by simp) (by simp)

/-- The augmentation kills every generator. -/
@[simp]
theorem aug_e (i : Fin (n - 1)) : aug (e δ i) = (0 : R) :=
  lift_e _ _ _ _ i

/-- The base ring embeds into the Temperley-Lieb algebra. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (TemperleyLieb R δ n)) := by
  intro x y hxy
  simpa using congrArg (aug (δ := δ) (n := n)) hxy

instance [Nontrivial R] : Nontrivial (TemperleyLieb R δ n) :=
  algebraMap_injective.nontrivial

end Augmentation

section SmallCases

variable (δ)

/-- On at most one strand there are no generators, so the Temperley-Lieb algebra is the base
ring. This matches the triviality of `TauCeti.BraidGroup 0` and `TauCeti.BraidGroup 1`. -/
def algEquivOfLeOne (h : n ≤ 1) : TemperleyLieb R δ n ≃ₐ[R] R :=
  have : IsEmpty (Fin (n - 1)) := ⟨fun i => absurd i.isLt (by omega)⟩
  AlgEquiv.ofAlgHom aug (Algebra.ofId R _) (AlgHom.ext fun x => by simp)
    (hom_ext fun i => isEmptyElim i)

/-- On at most one strand, the forward map of `algEquivOfLeOne` is the augmentation. -/
@[simp]
theorem algEquivOfLeOne_apply (h : n ≤ 1) (x : TemperleyLieb R δ n) :
    algEquivOfLeOne δ h x = aug x := by
  simp only [algEquivOfLeOne, AlgEquiv.ofAlgHom_apply]

/-- On at most one strand, the inverse of `algEquivOfLeOne` is the algebra structure map. -/
@[simp]
theorem algEquivOfLeOne_symm_apply (h : n ≤ 1) (r : R) :
    (algEquivOfLeOne δ h).symm r = algebraMap R (TemperleyLieb R δ n) r := by
  simp only [algEquivOfLeOne, AlgEquiv.ofAlgHom_symm_apply, Algebra.ofId_apply]

/-- The matrix `!![0, 0; 1, δ]`, idempotent up to `δ`: the matrix of left multiplication by the
single Temperley-Lieb generator on two strands, read in the pair `(1, e)`. -/
private def twoStrandMatrix : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, δ]

/-- The two-strand matrix is idempotent up to `δ`, which is the sole Temperley-Lieb relation on
two strands. -/
private theorem twoStrandMatrix_mul_self :
    twoStrandMatrix δ * twoStrandMatrix δ = δ • twoStrandMatrix δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoStrandMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- A two-dimensional representation of the two-strand Temperley-Lieb algebra. On two strands
there is a single generator and the adjacency and distance relations are vacuous, so the sole
condition to check is that the matrix be idempotent up to `δ`. -/
def twoStrandRep : TemperleyLieb R δ 2 →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  lift (fun _ => twoStrandMatrix δ) (fun _ => twoStrandMatrix_mul_self δ)
    (fun {i j} h => absurd h (by have := i.isLt; have := j.isLt; omega))
    (fun {i j} h => absurd h (by have := i.isLt; have := j.isLt; omega))

/-- The two-dimensional representation takes the single generator to the two-strand matrix. -/
@[simp]
theorem twoStrandRep_e (i : Fin (2 - 1)) : twoStrandRep δ (e δ i) = !![0, 0; 1, δ] := by
  rw [twoStrandRep, lift_e]
  rfl

variable {δ}

/-- The generator of the two-strand Temperley-Lieb algebra is nonzero: the presentation does not
collapse. -/
theorem e_ne_zero_two [Nontrivial R] (i : Fin (2 - 1)) : e δ i ≠ 0 := by
  intro h
  have h' : (!![0, 0; 1, δ] : Matrix (Fin 2) (Fin 2) R) 1 0
      = (0 : Matrix (Fin 2) (Fin 2) R) 1 0 := by
    rw [← twoStrandRep_e δ i, h, map_zero]
  simp at h'

end SmallCases

section Kauffman

variable (δ) in
/-- The Kauffman-bracket expansion `α • 1 + β • e i` of a crossing: `α` times the identity tangle
plus `β` times the tangle that caps off the two strands. -/
def crossing (α β : R) (i : Fin (n - 1)) : TemperleyLieb R δ n := α • 1 + β • e δ i

/-- A crossing is the indicated linear combination of the identity and one generator. -/
@[simp]
theorem crossing_def (α β : R) (i : Fin (n - 1)) :
    crossing δ α β i = α • 1 + β • e δ i := (rfl)

/-- The product of two crossings, expanded in the four terms `1`, `e i`, `e j`, `e i * e j`. -/
theorem crossing_mul_crossing (x y z w : R) (i j : Fin (n - 1)) :
    crossing δ x y i * crossing δ z w j
      = (x * z) • 1 + (x * w) • e δ j + (y * z) • e δ i + (y * w) • (e δ i * e δ j) := by
  rw [crossing_def, crossing_def]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

variable {α β : R}

/-- Crossings with arbitrary coefficients on disjoint pairs of strands commute. -/
theorem crossing_mul_crossing_comm (x y z w : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    crossing δ x y i * crossing δ z w j = crossing δ z w j * crossing δ x y i := by
  rw [crossing_mul_crossing, crossing_mul_crossing, (commute_e h).eq]
  module

end Kauffman

end TemperleyLieb

end TauCeti

namespace TauCeti.TemperleyLieb

variable (R : Type*) (δ : R) (n : ℕ)
variable {R δ n}

section Kauffman

variable [CommSemiring R]

/-- Swapping the two coefficients inverts a crossing when the coefficients are inverse and obey
the indicated polynomial relation with the loop value. -/
theorem crossing_mul_crossing_swap_eq_one_of_polynomial (hαβ : α * β = 1)
    (hpoly : α ^ 2 + α * β * δ + β ^ 2 = 0)
    (i : Fin (n - 1)) : crossing δ α β i * crossing δ β α i = 1 := by
  rw [crossing_mul_crossing, e_mul_self, smul_smul]
  match_scalars
  · simpa only [mul_one] using hαβ
  · calc
      α * α * 1 + β * β * 1 + β * α * δ * 1 = α ^ 2 + α * β * δ + β ^ 2 := by
        ring
      _ = 0 := hpoly

/-- The triple product of crossings on two adjacent pairs of strands, reduced using the
Temperley-Lieb relations to a linear combination of five standard monomials. -/
theorem crossing_mul_crossing_mul_crossing {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    crossing δ α β i * crossing δ α β j * crossing δ α β i
      = (α ^ 3) • 1 + (2 * α ^ 2 * β + α * β ^ 2 * δ + β ^ 3) • e δ i
        + (α ^ 2 * β) • e δ j + (α * β ^ 2) • (e δ i * e δ j)
        + (α * β ^ 2) • (e δ j * e δ i) := by
  have hEF : e δ i * e δ j * e δ i = e δ i := e_mul_e_mul_e h
  rw [crossing_mul_crossing, crossing_def]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
    hEF, e_mul_self]
  match_scalars
  all_goals ring

/-- Crossings on two strands sharing a strand satisfy the braid relation when their coefficients
obey the natural polynomial relation. -/
theorem crossing_braid (hpoly : β * (α ^ 2 + α * β * δ + β ^ 2) = 0)
    {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    crossing δ α β i * crossing δ α β j * crossing δ α β i
      = crossing δ α β j * crossing δ α β i * crossing δ α β j := by
  have hcoeff : 2 * α ^ 2 * β + α * β ^ 2 * δ + β ^ 3 = α ^ 2 * β := by
    calc
      2 * α ^ 2 * β + α * β ^ 2 * δ + β ^ 3
          = α ^ 2 * β + β * (α ^ 2 + α * β * δ + β ^ 2) := by ring
      _ = α ^ 2 * β := by rw [hpoly, add_zero]
  rw [crossing_mul_crossing_mul_crossing h, crossing_mul_crossing_mul_crossing h.symm, hcoeff]
  abel

end Kauffman

section KauffmanRing

variable [CommRing R]

/-- Swapping the two coefficients inverts a crossing, provided the coefficients are inverse to
one another and the loop value is `-(α ^ 2 + β ^ 2)`. -/
theorem crossing_mul_crossing_swap_eq_one (hαβ : α * β = 1) (hδ : δ = -(α ^ 2 + β ^ 2))
    (i : Fin (n - 1)) : crossing δ α β i * crossing δ β α i = 1 := by
  apply crossing_mul_crossing_swap_eq_one_of_polynomial hαβ
  rw [hδ, hαβ]
  ring

end KauffmanRing

end TauCeti.TemperleyLieb
