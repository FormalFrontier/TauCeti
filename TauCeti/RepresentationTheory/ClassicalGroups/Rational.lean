/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower

/-!
# Rational and polynomial representations of the general linear group

A representation of `GL n ℂ` is **polynomial** when, in some basis of the carrier, every matrix
entry of `ρ g` is a polynomial in the entries `gᵢⱼ`, and **rational** when every entry is such a
polynomial divided by a power of `det g`.  The distinction is the one that separates the
representations arising inside tensor powers of the standard representation from those needing a
determinant twist: `TauCeti.stdRep` and its tensor, symmetric and exterior powers are polynomial, as
is `det ^ m` for `m ≥ 0`, whereas `det ^ (-1)` is rational.

The two definitions quantify existentially over a basis, and the content of this file is that this
costs nothing: the condition holds in *one* basis exactly when it holds in *every* basis
(`TauCeti.isRationalRep_iff_forall_mem_rationalFunctions` and its polynomial companion), because a
change of basis rewrites each entry as a fixed linear combination of the old entries, with
coefficients read off the two change-of-basis matrices and independent of `g`.  So the existential
form is a genuinely basis-independent property of `ρ`, and the coordinate-entry form is available
against whatever basis a computation has in hand.

The bookkeeping is carried by two algebras of functions on the group rather than by the
representations.  `TauCeti.GeneralLinearGroup.polynomialFunctions k n` collects the
`f : GL (Fin n) k → k` that evaluate some polynomial in the matrix entries, and
`TauCeti.GeneralLinearGroup.rationalFunctions k n` those `f` for which some determinant power
`det ^ m` makes `det ^ m * f` polynomial.  Both are `k`-subalgebras of the functions on the group,
and closure under sums, products and scalars is what reduces every argument below to a single entry
computation: the change-of-basis formula is a sum of scalar multiples, the entries of a tensor
product are products of entries, and a determinant power is one generator.

Stating the rational condition as "`det ^ m * f` is polynomial" rather than as "`f` is a polynomial
over `det ^ m`" is what keeps the subalgebra available over an arbitrary commutative ring: no
inverse is taken.  Over a field the two agree
(`TauCeti.GeneralLinearGroup.mem_rationalFunctions_iff_inv`), and it is the field form that the
representation-level definitions are stated in, matching the roadmap.

The two function algebras carry an arbitrary base ring, but the two *representation-level* notions
are stated over `ℂ`, as the roadmap pins them, and that restriction is not cosmetic.  Over a finite
field `k` the group `GL n k` is a finite set and every function on it is the evaluation of a
polynomial in the matrix entries, so `TauCeti.GeneralLinearGroup.polynomialFunctions k n` is then
the whole function algebra and every finite-dimensional representation would count as polynomial.
The coordinate-entry condition is faithful to the intended notion only over an infinite field, and
`ℂ` is the case the roadmap and the layers above this one use.

That the negative determinant powers are rational is
`TauCeti.GeneralLinearGroup.detZPow_mem_rationalFunctions`.  Whether a *given* representation fails
to be polynomial is a separate question, not addressed here; so is complete reducibility of rational
representations, which the roadmap assigns to the reductive-groups development rather than to this
layer.

## Main definitions

* `TauCeti.GeneralLinearGroup.entryEval`: evaluation of a polynomial in the matrix entries at a
  group element.
* `TauCeti.GeneralLinearGroup.detPoly`: the generic determinant, the polynomial that `entryEval`
  sends to `det g`.
* `TauCeti.GeneralLinearGroup.polynomialFunctions`, `TauCeti.GeneralLinearGroup.rationalFunctions`:
  the two subalgebras of functions on `GL n k` described above.
* `TauCeti.IsPolynomialRep`, `TauCeti.IsRationalRep`: a representation is polynomial, respectively
  rational, in coordinates.

## Main results

* `TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions` and
  `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`: **basis independence**, the entry
  condition against an arbitrary basis characterises the property.
* `TauCeti.IsPolynomialRep.isRationalRep`: a polynomial representation is rational.
* `TauCeti.isPolynomialRep_stdRep`: the standard representation is polynomial.
* `TauCeti.isRationalRep_detPowerRep` and `TauCeti.isPolynomialRep_detPowerRep_of_nonneg`:
  `det ^ m` is rational, and polynomial when `0 ≤ m`.
* `TauCeti.IsPolynomialRep.tprod` and `TauCeti.IsRationalRep.tprod`: both properties pass to tensor
  products.
* `TauCeti.IsPolynomialRep.of_surjective` and `TauCeti.IsRationalRep.of_surjective`: both
  properties pass to quotients.
* `TauCeti.isPolynomialRep_tensorPowerRep`, `TauCeti.isPolynomialRep_symPowerRep` and
  `TauCeti.isPolynomialRep_extPowerRep`: the functorial powers of the standard representation are
  polynomial.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 0, "Rational and polynomial representations".
-/

public section

open Matrix MvPolynomial

universe u v w x y z

namespace TauCeti

namespace GeneralLinearGroup

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Evaluation at the matrix entries of `g`: the ring homomorphism sending the variable indexed by
`(i, j)` to the entry `gᵢⱼ`. -/
noncomputable def entryEval (g : GL (Fin n) k) : MvPolynomial (Fin n × Fin n) k →+* k :=
  MvPolynomial.eval fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2

@[simp]
theorem entryEval_X (g : GL (Fin n) k) (p : Fin n × Fin n) :
    entryEval g (X p) = (g : Matrix (Fin n) (Fin n) k) p.1 p.2 := by
  simp [entryEval]

@[simp]
theorem entryEval_C (g : GL (Fin n) k) (c : k) : entryEval g (C c) = c := by
  simp [entryEval]

variable (k n)

/-- The **generic determinant**: the determinant of the matrix of variables, hence the polynomial
that `TauCeti.GeneralLinearGroup.entryEval` sends to `det g`. -/
noncomputable def detPoly : MvPolynomial (Fin n × Fin n) k :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) k).det

variable {k n}

@[simp]
theorem entryEval_detPoly (g : GL (Fin n) k) :
    entryEval g (detPoly k n) = (g : Matrix (Fin n) (Fin n) k).det := by
  rw [entryEval, detPoly, Matrix.eval_det_mvPolynomialX]
  rfl

variable (k n)

/-- **The polynomial functions on `GL n k`**: those `f : GL (Fin n) k → k` obtained by evaluating a
polynomial in the matrix entries.  A subalgebra, because the polynomials form one. -/
noncomputable def polynomialFunctions : Subalgebra k (GL (Fin n) k → k) where
  carrier := {f | ∃ P : MvPolynomial (Fin n × Fin n) k, ∀ g : GL (Fin n) k, f g = entryEval g P}
  mul_mem' := by
    rintro f₁ f₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
    exact ⟨P₁ * P₂, fun g => by simp [Pi.mul_apply, hP₁ g, hP₂ g]⟩
  one_mem' := ⟨1, fun g => by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
    exact ⟨P₁ + P₂, fun g => by simp [Pi.add_apply, hP₁ g, hP₂ g]⟩
  zero_mem' := ⟨0, fun g => by simp⟩
  algebraMap_mem' c := ⟨C c, fun g => by simp⟩

/-- **The rational functions on `GL n k`**: those `f : GL (Fin n) k → k` some determinant power of
which is polynomial in the matrix entries.  Stated multiplicatively, as `det ^ m * f` being
polynomial, so that no inverse is taken and the definition makes sense over a commutative ring;
`TauCeti.GeneralLinearGroup.mem_rationalFunctions_iff_inv` is the form with `(det ^ m)⁻¹` over a
field. -/
noncomputable def rationalFunctions : Subalgebra k (GL (Fin n) k → k) where
  carrier := {f | ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
    ∀ g : GL (Fin n) k, (g : Matrix (Fin n) (Fin n) k).det ^ m * f g = entryEval g P}
  mul_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨P₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_mul, ← hP₁ g, ← hP₂ g, pow_add, Pi.mul_apply]
    ring
  one_mem' := ⟨1, 0, fun g => by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨detPoly k n ^ m₂ * P₁ + detPoly k n ^ m₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, entryEval_detPoly, ← hP₁ g, ← hP₂ g, pow_add,
      Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, fun g => by simp⟩
  algebraMap_mem' c := ⟨C c, 0, fun g => by simp⟩

variable {k n}

theorem mem_polynomialFunctions {f : GL (Fin n) k → k} :
    f ∈ polynomialFunctions k n ↔
      ∃ P : MvPolynomial (Fin n × Fin n) k, ∀ g : GL (Fin n) k, f g = entryEval g P :=
  Iff.rfl

theorem mem_rationalFunctions {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k, (g : Matrix (Fin n) (Fin n) k).det ^ m * f g = entryEval g P :=
  Iff.rfl

/-- A polynomial function is rational. -/
theorem polynomialFunctions_le_rationalFunctions :
    polynomialFunctions k n ≤ rationalFunctions k n := by
  rintro f ⟨P, hP⟩
  exact ⟨P, 0, fun g => by simp [hP g]⟩

/-- The matrix entries themselves are polynomial functions. -/
@[simp]
theorem entry_mem_polynomialFunctions (i j : Fin n) :
    (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) ∈ polynomialFunctions k n :=
  ⟨X (i, j), fun g => by simp⟩

/-- The determinant is a polynomial function. -/
@[simp]
theorem det_mem_polynomialFunctions :
    (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det) ∈ polynomialFunctions k n :=
  ⟨detPoly k n, fun g => by simp⟩

/-- **Every integral determinant power is a rational function.**  For `0 ≤ m` it is even a
polynomial function, by `TauCeti.GeneralLinearGroup.det_mem_polynomialFunctions`. -/
@[simp]
theorem detZPow_mem_rationalFunctions (m : ℤ) :
    (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g ^ m : kˣ) : k))
      ∈ rationalFunctions k n := by
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    refine ⟨detPoly k n ^ m, 0, fun g => ?_⟩
    simp [zpow_natCast, Units.val_pow_eq_pow_val]
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = -(M : ℤ) := ⟨(-m).toNat, by omega⟩
    refine ⟨1, M, fun g => ?_⟩
    have hval : (g : Matrix (Fin n) (Fin n) k).det = ((Matrix.GeneralLinearGroup.det g : kˣ) : k) :=
      rfl
    rw [hval, map_one, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast,
      ← zpow_add (Matrix.GeneralLinearGroup.det g)]
    simp

end CommRing

section Field

variable {k : Type u} [Field k] {n : ℕ}

/-- Over a field, membership in the rational functions is the expected statement that `f` is a
polynomial in the matrix entries divided by a power of the determinant. -/
theorem mem_rationalFunctions_iff_inv {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k,
        f g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ * entryEval g P := by
  rw [mem_rationalFunctions]
  refine exists_congr fun P => exists_congr fun m => forall_congr' fun g => ?_
  have hdet : (g : Matrix (Fin n) (Fin n) k).det ^ m ≠ 0 :=
    pow_ne_zero _ (Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [eq_comm, eq_inv_mul_iff_mul_eq₀ hdet, eq_comm]

/-- **A finite family of rational functions has a common denominator**: a single determinant power
and a family of numerator polynomials express every member of the family.  This is what lets the
coordinate form of rationality carry a single exponent for the whole matrix. -/
theorem exists_forall_eq_inv_mul_of_forall_mem {ι : Type w} [Finite ι]
    {f : ι → GL (Fin n) k → k} (hf : ∀ i, f i ∈ rationalFunctions k n) :
    ∃ (P : ι → MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ (i : ι) (g : GL (Fin n) k),
        f i g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ * entryEval g (P i) := by
  have : Fintype ι := Fintype.ofFinite ι
  choose P m hPm using fun i => mem_rationalFunctions.mp (hf i)
  refine ⟨fun i => detPoly k n ^ (Finset.univ.sup m - m i) * P i, Finset.univ.sup m, fun i g => ?_⟩
  have hne : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hle : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
  rw [map_mul, map_pow, entryEval_detPoly, ← hPm i g,
    eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hne), ← mul_assoc, ← pow_add]
  congr 2
  omega

end Field

end GeneralLinearGroup

/-! ### Rationality and polynomiality of a representation -/

section Defs

open GeneralLinearGroup

variable {n : ℕ} {W : Type v} [AddCommGroup W] [Module ℂ W]

/-- **A polynomial representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g`.  The carrier is forced to be finite-dimensional, since
no basis indexed by `Fin (Module.finrank ℂ W)` exists otherwise.  The condition does not depend on
the basis: see `TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions`.

The base field is the roadmap's `ℂ` rather than a general field because the coordinate-entry
condition is faithful only over an infinite field: over a finite `k` the group `GL n k` is finite,
so every function on it — hence every matrix entry of every representation — is polynomial in the
entries of `g`. -/
def IsPolynomialRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j = entryEval g (P i j)

/-- **A rational representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g` divided by a fixed power of `det g`.  The condition does
not depend on the basis: see `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`.  The base
field is `ℂ` for the reason recorded on `TauCeti.IsPolynomialRep`. -/
def IsRationalRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
    (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ * entryEval g (P i j)

end Defs

section BasisChange

variable {k : Type u} [CommRing k] {G : Type z} [Monoid G] {W : Type v} [AddCommGroup W]
  [Module k W]
variable {V : Type y} [AddCommGroup V] [Module k V]

/-- **The entries of a quotient representation stay inside any subalgebra of functions.**  If `σ` is
the image of `ρ` under a surjective intertwining map, and every entry of `ρ` against a basis of the
source lies in a subalgebra `A` of the functions on the group, then so does every entry of `σ`
against a basis of the target. -/
theorem toMatrix_mem_of_toMatrix_mem_of_surjective (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (σ g) i j) ∈ A := by
  obtain ⟨w, hw⟩ := hf (c j)
  have key : (fun g => LinearMap.toMatrix c c (σ g) i j)
      = ∑ p : ι, ∑ l : ι, (b.repr w l * c.repr (f (b p)) i) •
          fun g => LinearMap.toMatrix b b (ρ g) p l := by
    funext g
    have hfg : σ g (c j) = f (ρ g w) := by
      rw [← hw]
      simpa using (LinearMap.congr_fun (f.isIntertwining' g) w).symm
    have hexp : ∀ p, b.repr (ρ g w) p = ∑ l, b.repr w l * LinearMap.toMatrix b b (ρ g) p l := by
      intro p
      conv_lhs => rw [← b.sum_repr w]
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix_apply]
    rw [LinearMap.toMatrix_apply, hfg]
    conv_lhs => rw [← b.sum_repr (ρ g w)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, hexp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [key]
  exact Subalgebra.sum_mem _ fun p _ =>
    Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (h p l) _

/-- **Changing basis keeps the entries inside any subalgebra of functions**: if every entry of `ρ`
against one basis lies in a subalgebra `A` of the functions on the group, so does every entry
against any other basis.  This is the mechanism behind basis independence of both
`TauCeti.IsPolynomialRep` and `TauCeti.IsRationalRep`. -/
theorem toMatrix_mem_of_toMatrix_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k W)
    (ρ : Representation k G W)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (ρ g) i j) ∈ A :=
  toMatrix_mem_of_toMatrix_mem_of_surjective A b c (.id ρ) (fun v => ⟨v, rfl⟩) h i j

end BasisChange

section BasisIndependence

open GeneralLinearGroup

variable {n : ℕ} {W : Type v} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **Polynomiality is basis independent.**  A representation is polynomial exactly when, against
*any* chosen basis, each matrix entry is a polynomial function of the entries of `g`. -/
theorem isPolynomialRep_iff_forall_mem_polynomialFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsPolynomialRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ polynomialFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, hP⟩
    exact fun i j => toMatrix_mem_of_toMatrix_mem (polynomialFunctions ℂ n) b₀ b ρ
      (fun p l => ⟨P p l, fun g => hP g p l⟩) i j
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ polynomialFunctions ℂ n :=
      fun i j => toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    choose P hP using fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) =>
      mem_polynomialFunctions.mp (hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), fun g i j => hP (i, j) g⟩

/-- **Rationality is basis independent.**  A representation is rational exactly when, against *any*
chosen basis, each matrix entry is a rational function of the entries of `g`. -/
theorem isRationalRep_iff_forall_mem_rationalFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsRationalRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ rationalFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, m, hP⟩
    refine fun i j => toMatrix_mem_of_toMatrix_mem _ b₀ b ρ (fun p l => ?_) i j
    exact mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ rationalFunctions ℂ n :=
      fun i j => toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    obtain ⟨P, m, hPm⟩ := exists_forall_eq_inv_mul_of_forall_mem
      (f := fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) => fun g =>
        LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) q.1 q.2)
      (fun q => hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), m, fun g i j => hPm (i, j) g⟩

/-- A polynomial representation is rational. -/
theorem IsPolynomialRep.isRationalRep (h : IsPolynomialRep ρ) : IsRationalRep ρ := by
  obtain ⟨b, P, hP⟩ := h
  exact (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j =>
    polynomialFunctions_le_rationalFunctions ⟨P i j, fun g => hP g i j⟩

/-- **A quotient of a polynomial representation is polynomial.**  This is the form in which the
functorial powers below inherit polynomiality from the tensor power. -/
theorem IsPolynomialRep.of_surjective {V : Type y} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsPolynomialRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsPolynomialRep σ := by
  obtain ⟨b, P, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isPolynomialRep_iff_forall_mem_polynomialFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    toMatrix_mem_of_toMatrix_mem_of_surjective (polynomialFunctions ℂ n) b (Module.finBasis ℂ V)
      f hf (fun p l => ⟨P p l, fun g => hP g p l⟩) i j

/-- **A quotient of a rational representation is rational.** -/
theorem IsRationalRep.of_surjective {V : Type y} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsRationalRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsRationalRep σ := by
  obtain ⟨b, P, m, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isRationalRep_iff_forall_mem_rationalFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    toMatrix_mem_of_toMatrix_mem_of_surjective (rationalFunctions ℂ n) b (Module.finBasis ℂ V)
      f hf (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

end BasisIndependence

/-! ### The basic examples -/

section Examples

open GeneralLinearGroup

variable (n : ℕ)

/-- **The standard representation is polynomial**: in the standard basis its matrix is `g`
itself. -/
@[simp]
theorem isPolynomialRep_stdRep : IsPolynomialRep (stdRep ℂ n) := by
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Pi.basisFun ℂ (Fin n))).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (stdRep ℂ n g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j := by
    funext g
    simp [Matrix.mulVec_single]
  rw [hentry]
  exact entry_mem_polynomialFunctions i j

variable {n}

/-- **The determinant powers are rational representations.** -/
@[simp]
theorem isRationalRep_detPowerRep (m : ℤ) : IsRationalRep (detPowerRep ℂ n m) := by
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n m g) i j)
      = fun g : GL (Fin n) ℂ => ((Matrix.GeneralLinearGroup.det g ^ m : ℂˣ) : ℂ) := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp
  rw [hentry]
  exact detZPow_mem_rationalFunctions m

/-- **The nonnegative determinant powers are polynomial representations.** -/
@[simp]
theorem isPolynomialRep_detPowerRep_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    IsPolynomialRep (detPowerRep ℂ n m) := by
  lift m to ℕ using hm
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n (m : ℤ) g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det ^ m := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp [zpow_natCast, Units.val_pow_eq_pow_val]
  rw [hentry]
  exact pow_mem det_mem_polynomialFunctions m

end Examples

section TensorProduct

open GeneralLinearGroup

variable {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module ℂ W] {W' : Type x} [AddCommGroup W'] [Module ℂ W']
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W} {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- Against a tensor product of bases, the entries of a tensor product of representations are the
products of the entries of the two factors: the Kronecker product, read entrywise. -/
private theorem toMatrix_tprod {ι : Type y} [Fintype ι] [DecidableEq ι]
    {κ : Type z} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ W) (c : Module.Basis κ ℂ W') (g : GL (Fin n) ℂ) (i j : ι × κ) :
    LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j
      = LinearMap.toMatrix b b (ρ g) i.1 j.1 * LinearMap.toMatrix c c (σ g) i.2 j.2 := by
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  simp [Matrix.kroneckerMap_apply]

/-- **A tensor product of polynomial representations is polynomial.** -/
theorem IsPolynomialRep.tprod (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    IsPolynomialRep (ρ.tprod σ) := by
  obtain ⟨b, P, hP⟩ := hρ
  obtain ⟨c, Q, hQ⟩ := hσ
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions (b.tensorProduct c)).mpr fun i j => ?_
  have hentry : (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c)
        ((ρ.tprod σ) g) i j)
      = (fun g => LinearMap.toMatrix b b (ρ g) i.1 j.1) *
        fun g => LinearMap.toMatrix c c (σ g) i.2 j.2 :=
    funext fun g => toMatrix_tprod b c g i j
  rw [hentry]
  exact mul_mem ⟨P i.1 j.1, fun g => hP g i.1 j.1⟩ ⟨Q i.2 j.2, fun g => hQ g i.2 j.2⟩

/-- **A tensor product of rational representations is rational.** -/
theorem IsRationalRep.tprod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.tprod σ) := by
  obtain ⟨b, P, mP, hP⟩ := hρ
  obtain ⟨c, Q, mQ, hQ⟩ := hσ
  refine (isRationalRep_iff_forall_mem_rationalFunctions (b.tensorProduct c)).mpr fun i j => ?_
  have hentry : (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c)
        ((ρ.tprod σ) g) i j)
      = (fun g => LinearMap.toMatrix b b (ρ g) i.1 j.1) *
        fun g => LinearMap.toMatrix c c (σ g) i.2 j.2 :=
    funext fun g => toMatrix_tprod b c g i j
  rw [hentry]
  exact mul_mem (mem_rationalFunctions_iff_inv.mpr ⟨P i.1 j.1, mP, fun g => hP g i.1 j.1⟩)
    (mem_rationalFunctions_iff_inv.mpr ⟨Q i.2 j.2, mQ, fun g => hQ g i.2 j.2⟩)

end TensorProduct

/-! ### The functorial powers of the standard representation -/

section FunctorialPowers

open GeneralLinearGroup

variable (n d : ℕ)

/-- **The tensor powers of the standard representation are polynomial**: against the basis of pure
tensors of standard basis vectors, an entry of the tensor power is the product of the `d` entries
of `g` listed by the two indices. -/
@[simp]
theorem isPolynomialRep_tensorPowerRep : IsPolynomialRep (tensorPowerRep ℂ n d) := by
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun ℂ (Fin n))).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun ℂ (Fin n))
        (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun ℂ (Fin n))
        (tensorPowerRep ℂ n d g) i j)
      = ∏ l : Fin d, fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) (i l) (j l) := by
    funext g
    rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
      Representation.tensorPower_apply, PiTensorProduct.map_tprod,
      Basis.piTensorProduct_repr_tprod_apply]
    simp [Matrix.mulVec_single]
  rw [hentry]
  exact prod_mem fun l _ => entry_mem_polynomialFunctions (i l) (j l)

/-- **The symmetric powers of the standard representation are polynomial**. -/
@[simp]
theorem isPolynomialRep_symPowerRep : IsPolynomialRep (symPowerRep ℂ n d) :=
  (isPolynomialRep_tensorPowerRep n d).of_surjective
    (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (SymmetricPower.mk ℂ (Fin d) (Fin n → ℂ))
      fun g x => by simp)
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin d) (Fin n → ℂ)))

/-- **The exterior powers of the standard representation are polynomial**. -/
@[simp]
theorem isPolynomialRep_extPowerRep : IsPolynomialRep (extPowerRep ℂ n d) :=
  (isPolynomialRep_tensorPowerRep n d).of_surjective
    (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (exteriorPower.fromTensorPower ℂ (Fin n → ℂ) d) fun g x => by
        simpa using (LinearMap.congr_fun
          (exteriorPower.map_comp_fromTensorPower d (stdRep ℂ n g)) x).symm)
    (exteriorPower.fromTensorPower_surjective d)

end FunctorialPowers

end TauCeti
