/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Complex.Basic
-- The two subalgebras of functions on `GL n k` the definitions below are stated against; this
-- module also supplies `MvPolynomial.eval`, in which their coordinate form is written.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions
-- The subalgebra-generic behaviour of matrix coefficients under change of basis, quotients,
-- tensor products and tensor powers; this module also supplies `Basis.piTensorProduct`, the basis
-- the tensor-power results below are stated against.
public import TauCeti.RepresentationTheory.MatrixCoefficients
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
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
coefficients independent of `g`.  So the existential form is a genuinely basis-independent property
of `ρ`, and the coordinate-entry form is available against whatever basis a computation has in hand.

The bookkeeping is carried by two algebras of functions on the group rather than by the
representations.  `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` collects the
`f : GL (Fin n) k → k` that evaluate some polynomial in the matrix entries, and
`TauCeti.Matrix.GeneralLinearGroup.rationalFunctions k n` those `f` for which some determinant power
`det ^ m` makes `det ^ m * f` polynomial.  Both are `k`-subalgebras of the functions on the group,
and closure under sums, products and scalars is what reduces every argument below to a single entry
computation: the change-of-basis formula is a sum of scalar multiples, the entries of a tensor
product are products of entries, and a determinant power is one generator.  Those entry computations
are themselves subalgebra-generic, and live in `TauCeti.RepresentationTheory.MatrixCoefficients`.

The two function algebras carry an arbitrary base ring, but the two *representation-level* notions
are stated over `ℂ`, as the roadmap pins them, and that restriction is not cosmetic.  Over a finite
field `k` the group `GL n k` is a finite set and every function on it is the evaluation of a
polynomial in the matrix entries, so `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` is
then the whole function algebra and every finite-dimensional representation would count as
polynomial.  The coordinate-entry condition is faithful to the intended notion only over an infinite
field, and `ℂ` is the case the roadmap and the layers above this one use.

That the negative determinant powers are rational is
`TauCeti.Matrix.GeneralLinearGroup.det_zpow_mem_rationalFunctions`.  Whether a *given*
representation fails to be polynomial is a separate question, not addressed here; so is complete
reducibility of rational representations, which the roadmap assigns to the reductive-groups
development rather than to this layer.

## Main definitions

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
* `TauCeti.IsPolynomialRep.tensorPower`, `TauCeti.IsPolynomialRep.symmetricPower` and
  `TauCeti.IsPolynomialRep.exteriorPower`, together with `TauCeti.IsRationalRep.tensorPower`,
  `TauCeti.IsRationalRep.symmetricPower` and `TauCeti.IsRationalRep.exteriorPower`: both properties
  pass to the functorial powers, whence `TauCeti.isPolynomialRep_tensorPowerRep`,
  `TauCeti.isPolynomialRep_symPowerRep` and `TauCeti.isPolynomialRep_extPowerRep` for the standard
  representation.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 0, "Rational and polynomial representations".
* [Suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/Suggested.lean),
  where `IsRationalRep` is pinned in this coordinate-entry form.
-/

public section

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

universe u v w x y z

namespace TauCeti

/-! ### Rationality and polynomiality of a representation -/

section Defs

variable {n : ℕ} {W : Type v} [AddCommGroup W] [Module ℂ W]

/-- **A polynomial representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g`.  The carrier is forced to be finite-dimensional, since
no basis indexed by `Fin (Module.finrank ℂ W)` exists otherwise
(`TauCeti.IsPolynomialRep.finite`).  The condition does not depend on the basis: see
`TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions`.

The base field is the roadmap's `ℂ` rather than a general field because the coordinate-entry
condition is faithful only over an infinite field: over a finite `k` the group `GL n k` is finite,
so every function on it — hence every matrix entry of every representation — is polynomial in the
entries of `g`. -/
def IsPolynomialRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsPolynomialRep`, as a lemma. -/
theorem isPolynomialRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsPolynomialRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
      ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- **A rational representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g` divided by a fixed power of `det g`.  The carrier is
forced to be finite-dimensional (`TauCeti.IsRationalRep.finite`), and the condition does not depend
on the basis: see `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`.  The base field is `ℂ`
for the reason recorded on `TauCeti.IsPolynomialRep`. -/
def IsRationalRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
    (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
          MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalRep`, as a lemma. -/
theorem isRationalRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsRationalRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
      (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
            MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- The carrier of a polynomial representation is finite-dimensional. -/
theorem IsPolynomialRep.finite (h : IsPolynomialRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- The carrier of a rational representation is finite-dimensional. -/
theorem IsRationalRep.finite (h : IsRationalRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

end Defs

section BasisIndependence

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
    exact fun i j => Representation.toMatrix_mem_of_toMatrix_mem (polynomialFunctions ℂ n) b₀ b ρ
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ polynomialFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
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
    refine fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b₀ b ρ (fun p l => ?_) i j
    exact mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ rationalFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    obtain ⟨P, m, hPm⟩ := exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions
      (f := fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) => fun g =>
        LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) q.1 q.2)
      (fun q => hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), m, fun g i j => hPm (i, j) g⟩

/-- A polynomial representation is rational. -/
theorem IsPolynomialRep.isRationalRep (h : IsPolynomialRep ρ) : IsRationalRep ρ := by
  obtain ⟨b, P, hP⟩ := h
  exact (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j =>
    polynomialFunctions_le_rationalFunctions
      (mem_polynomialFunctions.mpr ⟨P i j, fun g => hP g i j⟩)

/-- **A quotient of a polynomial representation is polynomial.**  This is the form in which the
functorial powers below inherit polynomiality from the tensor power. -/
theorem IsPolynomialRep.of_surjective {V : Type y} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsPolynomialRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsPolynomialRep σ := by
  obtain ⟨b, P, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isPolynomialRep_iff_forall_mem_polynomialFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (polynomialFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A quotient of a rational representation is rational.** -/
theorem IsRationalRep.of_surjective {V : Type y} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsRationalRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsRationalRep σ := by
  obtain ⟨b, P, m, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isRationalRep_iff_forall_mem_rationalFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (rationalFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

end BasisIndependence

/-! ### The basic examples -/

section Examples

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
  exact det_zpow_mem_rationalFunctions m

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

variable {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module ℂ W] {W' : Type x} [AddCommGroup W'] [Module ℂ W']
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W} {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **A tensor product of polynomial representations is polynomial.** -/
theorem IsPolynomialRep.tprod (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    IsPolynomialRep (ρ.tprod σ) := by
  obtain ⟨b, P, hP⟩ := hρ
  obtain ⟨c, Q, hQ⟩ := hσ
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩)
    (fun p l => mem_polynomialFunctions.mpr ⟨Q p l, fun g => hQ g p l⟩) i j

/-- **A tensor product of rational representations is rational.** -/
theorem IsRationalRep.tprod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.tprod σ) := by
  obtain ⟨b, P, mP, hP⟩ := hρ
  obtain ⟨c, Q, mQ, hQ⟩ := hσ
  refine (isRationalRep_iff_forall_mem_rationalFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, mP, fun g => hP g p l⟩)
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨Q p l, mQ, fun g => hQ g p l⟩) i j

end TensorProduct

/-! ### The functorial powers -/

section FunctorialPowers

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **A tensor power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.tensorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.tensorPower d) := by
  obtain ⟨b, P, hP⟩ := h
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A tensor power of a rational representation is rational.** -/
theorem IsRationalRep.tensorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.tensorPower d) := by
  obtain ⟨b, P, m, hP⟩ := h
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

/-- The canonical map onto the symmetric power, as a surjective intertwining map out of the tensor
power.  It is what makes the symmetric power inherit polynomiality and rationality. -/
private noncomputable def symmetricPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.symmetricPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (SymmetricPower.mk ℂ (Fin d) W) fun g x => by
    simp

private theorem symmetricPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (symmetricPowerIntertwiningMap ρ d) :=
  LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin d) W)

/-- The canonical map onto the exterior power, as a surjective intertwining map out of the tensor
power.  It is what makes the exterior power inherit polynomiality and rationality. -/
private noncomputable def exteriorPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.exteriorPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (exteriorPower.fromTensorPower ℂ W d)
    fun g x => by
      simpa using (LinearMap.congr_fun (exteriorPower.map_comp_fromTensorPower d (ρ g)) x).symm

private theorem exteriorPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (exteriorPowerIntertwiningMap ρ d) :=
  exteriorPower.fromTensorPower_surjective d

/-- **A symmetric power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.symmetricPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **A symmetric power of a rational representation is rational.** -/
theorem IsRationalRep.symmetricPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.exteriorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a rational representation is rational.** -/
theorem IsRationalRep.exteriorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

variable (n d : ℕ)

/-- **The tensor powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_tensorPowerRep : IsPolynomialRep (tensorPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).tensorPower d

/-- **The symmetric powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_symPowerRep : IsPolynomialRep (symPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).symmetricPower d

/-- **The exterior powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_extPowerRep : IsPolynomialRep (extPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).exteriorPower d

end FunctorialPowers

end TauCeti
