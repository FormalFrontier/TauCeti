/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Triangularity of positive Kostant root subgroups

Let `M` be a Kostant-stable integral lattice with a basis of Cartan weight vectors. If the basis
is ordered so that adding a positive multiple of a root moves strictly towards the beginning,
then every divided power of the corresponding root operator is strictly upper triangular away
from degree zero. Consequently its divided-power exponential is upper unitriangular over every
commutative base ring.

This realizes a positive Kostant root subgroup inside the upper-unitriangular group. It is the
matrix input needed to place the positive-root subgroup in the unipotent radical of a Borel
subgroup in the Chevalley--Demazure construction.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.repr_integralDividedPower_eq_zero_of_not_lt`: positive
  divided powers have no coordinate on or below their source basis vector.
* `TauCeti.UniversalEnvelopingAlgebra.isUpperUnitriangular_kostantRootSubgroupMatrix`: a positive
  root-subgroup point has an upper-unitriangular matrix over every commutative ring.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupUpperUnitriangular`: the root-subgroup
  homomorphism corestricted to the upper-unitriangular group.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§21, 26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable {i : ι} {α : κ → ℤ}
variable {η : Type*} [Fintype η] [LinearOrder η]
variable (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

/-! ## Integral divided-power coordinates -/

omit [Fintype η] in
include e hM in
/-- A positive divided power has no coordinate at a basis vector which does not precede its
source. The order hypothesis says precisely that a nonzero positive root shift of weights must
move from `s` to an index `r < s`.

This statement includes both the entries below the diagonal and the diagonal entries of every
positive-degree divided power. -/
theorem repr_integralDividedPower_eq_zero_of_not_lt
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    {r s : η} (hrs : ¬ r < s) {n : ℕ} (hn : 0 < n) :
    b.repr
        (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
          (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i n hv) (b s)) r = 0 := by
  apply repr_eq_zero_of_isCartanWeightVector e h ρ M hM b wt hwt
  · rw [coe_integralDividedPower_apply]
    exact IsCartanWeightVector.integralDividedPower e hα (hwt s) n
  · exact fun heq ↦ hrs (horder hn heq)

include e hM in
/-- Every positive divided power of a positive root operator is strictly upper triangular in an
ordered weight basis. -/
theorem isUpperTriangular_toMatrix_integralDividedPower
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    {n : ℕ} (hn : 0 < n) :
    (LinearMap.toMatrix b b
        (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
          (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i n hv))).IsUpperTriangular := by
  intro r s hsr
  rw [LinearMap.toMatrix_apply]
  exact repr_integralDividedPower_eq_zero_of_not_lt e h ρ M hM b wt hwt hα horder
    (not_lt_of_ge hsr.le) hn

/-! ## Positive root-subgroup matrices -/

variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

include e hM in
/-- A positive Kostant root-subgroup point is upper unitriangular in an ordered weight basis over
every commutative base ring. The positive-degree divided powers are strictly upper triangular,
while the degree-zero divided power supplies the identity diagonal. -/
theorem isUpperUnitriangular_kostantRootSubgroupMatrix {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((kostantRootSubgroupMatrix e h ρ M hM i hnil b f :
        Matrix.GeneralLinearGroup η A) : Matrix η η A).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro r s hsr
    rw [kostantRootSubgroupMatrix_apply, Module.Basis.baseChange_apply,
      kostantRootSubgroupPoints_tmul, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro n _
    by_cases hn : n = 0
    · subst n
      have hrs : s ≠ r := ne_of_lt hsr
      simp [integralDividedPower_zero, hrs]
    · rw [Module.Basis.baseChange_repr_tmul,
        repr_integralDividedPower_eq_zero_of_not_lt e h ρ M hM b wt hwt hα horder
          (r := r) (s := s) (not_lt_of_ge hsr.le) (Nat.pos_of_ne_zero hn)]
      simp
  · intro r
    have hclass :
        nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ≠ 0 := by
      intro hzero
      have hpow := pow_nilpotencyClass hnil
      rw [hzero, pow_zero] at hpow
      have hbzero : ((b r : M) : V) = 0 := by
        have happ := LinearMap.congr_fun hpow ((b r : M) : V)
        simpa using happ
      exact b.ne_zero r (Subtype.ext hbzero)
    rw [kostantRootSubgroupMatrix_apply, Module.Basis.baseChange_apply,
      kostantRootSubgroupPoints_tmul, map_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single 0]
    · simp [integralDividedPower_zero]
    · intro n _ hn
      rw [Module.Basis.baseChange_repr_tmul,
        repr_integralDividedPower_eq_zero_of_not_lt e h ρ M hM b wt hwt hα horder
          (lt_irrefl r) (Nat.pos_of_ne_zero hn)]
      simp
    · intro hzero
      exact False.elim (hclass (by simpa using hzero))

include e hM in
/-- The image of a positive Kostant root subgroup lies in the upper-unitriangular subgroup of
the ambient general linear group. -/
theorem range_kostantRootSubgroupMatrix_le_upperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s) :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil b (A := A)).range ≤
      upperUnitriangularGroup η A := by
  rintro g ⟨f, rfl⟩
  exact UpperUnitriangularGroup.mem_iff.mpr <|
    isUpperUnitriangular_kostantRootSubgroupMatrix
      e h ρ M hM b wt i hnil hwt hα horder f

include e hM in
/-- A positive Kostant root subgroup, with its codomain restricted to the upper-unitriangular
group. This is the root-radical form used in triangular Borel constructions. -/
noncomputable def kostantRootSubgroupUpperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s) :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      upperUnitriangularGroup η A :=
  (kostantRootSubgroupMatrix e h ρ M hM i hnil b).codRestrict
    (upperUnitriangularGroup η A) fun f ↦
      range_kostantRootSubgroupMatrix_le_upperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder ⟨f, rfl⟩

/-- Forgetting the upper-unitriangular codomain recovers the original root-subgroup matrix. -/
@[simp]
theorem coe_kostantRootSubgroupUpperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupUpperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder f : Matrix.GeneralLinearGroup η A) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b f :=
  by rw [kostantRootSubgroupUpperUnitriangular, MonoidHom.codRestrict_apply]

/-- The upper-unitriangular realization of a positive Kostant root subgroup is natural in the
commutative base ring. -/
@[simp]
theorem map_kostantRootSubgroupUpperUnitriangular {A B : Type*} [CommRing A] [CommRing B]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (φ : A →+* B) (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    UpperUnitriangularGroup.map φ
        (kostantRootSubgroupUpperUnitriangular
          e h ρ M hM b wt i hnil hwt hα horder f) =
      kostantRootSubgroupUpperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder
          (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f) := by
  apply Subtype.ext
  rw [UpperUnitriangularGroup.coe_map]
  exact map_kostantRootSubgroupMatrix e h ρ M hM i hnil b φ f

end TauCeti.UniversalEnvelopingAlgebra
