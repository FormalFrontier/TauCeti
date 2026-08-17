/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.JordanChevalley
public import TauCeti.RingTheory.Adjoin.Unit
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent

/-!
# Multiplicative Jordan–Chevalley decomposition

Over a perfect field, every linear automorphism of a finite-dimensional vector space factors
uniquely as the product of a semisimple automorphism and a unipotent automorphism that commute.
This is the multiplicative Jordan–Chevalley decomposition.

The construction converts Mathlib's additive decomposition `f = n + s` into
`f = s * (1 + s⁻¹n)`.  The semisimple summand `s` is invertible because it differs from the
invertible map `f` by a commuting nilpotent map.  Uniqueness is reduced in the opposite direction
to `Module.End.isNilpotent_isSemisimple_unique`.

This is the general-linear-group case of the Jordan decomposition requested in Layer 4 of the
ReductiveGroups roadmap.  It is the linear-algebra input for transporting Jordan decompositions
through faithful representations of affine algebraic groups.

## Main declarations

* `LinearMap.GeneralLinearGroup.IsSemisimple`: a linear automorphism is semisimple when its
  underlying endomorphism is semisimple.
* `LinearMap.GeneralLinearGroup.IsSemisimple.inv` and `.zpow`: semisimple automorphisms are closed
  under inverses and integer powers.
* `LinearMap.GeneralLinearGroup.IsSemisimple.mul_of_commute`: commuting semisimple automorphisms
  have semisimple product.
* `LinearMap.GeneralLinearGroup.jordanDecomposition`: the canonical commuting semisimple and
  unipotent factors.
* `LinearMap.GeneralLinearGroup.eq_jordanDecomposition_iff`: the existence and uniqueness
  characterization of those factors.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* `Mathlib.LinearAlgebra.JordanChevalley`, whose additive existence and uniqueness theorems are
  used here.
-/

public section

namespace LinearMap.GeneralLinearGroup

open Module

universe u v w x

section Definitions

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]

/-- A linear automorphism is semisimple if its underlying linear endomorphism is semisimple. -/
def IsSemisimple (g : GeneralLinearGroup K V) : Prop :=
  Module.End.IsSemisimple (g : End K V)

/-- Semisimplicity of a linear automorphism means semisimplicity of its underlying
endomorphism. -/
theorem isSemisimple_def (g : GeneralLinearGroup K V) :
    IsSemisimple g ↔ Module.End.IsSemisimple (g : End K V) :=
  Iff.rfl

/-- The identity automorphism is semisimple. -/
@[simp]
theorem isSemisimple_one [IsSemisimpleModule K V] :
    IsSemisimple (1 : GeneralLinearGroup K V) := by
  unfold IsSemisimple
  exact Module.End.isSemisimple_id

end Definitions

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The inverse of a semisimple linear automorphism is semisimple. -/
theorem IsSemisimple.inv {g : GeneralLinearGroup K V} (hg : IsSemisimple g) :
    IsSemisimple g⁻¹ := by
  rw [isSemisimple_def] at hg ⊢
  exact hg.of_mem_adjoin_singleton
    (TauCeti.Units.coe_inv_mem_adjoin g (IsIntegral.of_finite K (g : End K V)))

/-- A linear automorphism is semisimple if and only if its inverse is semisimple. -/
@[simp]
theorem isSemisimple_inv_iff (g : GeneralLinearGroup K V) :
    IsSemisimple g⁻¹ ↔ IsSemisimple g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsSemisimple.inv

/-- Every natural power of a semisimple linear automorphism is semisimple. -/
theorem IsSemisimple.pow {g : GeneralLinearGroup K V} (hg : IsSemisimple g) (n : ℕ) :
    IsSemisimple (g ^ n) := by
  rw [isSemisimple_def] at hg ⊢
  simpa only [Units.val_pow_eq_pow_val] using hg.pow n

/-- Every integer power of a semisimple linear automorphism is semisimple. -/
theorem IsSemisimple.zpow {g : GeneralLinearGroup K V} (hg : IsSemisimple g) (n : ℤ) :
    IsSemisimple (g ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hg.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hg.pow n.succ).inv

section PerfectField

variable [PerfectField K]

/-- The product of two commuting semisimple linear automorphisms is semisimple. -/
theorem IsSemisimple.mul_of_commute {g h : GeneralLinearGroup K V}
    (hg : IsSemisimple g) (hh : IsSemisimple h) (hcomm : Commute g h) :
    IsSemisimple (g * h) := by
  rw [isSemisimple_def] at hg hh ⊢
  rw [Units.val_mul]
  exact hg.mul_of_commute hcomm.units_val hh

end PerfectField

end Field

section PerfectField

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [PerfectField K] [FiniteDimensional K V]

private theorem exists_jordanDecomposition (g : GeneralLinearGroup K V) :
    ∃ p : GeneralLinearGroup K V × GeneralLinearGroup K V,
      IsSemisimple p.1 ∧ IsUnipotent p.2 ∧ Commute p.1 p.2 ∧ g = p.1 * p.2 := by
  let f : End K V := g
  obtain ⟨n, hn_mem, s, hs_mem, hn, hs, hf⟩ := f.exists_isNilpotent_isSemisimple
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn_mem
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs_mem
  have hns : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_mem hfn.symm
  have hs_unit : _root_.IsUnit s := by
    have hs_eq : s = f + -n := by rw [hf]; abel
    rw [hs_eq]
    exact hn.neg.isUnit_add_left_of_commute g.isUnit hfn.symm.neg_left
  let s' : GeneralLinearGroup K V := hs_unit.unit
  let u' : GeneralLinearGroup K V := s'⁻¹ * g
  have hs'_val : (s' : End K V) = s := hs_unit.unit_spec
  have hs'n : Commute ((s'⁻¹ : GeneralLinearGroup K V) : End K V) n := by
    apply Commute.units_inv_left
    simpa only [hs'_val] using hns.symm
  have hu'_sub : (u' : End K V) - 1 =
      ((s'⁻¹ : GeneralLinearGroup K V) : End K V) * n := by
    dsimp only [u']
    rw [Units.val_mul]
    -- Expose the named endomorphism `f` beneath the coercions from the two units.
    change ((s'⁻¹ : GeneralLinearGroup K V) : End K V) * f - 1 = _
    rw [hf, mul_add, ← hs'_val]
    simp
  have hs'g : Commute s' g := by
    apply Commute.units_of_val
    simpa only [hs'_val] using hfs.symm
  refine ⟨⟨s', u'⟩, ?_, ?_, ?_, ?_⟩
  · unfold IsSemisimple
    rw [hs'_val]
    exact hs
  · rw [isUnipotent_def]
    rw [hu'_sub]
    exact hs'n.isNilpotent_mul_left hn
  · exact (Commute.refl s').inv_right.mul_right hs'g
  · dsimp only [u']
    simp

/-- The nilpotent additive part associated to a semisimple--unipotent factorization. -/
private def additiveNilpotentPart
    (s u : GeneralLinearGroup K V) : End K V :=
  (s : End K V) * ((u : End K V) - 1)

omit [PerfectField K] [FiniteDimensional K V] in
private theorem additiveNilpotentPart_isNilpotent
    {s u : GeneralLinearGroup K V} (hu : IsUnipotent u) (hsu : Commute s u) :
    _root_.IsNilpotent (additiveNilpotentPart s u) := by
  rw [isUnipotent_def] at hu
  apply (hsu.units_val.sub_right (Commute.one_right _)).isNilpotent_mul_left
  exact hu

omit [PerfectField K] [FiniteDimensional K V] in
private theorem additiveNilpotentPart_add
    (s u : GeneralLinearGroup K V) :
    additiveNilpotentPart s u + (s : End K V) = (s * u : GeneralLinearGroup K V) := by
  dsimp only [additiveNilpotentPart]
  rw [Units.val_mul]
  rw [mul_sub, mul_one, sub_add_cancel]

omit [PerfectField K] [FiniteDimensional K V] in
private theorem additiveNilpotentPart_commute
    {s u : GeneralLinearGroup K V} (hsu : Commute s u) :
    Commute (additiveNilpotentPart s u) (s : End K V) := by
  apply (Commute.refl (s : End K V)).mul_left
  exact (hsu.units_val.sub_right (Commute.one_right _)).symm

/-- Two commuting semisimple–unipotent factorizations of the same linear automorphism have the
same factors. -/
theorem isSemisimple_isUnipotent_unique
    {s₁ u₁ s₂ u₂ : GeneralLinearGroup K V}
    (hs₁ : IsSemisimple s₁) (hu₁ : IsUnipotent u₁) (hc₁ : Commute s₁ u₁)
    (hs₂ : IsSemisimple s₂) (hu₂ : IsUnipotent u₂) (hc₂ : Commute s₂ u₂)
    (h : s₁ * u₁ = s₂ * u₂) :
    s₁ = s₂ ∧ u₁ = u₂ := by
  unfold IsSemisimple at hs₁ hs₂
  have hadd : additiveNilpotentPart s₁ u₁ + (s₁ : End K V) =
      additiveNilpotentPart s₂ u₂ + (s₂ : End K V) := by
    rw [additiveNilpotentPart_add, additiveNilpotentPart_add, h]
  have hs : (s₁ : End K V) = (s₂ : End K V) :=
    (Module.End.isNilpotent_isSemisimple_unique
      (additiveNilpotentPart_isNilpotent hu₁ hc₁) hs₁
      (additiveNilpotentPart_isNilpotent hu₂ hc₂) hs₂
      (additiveNilpotentPart_commute hc₁) (additiveNilpotentPart_commute hc₂) hadd).2
  have hs' : s₁ = s₂ := Units.ext hs
  subst s₂
  exact ⟨rfl, mul_left_cancel h⟩

/-- The canonical multiplicative Jordan–Chevalley decomposition of a linear automorphism.  The
first factor is semisimple, the second is unipotent, and the two factors commute. -/
noncomputable def jordanDecomposition (g : GeneralLinearGroup K V) :
    GeneralLinearGroup K V × GeneralLinearGroup K V :=
  Classical.choose (exists_jordanDecomposition g)

/-- The canonical Jordan decomposition has the defining semisimple, unipotent, commutation, and
product properties. -/
theorem jordanDecomposition_spec (g : GeneralLinearGroup K V) :
    IsSemisimple (jordanDecomposition g).1 ∧
      IsUnipotent (jordanDecomposition g).2 ∧
      Commute (jordanDecomposition g).1 (jordanDecomposition g).2 ∧
      g = (jordanDecomposition g).1 * (jordanDecomposition g).2 :=
  Classical.choose_spec (exists_jordanDecomposition g)

/-- A pair is the canonical Jordan decomposition exactly when it is a commuting
semisimple–unipotent factorization. -/
theorem eq_jordanDecomposition_iff (g s u : GeneralLinearGroup K V) :
    (s, u) = jordanDecomposition g ↔
      IsSemisimple s ∧ IsUnipotent u ∧ Commute s u ∧ g = s * u := by
  constructor
  · intro h
    have hs : s = (jordanDecomposition g).1 := congrArg Prod.fst h
    have hu : u = (jordanDecomposition g).2 := congrArg Prod.snd h
    subst s
    subst u
    exact jordanDecomposition_spec g
  · intro h
    have h_unique := isSemisimple_isUnipotent_unique h.1 h.2.1 h.2.2.1
      (jordanDecomposition_spec g).1 (jordanDecomposition_spec g).2.1
      (jordanDecomposition_spec g).2.2.1
      (h.2.2.2.symm.trans (jordanDecomposition_spec g).2.2.2)
    exact Prod.ext h_unique.1 h_unique.2

/-- The semisimple factor of the multiplicative Jordan–Chevalley decomposition. -/
noncomputable def semisimplePart (g : GeneralLinearGroup K V) : GeneralLinearGroup K V :=
  (jordanDecomposition g).1

/-- The semisimple part is the first factor of the canonical Jordan decomposition. -/
theorem semisimplePart_def (g : GeneralLinearGroup K V) :
    semisimplePart g = (jordanDecomposition g).1 :=
  (rfl)

/-- The unipotent factor of the multiplicative Jordan–Chevalley decomposition. -/
noncomputable def unipotentPart (g : GeneralLinearGroup K V) : GeneralLinearGroup K V :=
  (jordanDecomposition g).2

/-- The unipotent part is the second factor of the canonical Jordan decomposition. -/
theorem unipotentPart_def (g : GeneralLinearGroup K V) :
    unipotentPart g = (jordanDecomposition g).2 :=
  (rfl)

/-- The semisimple factor is semisimple. -/
theorem isSemisimple_semisimplePart (g : GeneralLinearGroup K V) :
    IsSemisimple (semisimplePart g) :=
  (jordanDecomposition_spec g).1

/-- The unipotent factor is unipotent. -/
theorem isUnipotent_unipotentPart (g : GeneralLinearGroup K V) :
    IsUnipotent (unipotentPart g) :=
  (jordanDecomposition_spec g).2.1

/-- The semisimple and unipotent factors commute. -/
theorem commute_semisimplePart_unipotentPart (g : GeneralLinearGroup K V) :
    Commute (semisimplePart g) (unipotentPart g) :=
  (jordanDecomposition_spec g).2.2.1

/-- Multiplying the semisimple and unipotent factors recovers the original automorphism. -/
@[simp]
theorem semisimplePart_mul_unipotentPart (g : GeneralLinearGroup K V) :
    semisimplePart g * unipotentPart g = g :=
  (jordanDecomposition_spec g).2.2.2.symm

/-- A binary operation preserving multiplication, semisimplicity, and unipotence preserves the
multiplicative Jordan decomposition. -/
theorem jordanDecomposition_map₂
    {W : Type w} {U : Type x}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (F : GeneralLinearGroup K V → GeneralLinearGroup K W → GeneralLinearGroup K U)
    (map_mul : ∀ a c b d, F (a * c) (b * d) = F a b * F c d)
    (map_isSemisimple : ∀ {a b}, IsSemisimple a → IsSemisimple b → IsSemisimple (F a b))
    (map_isUnipotent : ∀ {a b}, IsUnipotent a → IsUnipotent b → IsUnipotent (F a b))
    (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    jordanDecomposition (F g h) =
      (F (semisimplePart g) (semisimplePart h),
        F (unipotentPart g) (unipotentPart h)) := by
  symm
  apply (eq_jordanDecomposition_iff (F g h) _ _).2
  refine ⟨map_isSemisimple (isSemisimple_semisimplePart g)
      (isSemisimple_semisimplePart h),
    map_isUnipotent (isUnipotent_unipotentPart g) (isUnipotent_unipotentPart h), ?_, ?_⟩
  · rw [commute_iff_eq, ← map_mul, ← map_mul]
    exact congrArg₂ F (commute_semisimplePart_unipotentPart g).eq
      (commute_semisimplePart_unipotentPart h).eq
  · rw [← map_mul, semisimplePart_mul_unipotentPart,
      semisimplePart_mul_unipotentPart]

/-- The semisimple factor of an automorphism is a polynomial in that automorphism. -/
theorem coe_semisimplePart_mem_adjoin (g : GeneralLinearGroup K V) :
    (semisimplePart g : Module.End K V) ∈
      Algebra.adjoin K {(g : Module.End K V)} := by
  obtain ⟨n, hn_mem, s, hs_mem, hn, hs, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := (g : Module.End K V))
  let s₀ : Module.End K V := semisimplePart g
  let u₀ : Module.End K V := unipotentPart g
  let n₀ : Module.End K V := s₀ * (u₀ - 1)
  have hsu : Commute s₀ (u₀ - 1) :=
    (commute_semisimplePart_unipotentPart g).units_val.sub_right (Commute.one_right _)
  have hn₀ : IsNilpotent n₀ :=
    hsu.isNilpotent_mul_left ((isUnipotent_def _).mp (isUnipotent_unipotentPart g))
  have hs₀ : Module.End.IsSemisimple s₀ :=
    (isSemisimple_def _).mp (isSemisimple_semisimplePart g)
  have hcomm₀ : Commute n₀ s₀ := (Commute.refl s₀).mul_left hsu.symm
  have hsum₀ : n₀ + s₀ = (g : Module.End K V) := by
    dsimp only [n₀]
    rw [mul_sub, mul_one, sub_add_cancel]
    exact congrArg ((↑·) : GeneralLinearGroup K V → Module.End K V)
      (semisimplePart_mul_unipotentPart g)
  have hcomm : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_mem
      (Algebra.commute_of_mem_adjoin_self hn_mem).symm
  have heq := Module.End.isNilpotent_isSemisimple_unique hn₀ hs₀ hn hs hcomm₀ hcomm
    (hsum₀.trans hsum)
  -- Restate the opaque factor through the local name used by the uniqueness calculation.
  change s₀ ∈ Algebra.adjoin K {(g : Module.End K V)}
  rw [heq.2]
  exact hs_mem

/-- A semisimple automorphism is its own semisimple part. -/
@[simp]
theorem semisimplePart_eq_self {g : GeneralLinearGroup K V} (hg : IsSemisimple g) :
    semisimplePart g = g :=
  (isSemisimple_isUnipotent_unique
    (isSemisimple_semisimplePart g) (isUnipotent_unipotentPart g)
    (commute_semisimplePart_unipotentPart g) hg isUnipotent_one (Commute.one_right g)
    (by simp)).1

/-- A semisimple automorphism has trivial unipotent part. -/
@[simp]
theorem unipotentPart_eq_one_of_isSemisimple
    {g : GeneralLinearGroup K V} (hg : IsSemisimple g) :
    unipotentPart g = 1 :=
  (isSemisimple_isUnipotent_unique
    (isSemisimple_semisimplePart g) (isUnipotent_unipotentPart g)
    (commute_semisimplePart_unipotentPart g) hg isUnipotent_one (Commute.one_right g)
    (by simp)).2

/-- A unipotent automorphism has trivial semisimple part. -/
@[simp]
theorem semisimplePart_eq_one_of_isUnipotent
    {g : GeneralLinearGroup K V} (hg : IsUnipotent g) :
    semisimplePart g = 1 :=
  (isSemisimple_isUnipotent_unique
    (isSemisimple_semisimplePart g) (isUnipotent_unipotentPart g)
    (commute_semisimplePart_unipotentPart g) isSemisimple_one hg (Commute.one_left g)
    (by simp)).1

/-- A unipotent automorphism is its own unipotent part. -/
@[simp]
theorem unipotentPart_eq_self {g : GeneralLinearGroup K V} (hg : IsUnipotent g) :
    unipotentPart g = g :=
  (isSemisimple_isUnipotent_unique
    (isSemisimple_semisimplePart g) (isUnipotent_unipotentPart g)
    (commute_semisimplePart_unipotentPart g) isSemisimple_one hg (Commute.one_left g)
    (by simp)).2

end PerfectField

end LinearMap.GeneralLinearGroup
