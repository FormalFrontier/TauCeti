/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
public import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of the standard general-linear module

The infinitesimal exterior-power action restricts along the matrix-to-endomorphism equivalence to
an action of a general linear Lie algebra. A matrix unit acts on the wedge of the standard basis
vectors indexed by a finite set `S` of coordinates in a way read off from `S`: the diagonal unit
`Eᵢᵢ` scales it by one or by zero according as `i` lies in `S`, and `Eᵢⱼ` with `i ≠ j` annihilates
it whenever `S` contains `i` as soon as it contains `j`. Over a nontrivial ring, for `d ≤ n`, this
makes the wedge of the first `d` standard basis vectors in `Kⁿ` a highest-weight vector.

## Main definitions

* `exteriorPower.glLieMap`: the action of matrices on an exterior power.
* `exteriorPower.basisWedge`: the wedge of the standard basis vectors indexed by a finite set of
  coordinates.
* `exteriorPower.firstBasisWedge`: the wedge of the first standard basis vectors.
* `exteriorPower.fundamentalWeight`: the first-`d` coordinate-indicator weight.

## Main results

* `exteriorPower.lie_single_self_basisWedge` and
  `exteriorPower.lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem`: how a matrix unit acts on the
  wedge of a set of standard basis vectors.
* `exteriorPower.isGlHighestWeightVector_firstBasisWedge`: over a nontrivial ring, the first basis
  wedge is a highest-weight vector when `d ≤ n`.

## Roadmap context

The [highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
uses these exterior modules in two places: Layer 9 constructs the fundamental `gl_n` modules,
while Layer 8 uses the `sl₉` action on `⋀³(K⁹)` in the Vinberg model of `E₈`.

## References

The exterior-power construction and its cyclicity and irreducibility argument follow the standard
general-linear treatment in Goodman--Wallach, especially §§5.5 and 9.1, and Fulton--Harris §15.5.
-/

public section

open scoped Matrix

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

section Action

variable {K : Type*} [CommRing K]

/-- The natural matrix action on an exterior power of the standard module. -/
noncomputable def glLieMap (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    Matrix n n K →ₗ⁅K⁆ Module.End K (⋀[K]^d (n → K)) :=
  (lieMap d).comp (lieEquivMatrix' (R := K) (n := n)).symm

/-- A matrix acts on a decomposable wedge by acting on one factor at a time. -/
@[simp]
theorem glLieMap_apply_ιMulti (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (v : Fin d → (n → K)) :
    glLieMap d A (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (A *ᵥ v i)) := by
  rw [glLieMap, LieHom.comp_apply]
  have hmatrix :
      (lieEquivMatrix' (R := K) (n := n)).symm.toLieHom A = Matrix.toLin' A :=
    lieEquivMatrix'_symm_apply A
  rw [hmatrix, lieMap_apply_ιMulti]
  simp only [Matrix.toLin'_apply]

/-- The Lie-ring module structure on an exterior power induced by the standard matrix action. -/
noncomputable scoped instance glLieRingModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieRingModule.compLieHom _ (glLieMap d)

/-- The Lie-module structure on an exterior power induced by the standard matrix action. -/
noncomputable scoped instance glLieModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieModule K (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieModule.compLieHom _ (glLieMap d)

/-- The scoped Lie action is the action represented by `glLieMap`. -/
theorem gl_lie_def (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (x : ⋀[K]^d (n → K)) :
    letI : LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
      glLieRingModule (K := K) (n := n) d
    ⁅A, x⁆ = glLieMap d A x := by
  rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]

private theorem single_mulVec_basis (n : ℕ) (i j k : Fin n) :
    Matrix.single i j 1 *ᵥ (Pi.single k 1 : Fin n → K) =
      if j = k then Pi.single i 1 else 0 := by
  rw [Matrix.single_mulVec_eq]
  by_cases hjk : j = k
  · subst j
    simp
  · simp [hjk]

section BasisWedge

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n] {N : ℕ}

variable (K) in
/-- The wedge of the standard basis vectors of `n → K` indexed by a finite set `S` of coordinates,
an element of the exterior power of degree the size of `S`. The factors are wedged together in the
order `S` inherits from `n`. -/
noncomputable def basisWedge (S : Finset n) (h : S.card = N) : ⋀[K]^N (n → K) :=
  ιMulti_family K N (Pi.basisFun K n) ⟨S, h⟩

omit [DecidableEq n] in
/-- The wedge of a set of basis vectors is the member of the standard basis of the exterior power
that the set indexes. -/
theorem basisWedge_eq_ιMulti_family (S : Finset n) (h : S.card = N) :
    basisWedge K S h = ιMulti_family K N (Pi.basisFun K n) ⟨S, h⟩ := by
  rw [basisWedge]

/-- The wedge of a set of basis vectors, written as an exterior product. -/
theorem basisWedge_eq_ιMulti (S : Finset n) (h : S.card = N) :
    basisWedge K S h = ιMulti K N fun k => Pi.single (S.orderEmbOfFin h k) 1 := by
  rw [basisWedge_eq_ιMulti_family, ιMulti_family]
  refine congrArg (ιMulti K N) (funext fun k => ?_)
  simp [Pi.basisFun_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]

omit [DecidableEq n] in
/-- The wedge of a set of basis vectors is nonzero. -/
theorem basisWedge_ne_zero [Nontrivial K] (S : Finset n) (h : S.card = N) :
    basisWedge K S h ≠ 0 := by
  rw [basisWedge_eq_ιMulti_family]
  exact (ιMulti_family_linearIndependent_ofBasis K N (Pi.basisFun K n)).ne_zero _

/-- The diagonal matrix unit `Eᵢᵢ` fixes the factors of a wedge of standard basis vectors that lie
in direction `i` and kills the others, so it scales the wedge by one when `i` is one of its indices
and annihilates it otherwise. -/
@[simp]
theorem lie_single_self_basisWedge (S : Finset n) (h : S.card = N) (i : n) :
    ⁅Matrix.single i i (1 : K), basisWedge K S h⁆ =
      (if i ∈ S then (1 : K) else 0) • basisWedge K S h := by
  rw [basisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp only [Matrix.single_mulVec_eq, Pi.single_apply, one_mul, ite_smul, one_smul, zero_smul,
    eq_comm]
  by_cases hiS : i ∈ S
  · obtain ⟨k₀, hk₀⟩ := (S.range_orderEmbOfFin h).ge (Finset.mem_coe.2 hiS)
    rw [ite_eq_left hiS, Finset.sum_eq_single k₀]
    · rw [ite_eq_left hk₀.symm, ← hk₀]
      exact (congrArg (ιMulti K N) (Function.update_eq_self k₀ _)).symm
    · intro k _ hk
      have hik : ¬i = S.orderEmbOfFin h k := fun hik =>
        hk ((S.orderEmbOfFin h).injective (hk₀.trans hik)).symm
      rw [ite_eq_right hik]
      exact (ιMulti K N).map_update_zero _ _
    · exact fun hk => absurd (Finset.mem_univ k₀) hk
  · rw [ite_eq_right hiS]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have hik : ¬i = S.orderEmbOfFin h k := by
      intro hik
      exact hiS (by rw [hik]; exact Finset.orderEmbOfFin_mem S h k)
    rw [ite_eq_right hik]
    exact (ιMulti K N).map_update_zero _ _

/-- A matrix unit `Eᵢⱼ` with `i ≠ j` annihilates the wedge of the standard basis vectors indexed by
`S`, as soon as `S` contains `i` whenever it contains `j`: the `j`-th factor is carried to a factor
already present, so every summand of the Leibniz expansion has a repeated factor. -/
theorem lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem (S : Finset n) (h : S.card = N)
    {i j : n} (hij : i ≠ j) (hS : j ∈ S → i ∈ S) :
    ⁅Matrix.single i j (1 : K), basisWedge K S h⁆ = 0 := by
  rw [basisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp only [Matrix.single_mulVec_eq, Pi.single_apply, one_mul, ite_smul, one_smul, zero_smul,
    eq_comm]
  refine (Finset.sum_eq_zero fun k _ => ?_).symm
  by_cases hjk : j = S.orderEmbOfFin h k
  · have hjS : j ∈ S := by rw [hjk]; exact Finset.orderEmbOfFin_mem S h k
    obtain ⟨l, hl⟩ := (S.range_orderEmbOfFin h).ge (Finset.mem_coe.2 (hS hjS))
    have hlk : l ≠ k := by
      rintro rfl
      exact hij (hl.symm.trans hjk.symm)
    rw [ite_eq_left hjk]
    refine (ιMulti K N).map_eq_zero_of_eq _ (i := l) (j := k) ?_ hlk
    rw [Function.update_of_ne hlk, Function.update_self, hl]
  · rw [ite_eq_right hjk]
    exact (ιMulti K N).map_update_zero _ _

end BasisWedge

/-- The subset of the first `d` coordinates in `Fin n`. -/
private noncomputable def firstBasisSet (d n : ℕ) (h : d ≤ n) : Set.powersetCard (Fin n) d :=
  Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb h)

private theorem mem_firstBasisSet (d n : ℕ) (h : d ≤ n) (k : Fin n) :
    k ∈ (firstBasisSet d n h : Finset (Fin n)) ↔ (k : ℕ) < d := by
  rw [Set.powersetCard.mem_coe_iff, firstBasisSet,
    Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  simp [Fin.castLEOrderEmb, Fin.range_castLE]

/-- The wedge of the first `d` standard basis vectors of `K^n`. -/
noncomputable def firstBasisWedge (d n : ℕ) (h : d ≤ n) : ⋀[K]^d (Fin n → K) :=
  ιMulti_family K d (Pi.basisFun K (Fin n)) (firstBasisSet d n h)

/-- The first basis wedge written as an exterior product of standard basis vectors. -/
@[simp]
theorem firstBasisWedge_eq_ιMulti (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h =
      ιMulti K d (fun i => Pi.single (Fin.castLE h i) 1) := by
  simp only [firstBasisWedge, ιMulti_family, firstBasisSet, Equiv.symm_apply_apply]
  apply congrArg (ιMulti K d)
  funext i x
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The first basis wedge is the wedge of the basis vectors indexed by the first `d` coordinates. -/
private theorem firstBasisWedge_eq_basisWedge (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h =
      basisWedge K (firstBasisSet d n h : Finset (Fin n))
        (Set.powersetCard.card_eq (firstBasisSet d n h)) :=
  rfl

end Action

section Weight

variable {K : Type*} [Zero K] [One K]

/-- The tuple that is `1` on the first `d` coordinates and `0` afterward. When `d ≤ n`, this is
the weight of the first basis wedge in the `d`-th exterior power of the standard `gl_n` module. -/
def fundamentalWeight (d n : ℕ) : Fin n → K :=
  fun j => if j.val < d then 1 else 0

/-- The fundamental exterior weight is `1` on the first `d` coordinates and `0` afterward. -/
@[simp]
theorem fundamentalWeight_apply (d n : ℕ) (j : Fin n) :
    fundamentalWeight (K := K) d n j = if j.val < d then 1 else 0 := by
  rw [fundamentalWeight]

end Weight

section HighestWeight

variable {K : Type*} [CommRing K]

/-- The fundamental exterior weight is dominant integral in characteristic zero. -/
theorem isGlDominantIntegral_fundamentalWeight [CharZero K] (d n : ℕ) :
    TauCeti.IsGlDominantIntegral (fundamentalWeight (K := K) d n) := by
  rw [TauCeti.isGlDominantIntegral_iff]
  intro i j hij
  by_cases hi : i.val < d
  · by_cases hj : j.val < d
    · exact ⟨0, by simp [hi, hj]⟩
    · exact ⟨1, by simp [hi, hj]⟩
  · have hj : ¬j.val < d := by omega
    exact ⟨0, by simp [hi, hj]⟩

/-- The first basis wedge is nonzero. -/
theorem firstBasisWedge_ne_zero [Nontrivial K] (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h ≠ 0 := by
  rw [firstBasisWedge_eq_basisWedge]
  exact basisWedge_ne_zero _ _

/-- Over a nontrivial ring, the first basis wedge is a highest-weight vector for the exterior-power
action when `d ≤ n`. -/
theorem isGlHighestWeightVector_firstBasisWedge [Nontrivial K] (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    TauCeti.IsGlHighestWeightVector (fundamentalWeight (K := K) d n)
      (firstBasisWedge (K := K) d n h) := by
  rw [firstBasisWedge_eq_basisWedge]
  refine TauCeti.isGlHighestWeightVector_iff.mpr
    ⟨basisWedge_ne_zero _ _, fun i => ?_, fun i j hij => ?_⟩
  · rw [lie_single_self_basisWedge, fundamentalWeight_apply]
    simp only [mem_firstBasisSet]
  · exact lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem _ _ hij.ne fun hj =>
      (mem_firstBasisSet d n h i).2
        ((Fin.lt_def.1 hij).trans ((mem_firstBasisSet d n h j).1 hj))

end HighestWeight

section Cyclicity

variable {K : Type*} [CommRing K]

private theorem lie_single_self_basisWedge_family (d n : ℕ)
    (s : Set.powersetCard (Fin n) d) (i : Fin n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single i i (1 : K),
      ιMulti_family K d (Pi.basisFun K (Fin n)) s⁆ =
        if i ∈ s.1 then ιMulti_family K d (Pi.basisFun K (Fin n)) s else 0 := by
  simpa [basisWedge] using
    (lie_single_self_basisWedge (K := K) s.1 s.2 i)

private noncomputable def basisPath (d n : ℕ) (h : d ≤ n)
    (s : Set.powersetCard (Fin n) d) (k : ℕ) (l : Fin d) : Fin n :=
  if l.val < k then Fin.castLE h l else Set.powersetCard.ofFinEmbEquiv.symm s l

private theorem basisPath_top (d n : ℕ) (h : d ≤ n)
    (s : Set.powersetCard (Fin n) d) :
    basisPath d n h s d = Fin.castLE h := by
  funext l
  simp [basisPath, l.isLt]

private theorem basisPath_zero (d n : ℕ) (h : d ≤ n)
    (s : Set.powersetCard (Fin n) d) :
    basisPath d n h s 0 = Set.powersetCard.ofFinEmbEquiv.symm s := by
  funext l
  simp [basisPath]

private theorem fin_val_le_of_strictMono {d n : ℕ} (f : Fin d → Fin n)
    (hf : StrictMono f) (i : Fin d) : i.val ≤ (f i).val := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hmono := hf (Fin.castSucc_lt_succ (i := i))
      simp only [Fin.val_succ] at hmono ⊢
      have hmono' : (f i.castSucc).val < (f i.succ).val := hmono
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hmono')

private theorem basisPath_strictMono (d n : ℕ) (h : d ≤ n)
    (s : Set.powersetCard (Fin n) d) (k : ℕ) :
    StrictMono (basisPath d n h s k) := by
  intro a b hab
  by_cases ha : a.val < k
  · by_cases hb : b.val < k
    · simp only [basisPath, ha, hb, ite_true]
      exact hab
    · simp only [basisPath, ha, hb, ite_true, ite_false]
      have hs := fin_val_le_of_strictMono _
        (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono b
      exact Fin.mk_lt_mk.mpr
        (lt_of_lt_of_le ha (le_trans (Nat.le_of_not_gt hb) hs))
  · have hb : ¬b.val < k := fun hb ↦ ha (lt_trans hab hb)
    simp only [basisPath, ha, hb, ite_false]
    exact (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hab

private theorem lie_single_basisFamily (d n : ℕ) (v : Fin d → Fin n)
    (hv : Function.Injective v) (a : Fin d) (i : Fin n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single i (v a) (1 : K),
      ιMulti K d (fun l ↦ (Pi.single (v l) (1 : K) : Fin n → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (Function.update v a i l) (1 : K) : Fin n → K)) := by
  classical
  rw [gl_lie_def, glLieMap_apply_ιMulti]
  simp only [single_mulVec_basis]
  rw [Finset.sum_eq_single a]
  · congr 1
    funext l
    by_cases hla : l = a
    · subst l
      simp
    · have hcol : v a ≠ v l := fun h ↦ hla (hv h.symm)
      simp [Function.update, hla]
  · intro l _ hla
    have hcol : v a ≠ v l := fun h ↦ hla (hv h.symm)
    simp only [hcol, ite_false]
    exact (ιMulti K d).map_update_zero _ _
  · simp

private theorem lie_single_basisPath_transition (d n : ℕ) (v w : Fin d → Fin n)
    (hv : StrictMono v) (a : Fin d) (i : Fin n)
    (hupdate : Function.update v a i = w) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single i (v a) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (v l) (1 : K) : Fin n → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (w l) (1 : K) : Fin n → K)) := by
  rw [lie_single_basisFamily (K := K) d n v hv.injective a]
  exact congrArg (ιMulti K d) (congrArg (fun f ↦
    fun l ↦ (Pi.single (f l) (1 : K) : Fin n → K)) hupdate)

private theorem basisPath_succ_eq_of_ne (d n k : ℕ) (h : d ≤ n) (hk : k < d)
    (s : Set.powersetCard (Fin n) d) (a l : Fin d) (hla : l ≠ a)
    (ha : a = ⟨k, hk⟩) :
    basisPath d n h s (k + 1) l = basisPath d n h s k l := by
  have hlk : l.val ≠ k := by
    intro hlk
    apply hla
    exact Fin.ext (hlk.trans (congrArg Fin.val ha.symm))
  by_cases hlt : l.val < k
  · simp [basisPath, hlt, Nat.lt_succ_of_lt hlt]
  · have hsucc : ¬l.val < k + 1 := by omega
    simp [basisPath, hlt, hsucc]

private theorem lie_basisPath_succ (d n k : ℕ) (h : d ≤ n) (hk : k < d)
    (s : Set.powersetCard (Fin n) d) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single
        (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩)
        (Fin.castLE h ⟨k, hk⟩) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d n h s (k + 1) l) (1 : K) : Fin n → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (basisPath d n h s k l) (1 : K) : Fin n → K)) := by
  let a : Fin d := ⟨k, hk⟩
  have hsource : Fin.castLE h ⟨k, hk⟩ = basisPath d n h s (k + 1) a := by
    simp [a, basisPath]
  rw [hsource]
  apply lie_single_basisPath_transition (K := K) d n
    (basisPath d n h s (k + 1)) (basisPath d n h s k)
    (basisPath_strictMono d n h s (k + 1)) a
    (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩)
  funext l
  by_cases hla : l = a
  · subst l
    simp [Function.update, basisPath, a]
  · have hlk : l.val ≠ k := fun hlk ↦ hla (Fin.ext hlk)
    rw [Function.update_of_ne hla, basisPath_succ_eq_of_ne d n k h hk s a l hla rfl]

private theorem basisWedge_mem_of_first_mem (d n : ℕ) (h : d ≤ n)
    (N : LieSubmodule K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)))
    (hfirst : firstBasisWedge (K := K) d n h ∈ N)
    (s : Set.powersetCard (Fin n) d) :
    ιMulti_family K d (Pi.basisFun K (Fin n)) s ∈ N := by
  classical
  let _ : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
    glLieRingModule (K := K) (n := Fin n) d
  have hd : ιMulti K d (fun l ↦
      (Pi.single (basisPath d n h s d l) (1 : K) : Fin n → K)) ∈ N := by
    rw [basisPath_top, ← firstBasisWedge_eq_ιMulti]
    exact hfirst
  have hzero : ιMulti K d (fun l ↦
      (Pi.single (basisPath d n h s 0 l) (1 : K) : Fin n → K)) ∈ N :=
    Nat.decreasingInduction' (m := 0) (n := d) (P := fun k ↦
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d n h s k l) (1 : K) : Fin n → K)) ∈ N)
      (fun k hk _ ih ↦ by
        rw [← lie_basisPath_succ (K := K) d n k h hk s]
        exact N.lie_mem ih)
      (Nat.zero_le d) hd
  rw [basisPath_zero] at hzero
  rw [ιMulti_family]
  convert hzero using 1
  apply congrArg (ιMulti K d)
  funext l x
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The first basis wedge generates the exterior power as a general-linear Lie module. -/
theorem lieSpan_firstBasisWedge_eq_top (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    LieSubmodule.lieSpan K (Matrix (Fin n) (Fin n) K)
      {firstBasisWedge (K := K) d n h} = ⊤ := by
  classical
  let N := LieSubmodule.lieSpan K (Matrix (Fin n) (Fin n) K)
    {firstBasisWedge (K := K) d n h}
  apply (LieSubmodule.toSubmodule_eq_top N).mp
  rw [eq_top_iff, ← ((Pi.basisFun K (Fin n)).exteriorPower d).span_eq,
    Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [exteriorPower.basis_apply]
  exact basisWedge_mem_of_first_mem (K := K) d n h N
    (LieSubmodule.subset_lieSpan (Set.mem_singleton _)) s

private theorem lie_basisPath_reverse (d n k : ℕ) (h : d ≤ n) (hk : k < d)
    (s : Set.powersetCard (Fin n) d) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single
        (Fin.castLE h ⟨k, hk⟩)
        (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d n h s k l) (1 : K) : Fin n → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (basisPath d n h s (k + 1) l) (1 : K) : Fin n → K)) := by
  let a : Fin d := ⟨k, hk⟩
  have hsource : Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩ =
      basisPath d n h s k a := by
    simp [a, basisPath]
  rw [hsource]
  apply lie_single_basisPath_transition (K := K) d n
    (basisPath d n h s k) (basisPath d n h s (k + 1))
    (basisPath_strictMono d n h s k) a
    (Fin.castLE h ⟨k, hk⟩)
  funext l
  by_cases hla : l = a
  · subst l
    simp [Function.update, basisPath, a]
  · have hlk : l.val ≠ k := fun hlk ↦ hla (Fin.ext hlk)
    rw [Function.update_of_ne hla, (basisPath_succ_eq_of_ne d n k h hk s a l hla rfl).symm]

private theorem first_mem_of_basisWedge_mem (d n : ℕ) (h : d ≤ n)
    (N : LieSubmodule K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)))
    (s : Set.powersetCard (Fin n) d)
    (hs : ιMulti_family K d (Pi.basisFun K (Fin n)) s ∈ N) :
    firstBasisWedge (K := K) d n h ∈ N := by
  classical
  let _ : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
    glLieRingModule (K := K) (n := Fin n) d
  have hzero : ιMulti K d (fun l ↦
      (Pi.single (basisPath d n h s 0 l) (1 : K) : Fin n → K)) ∈ N := by
    rw [basisPath_zero]
    rw [ιMulti_family] at hs
    convert hs using 1
    apply congrArg (ιMulti K d)
    funext l x
    simp [Pi.basisFun_apply, Pi.single_apply]
  have hmem : ∀ k, k ≤ d →
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d n h s k l) (1 : K) : Fin n → K)) ∈ N := by
    intro k hk
    induction k with
    | zero => exact hzero
    | succ k ih =>
      rw [← lie_basisPath_reverse (K := K) d n k h (by omega) s]
      exact N.lie_mem (ih (by omega))
  have htop := hmem d le_rfl
  rw [basisPath_top, ← firstBasisWedge_eq_ιMulti] at htop
  exact htop

end Cyclicity

section Irreducibility

variable {K : Type*} [Field K]

private noncomputable def diagonalFactor (d n : ℕ)
    (s : Set.powersetCard (Fin n) d) (i : Fin n) :
    Module.End K (⋀[K]^d (Fin n → K)) :=
  if i ∈ s.1 then glLieMap d (Matrix.single i i 1) else
    1 - glLieMap d (Matrix.single i i 1)

private theorem diagonalFactor_apply (d n : ℕ)
    (s t : Set.powersetCard (Fin n) d) (i : Fin n) :
    diagonalFactor (K := K) d n s i
        (ιMulti_family K d (Pi.basisFun K (Fin n)) t) =
      if (i ∈ s.1) = (i ∈ t.1) then
        ιMulti_family K d (Pi.basisFun K (Fin n)) t else 0 := by
  classical
  rw [diagonalFactor]
  by_cases his : i ∈ s.1 <;> by_cases hit : i ∈ t.1
  all_goals simp [his, hit, ← gl_lie_def, lie_single_self_basisWedge_family]

private noncomputable def diagonalProjector (d n : ℕ)
    (s : Set.powersetCard (Fin n) d) : Module.End K (⋀[K]^d (Fin n → K)) :=
  ((List.ofFn id).map fun i : Fin n ↦ diagonalFactor (K := K) d n s i).prod

private theorem diagonalProjector_apply (d n : ℕ)
    (s t : Set.powersetCard (Fin n) d) :
    diagonalProjector (K := K) d n s
        (ιMulti_family K d (Pi.basisFun K (Fin n)) t) =
      if s = t then ιMulti_family K d (Pi.basisFun K (Fin n)) t else 0 := by
  classical
  have hprod : ∀ u : List (Fin n),
      (u.map fun i ↦ diagonalFactor (K := K) d n s i).prod
          (ιMulti_family K d (Pi.basisFun K (Fin n)) t) =
        (u.map fun i ↦ if (i ∈ s.1) = (i ∈ t.1) then (1 : K) else 0).prod •
          ιMulti_family K d (Pi.basisFun K (Fin n)) t := by
    intro u
    induction u with
    | nil => simp
    | cons i u ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
        diagonalFactor_apply, List.map_cons, List.prod_cons]
      split <;> simp_all
  rw [diagonalProjector, hprod]
  by_cases hst : s = t
  · subst t
    simp
  · obtain ⟨i, his, hit⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    have hi : (i ∈ s.1) ≠ (i ∈ t.1) := fun h ↦ hit (h.mp his)
    have hzero : ((List.ofFn id).map fun j : Fin n ↦
        if (j ∈ s.1) = (j ∈ t.1) then (1 : K) else 0).prod = 0 := by
      apply List.prod_eq_zero
      rw [List.mem_map]
      refine ⟨i, ?_, by simp [hi]⟩
      rw [List.mem_ofFn']
      exact ⟨i, rfl⟩
    simp only [hst, ite_false]
    rw [hzero, zero_smul]

private theorem diagonalProjector_mem (d n : ℕ)
    (N : LieSubmodule K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)))
    (s : Set.powersetCard (Fin n) d) {x : ⋀[K]^d (Fin n → K)} (hx : x ∈ N) :
    diagonalProjector (K := K) d n s x ∈ N := by
  classical
  let _ : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
    glLieRingModule (K := K) (n := Fin n) d
  rw [diagonalProjector]
  have hmem : ∀ u : List (Fin n),
      (u.map fun i ↦ diagonalFactor (K := K) d n s i).prod x ∈ N := by
    intro u
    induction u with
    | nil => simpa using hx
    | cons i u ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, diagonalFactor]
      by_cases his : i ∈ s.1
      · simp only [his, ite_true]
        rw [← gl_lie_def]
        exact N.lie_mem ih
      · simp only [his, ite_false]
        rw [LinearMap.sub_apply, Module.End.one_apply, ← gl_lie_def]
        exact N.sub_mem ih (N.lie_mem ih)
  exact hmem (List.ofFn id)

private theorem exists_basisWedge_mem_of_nonzero_mem (d n : ℕ)
    (N : LieSubmodule K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)))
    {x : ⋀[K]^d (Fin n → K)} (hx : x ∈ N) (hx0 : x ≠ 0) :
    ∃ s : Set.powersetCard (Fin n) d,
      ιMulti_family K d (Pi.basisFun K (Fin n)) s ∈ N := by
  classical
  let B := (Pi.basisFun K (Fin n)).exteriorPower d
  have hre : B.repr x ≠ 0 := fun h ↦ hx0 (B.repr.injective (h.trans (map_zero B.repr).symm))
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hre
  have hproj : diagonalProjector (K := K) d n s x =
      (B.repr x s) • ιMulti_family K d (Pi.basisFun K (Fin n)) s := by
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, Finset.sum_eq_single s]
    · rw [map_smul, exteriorPower.basis_apply, diagonalProjector_apply]
      simp
    · intro t _ hts
      rw [map_smul, exteriorPower.basis_apply, diagonalProjector_apply]
      simp only [Ne.symm hts, ite_false, smul_zero]
    · simp
  have hmem := diagonalProjector_mem (K := K) d n N s hx
  rw [hproj] at hmem
  refine ⟨s, ?_⟩
  have hunit := N.smul_mem (B.repr x s)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at hunit
  exact hunit

/-- The standard general-linear action on an exterior power is irreducible. -/
theorem isIrreducible_glLieModule (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    letI : LieModule K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieModule (K := K) (n := Fin n) d
    LieModule.IsIrreducible K (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) := by
  classical
  let _ : Nontrivial (⋀[K]^d (Fin n → K)) :=
    ⟨⟨firstBasisWedge (K := K) d n h, 0, firstBasisWedge_ne_zero d n h⟩⟩
  refine LieModule.IsIrreducible.mk fun N hN ↦ ?_
  have hN' : N.toSubmodule ≠ ⊥ := fun h ↦
    hN ((LieSubmodule.toSubmodule_eq_bot N).mp h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'
  obtain ⟨s, hs⟩ := exists_basisWedge_mem_of_nonzero_mem (K := K) d n N hx hx0
  have hfirst := first_mem_of_basisWedge_mem (K := K) d n h N s hs
  apply top_unique
  rw [← lieSpan_firstBasisWedge_eq_top (K := K) d n h]
  exact LieSubmodule.lieSpan_le.mpr (by simpa using hfirst)


end Irreducibility



end exteriorPower
