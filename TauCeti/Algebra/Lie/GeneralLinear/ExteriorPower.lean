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
* `exteriorPower.lieSpan_basisWedge_eq_top`: over a commutative ring, every standard basis wedge
  generates the full exterior power.
* `exteriorPower.isIrreducible_glLieModule`: over a field, the standard exterior-power
  representation is irreducible when `d ≤ Fintype.card ι`.

## Roadmap context

The [highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
uses these exterior modules in two places: Layer 9 constructs the fundamental `gl_n` modules,
while Layer 8 uses the `sl₉` action on `⋀³(K⁹)` in the Vinberg model of `E₈`.

## References

Goodman--Wallach, especially §§5.5 and 9.1, and Fulton--Harris §15.5 provide the
characteristic-zero representation-theoretic background. The matrix-unit path and diagonal
projector arguments here establish cyclicity over a commutative ring and irreducibility over an
arbitrary field. The diagonal-factor and list-product projector proof plan follows the
occupation/vacancy projector construction in `TauCeti.LinearAlgebra.ExteriorAlgebra.End`.
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
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private noncomputable def firstBasisEmbedding (d : ℕ) (h : d ≤ Fintype.card ι) : Fin d ↪o ι :=
  (Fin.castLEOrderEmb h).trans (Fintype.orderIsoFinOfCardEq ι rfl).toOrderEmbedding

private theorem firstBasisEmbedding_apply (d : ℕ) (h : d ≤ Fintype.card ι) (l : Fin d) :
    firstBasisEmbedding d h l = Fintype.orderIsoFinOfCardEq ι rfl (Fin.castLE h l) := rfl

private noncomputable def basisPath (d : ℕ) (h : d ≤ Fintype.card ι)
    (s : Set.powersetCard ι d) (k : ℕ) (l : Fin d) : ι :=
  if l.val < k then firstBasisEmbedding d h l else Set.powersetCard.ofFinEmbEquiv.symm s l

private theorem basisPath_top (d : ℕ) (h : d ≤ Fintype.card ι)
    (s : Set.powersetCard ι d) :
    basisPath d h s d = firstBasisEmbedding d h := by
  funext l
  simp [basisPath, l.isLt]

private theorem basisPath_zero (d : ℕ) (h : d ≤ Fintype.card ι)
    (s : Set.powersetCard ι d) :
    basisPath d h s 0 = Set.powersetCard.ofFinEmbEquiv.symm s := by
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

private theorem basisPath_strictMono (d : ℕ) (h : d ≤ Fintype.card ι)
    (s : Set.powersetCard ι d) (k : ℕ) :
    StrictMono (basisPath d h s k) := by
  intro a b hab
  by_cases ha : a.val < k
  · by_cases hb : b.val < k
    · simp only [basisPath, ha, hb, ite_true]
      exact (firstBasisEmbedding d h).strictMono hab
    · simp only [basisPath, ha, hb, ite_true, ite_false]
      let e := Fintype.orderIsoFinOfCardEq ι rfl
      rw [firstBasisEmbedding_apply,
        ← e.apply_symm_apply (Set.powersetCard.ofFinEmbEquiv.symm s b)]
      apply e.strictMono
      have hs := fin_val_le_of_strictMono
        (fun l ↦ e.symm (Set.powersetCard.ofFinEmbEquiv.symm s l))
        (e.symm.strictMono.comp (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono) b
      exact Fin.mk_lt_mk.mpr
        (lt_of_lt_of_le ha (le_trans (Nat.le_of_not_gt hb) hs))
  · have hb : ¬b.val < k := fun hb ↦ ha (lt_trans hab hb)
    simp only [basisPath, ha, hb, ite_false]
    exact (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hab

private theorem lie_single_basis_family (d : ℕ) (v : Fin d → ι)
    (hv : Function.Injective v) (a : Fin d) (i : ι) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    ⁅Matrix.single i (v a) (1 : K),
      ιMulti K d (fun l ↦ (Pi.single (v l) (1 : K) : ι → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (Function.update v a i l) (1 : K) : ι → K)) := by
  classical
  rw [gl_lie_def, glLieMap_apply_ιMulti]
  simp only [Matrix.single_mulVec_eq, Pi.single_apply, eq_comm]
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
    simpa only [mul_zero, zero_smul] using (ιMulti K d).map_update_zero
      (fun k ↦ (Pi.single (v k) (1 : K) : ι → K)) l
  · simp

private theorem lie_single_basisPath_transition (d : ℕ) (v w : Fin d → ι)
    (hv : Function.Injective v) (a : Fin d) (i : ι)
    (hupdate : Function.update v a i = w) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    ⁅Matrix.single i (v a) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (v l) (1 : K) : ι → K))⁆ =
        ιMulti K d (fun l ↦
          (Pi.single (w l) (1 : K) : ι → K)) := by
  rw [lie_single_basis_family (K := K) d v hv a]
  exact congrArg (ιMulti K d) (congrArg (fun f ↦
    fun l ↦ (Pi.single (f l) (1 : K) : ι → K)) hupdate)

private theorem lie_single_basisPath_transition_of_update (d : ℕ) (v w : Fin d → ι)
    (hv : Function.Injective v) (a : Fin d) (i : ι)
    (hxa : i = w a) (hvw : ∀ l, l ≠ a → v l = w l) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    ⁅Matrix.single i (v a) (1 : K),
      ιMulti K d (fun l ↦ (Pi.single (v l) (1 : K) : ι → K))⁆ =
        ιMulti K d (fun l ↦ (Pi.single (w l) (1 : K) : ι → K)) := by
  apply lie_single_basisPath_transition (K := K) d v w hv a i
  exact Function.update_eq_iff.2 ⟨hxa, hvw⟩

private theorem basisPath_succ_eq_of_ne (d : ℕ) (h : d ≤ Fintype.card ι) (hk : k < d)
    (s : Set.powersetCard ι d) (a l : Fin d) (hla : l ≠ a)
    (ha : a = ⟨k, hk⟩) :
    basisPath d h s (k + 1) l = basisPath d h s k l := by
  have hlk : l.val ≠ k := by
    intro hlk
    apply hla
    exact Fin.ext (hlk.trans (congrArg Fin.val ha.symm))
  by_cases hlt : l.val < k
  · simp [basisPath, hlt, Nat.lt_succ_of_lt hlt]
  · have hsucc : ¬l.val < k + 1 := by omega
    simp [basisPath, hlt, hsucc]

private theorem lie_basisPath_step (d k : ℕ) (h : d ≤ Fintype.card ι) (hk : k < d)
    (s : Set.powersetCard ι d) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    (⁅Matrix.single
          (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩)
          (firstBasisEmbedding d h ⟨k, hk⟩) (1 : K),
        ιMulti K d (fun l ↦
          (Pi.single (basisPath d h s (k + 1) l) (1 : K) : ι → K))⁆ =
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s k l) (1 : K) : ι → K))) ∧
    (⁅Matrix.single
          (firstBasisEmbedding d h ⟨k, hk⟩)
          (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩) (1 : K),
        ιMulti K d (fun l ↦
          (Pi.single (basisPath d h s k l) (1 : K) : ι → K))⁆ =
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s (k + 1) l) (1 : K) : ι → K))) := by
  let a : Fin d := ⟨k, hk⟩
  have hforward_source :
      firstBasisEmbedding d h a = basisPath d h s (k + 1) a := by
    simp [a, basisPath]
  have hreverse_source :
      Set.powersetCard.ofFinEmbEquiv.symm s a = basisPath d h s k a := by
    simp [a, basisPath]
  have hforward_update :
      Function.update (basisPath d h s (k + 1)) a
          (Set.powersetCard.ofFinEmbEquiv.symm s a) = basisPath d h s k := by
    refine Function.update_eq_iff.2 ⟨?_, ?_⟩
    · simp [basisPath, a]
    · intro l hla
      exact basisPath_succ_eq_of_ne d h hk s a l hla rfl
  have hreverse_update :
      Function.update (basisPath d h s k) a (firstBasisEmbedding d h a) =
        basisPath d h s (k + 1) := by
    refine Function.update_eq_iff.2 ⟨?_, ?_⟩
    · simp [basisPath, a]
    · intro l hla
      exact (basisPath_succ_eq_of_ne d h hk s a l hla rfl).symm
  constructor
  · rw [hforward_source]
    exact lie_single_basisPath_transition (K := K) d
      (basisPath d h s (k + 1)) (basisPath d h s k)
      (basisPath_strictMono d h s (k + 1)).injective a
      (Set.powersetCard.ofFinEmbEquiv.symm s a) hforward_update
  · rw [hreverse_source]
    exact lie_single_basisPath_transition (K := K) d
      (basisPath d h s k) (basisPath d h s (k + 1))
      (basisPath_strictMono d h s k).injective a
      (firstBasisEmbedding d h a) hreverse_update

private theorem lie_basisPath_succ (d k : ℕ) (h : d ≤ Fintype.card ι) (hk : k < d)
    (s : Set.powersetCard ι d) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    ⁅Matrix.single
        (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩)
        (firstBasisEmbedding d h ⟨k, hk⟩) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s (k + 1) l) (1 : K) : ι → K))⁆ =
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s k l) (1 : K) : ι → K)) := by
  exact (lie_basisPath_step (K := K) d k h hk s).1

private theorem mem_of_lie_succ_path (d : ℕ)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    (x : ℕ → (⋀[K]^d (ι → K)))
    (hstep : ∀ k, k < d → ∃ a : Matrix ι ι K, ⁅a, x (k + 1)⁆ = x k)
    (hd : x d ∈ N) : x 0 ∈ N := by
  exact Nat.decreasingInduction' (m := 0) (n := d) (P := fun k ↦ x k ∈ N)
    (fun k hk _ ih ↦ by
      obtain ⟨a, ha⟩ := hstep k hk
      rw [← ha]
      exact N.lie_mem ih)
    (Nat.zero_le d) hd

private theorem mem_of_lie_reverse_path (d : ℕ)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    (x : ℕ → (⋀[K]^d (ι → K)))
    (hstep : ∀ k, k < d → ∃ a : Matrix ι ι K, ⁅a, x k⁆ = x (k + 1))
    (h0 : x 0 ∈ N) : x d ∈ N := by
  have hmem : ∀ k, k ≤ d → x k ∈ N := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih =>
        obtain ⟨a, ha⟩ := hstep k (by omega)
        have hnext : ⁅a, x k⁆ ∈ N := N.lie_mem (ih (by omega))
        rw [ha] at hnext
        exact hnext
  exact hmem d le_rfl

private theorem basisWedge_mem_of_first_mem (d : ℕ) (h : d ≤ Fintype.card ι)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    (hfirst : ιMulti K d (fun l ↦
      (Pi.single (firstBasisEmbedding d h l) (1 : K) : ι → K)) ∈ N)
    (s : Set.powersetCard ι d) :
    basisWedge K s.1 (Set.powersetCard.card_eq s) ∈ N := by
  classical
  let _ : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
    glLieRingModule (K := K) (n := ι) d
  have hd : ιMulti K d (fun l ↦
      (Pi.single (basisPath d h s d l) (1 : K) : ι → K)) ∈ N := by
    rw [basisPath_top]
    exact hfirst
  have hzero : ιMulti K d (fun l ↦
      (Pi.single (basisPath d h s 0 l) (1 : K) : ι → K)) ∈ N :=
    mem_of_lie_succ_path (K := K) d N
      (fun k ↦ ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s k l) (1 : K) : ι → K)))
      (fun k hk ↦ by
        refine ⟨Matrix.single
          (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩)
          (firstBasisEmbedding d h ⟨k, hk⟩) (1 : K), ?_⟩
        rw [← lie_basisPath_succ (K := K) d k h hk s]) hd
  rw [basisPath_zero] at hzero
  rw [basisWedge_eq_ιMulti]
  simpa only [Set.powersetCard.ofFinEmbEquiv_symm_apply] using hzero

private theorem lie_basisPath_reverse (d k : ℕ) (h : d ≤ Fintype.card ι) (hk : k < d)
    (s : Set.powersetCard ι d) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    ⁅Matrix.single
        (firstBasisEmbedding d h ⟨k, hk⟩)
        (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩) (1 : K),
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s k l) (1 : K) : ι → K))⁆ =
      ιMulti K d (fun l ↦
        (Pi.single (basisPath d h s (k + 1) l) (1 : K) : ι → K)) := by
  exact (lie_basisPath_step (K := K) d k h hk s).2

private theorem first_mem_of_basisWedge_mem (d : ℕ) (h : d ≤ Fintype.card ι)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    (s : Set.powersetCard ι d)
    (hs : basisWedge K s.1 (Set.powersetCard.card_eq s) ∈ N) :
    ιMulti K d (fun l ↦
      (Pi.single (firstBasisEmbedding d h l) (1 : K) : ι → K)) ∈ N := by
  classical
  let _ : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
    glLieRingModule (K := K) (n := ι) d
  have hzero : ιMulti K d (fun l ↦
      (Pi.single (basisPath d h s 0 l) (1 : K) : ι → K)) ∈ N := by
    rw [basisPath_zero]
    rw [basisWedge_eq_ιMulti] at hs
    simpa only [Set.powersetCard.ofFinEmbEquiv_symm_apply] using hs
  have htop := mem_of_lie_reverse_path (K := K) d N
    (fun k ↦ ιMulti K d (fun l ↦
      (Pi.single (basisPath d h s k l) (1 : K) : ι → K)))
    (fun k hk ↦ by
      refine ⟨Matrix.single
        (firstBasisEmbedding d h ⟨k, hk⟩)
        (Set.powersetCard.ofFinEmbEquiv.symm s ⟨k, hk⟩) (1 : K), ?_⟩
      rw [← lie_basisPath_reverse (K := K) d k h hk s]) hzero
  rw [basisPath_top] at htop
  exact htop

/-- Every standard basis wedge generates the exterior power as a general-linear Lie module. -/
theorem lieSpan_basisWedge_eq_top (d : ℕ) (S : Finset ι) (hS : S.card = d) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    LieSubmodule.lieSpan K (Matrix ι ι K)
      {basisWedge K S hS} = ⊤ := by
  classical
  have h : d ≤ Fintype.card ι := by
    rw [← hS]
    exact S.card_le_univ
  let s : Set.powersetCard ι d := ⟨S, hS⟩
  let N := LieSubmodule.lieSpan K (Matrix ι ι K)
    {basisWedge K S hS}
  apply (LieSubmodule.toSubmodule_eq_top N).mp
  rw [eq_top_iff, ← ((Pi.basisFun K ι).exteriorPower d).span_eq,
    Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  rw [exteriorPower.basis_apply]
  exact basisWedge_mem_of_first_mem (K := K) d h N
    (first_mem_of_basisWedge_mem (K := K) d h N s
      (LieSubmodule.subset_lieSpan (Set.mem_singleton _))) t

/-- The canonical first basis wedge generates the exterior power as a general-linear Lie module. -/
theorem lieSpan_firstBasisWedge_eq_top (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    LieSubmodule.lieSpan K (Matrix (Fin n) (Fin n) K)
      {firstBasisWedge (K := K) d n h} = ⊤ := by
  rw [firstBasisWedge_eq_basisWedge]
  exact lieSpan_basisWedge_eq_top (K := K) d
    (firstBasisSet d n h : Finset (Fin n))
    (Set.powersetCard.card_eq (firstBasisSet d n h))

end Cyclicity

section Irreducibility

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem listProd_end_apply_eq_smul {R : Type*} {N : Type*} {α : Type*}
    [CommSemiring R] [AddCommMonoid N] [Module R N] (f : α → Module.End R N) (c : α → R)
    (x : N) (l : List α) (h : ∀ i ∈ l, f i x = c i • x) :
    (l.map f).prod x = (l.map c).prod • x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj)), map_smul, h i (List.mem_cons_self)]
    rw [smul_smul, mul_comm ((l.map c).prod) (c i)]

private noncomputable def diagonalFactor (d : ℕ)
    (s : Set.powersetCard ι d) (i : ι) :
    Module.End K (⋀[K]^d (ι → K)) :=
  if i ∈ s.1 then glLieMap d (Matrix.single i i 1) else
    1 - glLieMap d (Matrix.single i i 1)

private theorem diagonalFactor_apply (d : ℕ)
    (s t : Set.powersetCard ι d) (i : ι) :
    diagonalFactor (K := K) d s i
        (ιMulti_family K d (Pi.basisFun K ι) t) =
      if (i ∈ s.1) = (i ∈ t.1) then
        ιMulti_family K d (Pi.basisFun K ι) t else 0 := by
  classical
  rw [diagonalFactor]
  have haction := lie_single_self_basisWedge (K := K) t.1 t.2 i
  rw [basisWedge_eq_ιMulti_family t.1 (Set.powersetCard.card_eq t)] at haction
  by_cases his : i ∈ s.1
  · by_cases hit : i ∈ t.1
    · simp only [his, hit, ite_true, eq_self]
      rw [← gl_lie_def, haction]
      simp only [hit, ite_true, one_smul]
    · simp only [his, hit, ite_true, true_ne_false]
      rw [← gl_lie_def, haction]
      simp only [hit, ite_false, zero_smul]
  · by_cases hit : i ∈ t.1
    · simp only [his, hit, ite_false, false_ne_true]
      rw [LinearMap.sub_apply]
      rw [← gl_lie_def, haction]
      simp only [hit, ite_true, Module.End.one_apply, one_smul, sub_self]
    · simp only [his, hit, ite_false, eq_self]
      rw [LinearMap.sub_apply]
      rw [← gl_lie_def, haction]
      simp only [hit, ite_false, Module.End.one_apply, zero_smul, sub_zero, ite_true]

private noncomputable def diagonalProjector (d : ℕ)
    (s : Set.powersetCard ι d) : Module.End K (⋀[K]^d (ι → K)) :=
  ((Finset.univ.toList).map fun i : ι ↦ diagonalFactor (K := K) d s i).prod

private theorem diagonalProjector_coeff_eq_one (d : ℕ)
    (s : Set.powersetCard ι d) :
    ((Finset.univ.toList).map fun j : ι ↦
      if (j ∈ s.1) = (j ∈ s.1) then (1 : K) else 0).prod = 1 := by
  simp

private theorem diagonalProjector_apply (d : ℕ)
    (s t : Set.powersetCard ι d) :
    diagonalProjector (K := K) d s
        (ιMulti_family K d (Pi.basisFun K ι) t) =
      if s = t then ιMulti_family K d (Pi.basisFun K ι) t else 0 := by
  classical
  have hprod : ∀ u : List ι,
      (u.map fun i ↦ diagonalFactor (K := K) d s i).prod
          (ιMulti_family K d (Pi.basisFun K ι) t) =
        (u.map fun i ↦ if (i ∈ s.1) = (i ∈ t.1) then (1 : K) else 0).prod •
          ιMulti_family K d (Pi.basisFun K ι) t := by
    intro u
    apply listProd_end_apply_eq_smul (R := K)
    intro i _
    rw [diagonalFactor_apply]
    by_cases h : (i ∈ s.1) = (i ∈ t.1)
    · simp only [h, ite_true, one_smul]
    · simp only [h, ite_false, zero_smul]
  rw [diagonalProjector, hprod]
  by_cases hst : s = t
  · subst t
    rw [diagonalProjector_coeff_eq_one]
    simp
  · obtain ⟨i, his, hit⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    have hi : (i ∈ s.1) ≠ (i ∈ t.1) := fun h ↦ hit (h.mp his)
    have hzero : ((Finset.univ.toList).map fun j : ι ↦
        if (j ∈ s.1) = (j ∈ t.1) then (1 : K) else 0).prod = 0 := by
      apply List.prod_eq_zero
      rw [List.mem_map]
      refine ⟨i, ?_, by simp [hi]⟩
      simp
    simp only [hst, ite_false]
    rw [hzero, zero_smul]

private theorem diagonalProjector_mem (d : ℕ)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    (s : Set.powersetCard ι d) {x : ⋀[K]^d (ι → K)} (hx : x ∈ N) :
    diagonalProjector (K := K) d s x ∈ N := by
  classical
  let _ : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
    glLieRingModule (K := K) (n := ι) d
  rw [diagonalProjector]
  have hfactor (i : ι) {y : ⋀[K]^d (ι → K)} (hy : y ∈ N) :
      diagonalFactor (K := K) d s i y ∈ N := by
    rw [diagonalFactor]
    by_cases his : i ∈ s.1
    · simp only [his, ite_true]
      rw [← gl_lie_def]
      exact N.lie_mem hy
    · simp only [his, ite_false, LinearMap.sub_apply, Module.End.one_apply]
      rw [← gl_lie_def]
      exact N.sub_mem hy (N.lie_mem hy)
  have hmem : ∀ u : List ι,
      (u.map fun i ↦ diagonalFactor (K := K) d s i).prod x ∈ N := by
    intro u
    induction u with
    | nil => simpa using hx
    | cons i u ih => simpa [Module.End.mul_apply] using hfactor i ih
  exact hmem Finset.univ.toList

private theorem exists_basisWedge_mem_of_nonzero_mem (d : ℕ)
    (N : LieSubmodule K (Matrix ι ι K) (⋀[K]^d (ι → K)))
    {x : ⋀[K]^d (ι → K)} (hx : x ∈ N) (hx0 : x ≠ 0) :
    ∃ s : Set.powersetCard ι d,
      basisWedge K s.1 (Set.powersetCard.card_eq s) ∈ N := by
  classical
  let B := (Pi.basisFun K ι).exteriorPower d
  have hre : B.repr x ≠ 0 := (B.repr.map_ne_zero_iff).2 hx0
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hre
  have hproj : diagonalProjector (K := K) d s x =
      (B.repr x s) • ιMulti_family K d (Pi.basisFun K ι) s := by
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, Finset.sum_eq_single s]
    · rw [map_smul, exteriorPower.basis_apply, diagonalProjector_apply]
      simp
    · intro t _ hts
      rw [map_smul, exteriorPower.basis_apply, diagonalProjector_apply]
      simp only [Ne.symm hts, ite_false, smul_zero]
    · simp
  have hmem := diagonalProjector_mem (K := K) d N s hx
  rw [hproj] at hmem
  refine ⟨s, ?_⟩
  rw [basisWedge_eq_ιMulti_family]
  have hunit := N.smul_mem (B.repr x s)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at hunit
  exact hunit

/-- The standard general-linear action on an exterior power is irreducible when `d` does not exceed
the coordinate cardinality. -/
private theorem isIrreducible_glLieModule_ordered (d : ℕ) (h : d ≤ Fintype.card ι) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    LieModule.IsIrreducible K (Matrix ι ι K) (⋀[K]^d (ι → K)) := by
  classical
  let S : Finset ι := Finset.univ.map (firstBasisEmbedding d h).toEmbedding
  have hS : S.card = d := by simp [S]
  let _ : Nontrivial (⋀[K]^d (ι → K)) :=
    ⟨⟨basisWedge K S hS, 0, basisWedge_ne_zero _ _⟩⟩
  refine LieModule.IsIrreducible.mk fun N hN ↦ ?_
  have hN' : N.toSubmodule ≠ ⊥ := fun h ↦
    hN ((LieSubmodule.toSubmodule_eq_bot N).mp h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'
  obtain ⟨s, hs⟩ := exists_basisWedge_mem_of_nonzero_mem (K := K) d N hx hx0
  apply top_unique
  rw [← lieSpan_basisWedge_eq_top (K := K) d s.1 (Set.powersetCard.card_eq s)]
  exact LieSubmodule.lieSpan_le.mpr (by simpa using hs)


end Irreducibility

section IrreducibilityUnordered

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over a field, the standard general-linear action on the `d`-th exterior power is
irreducible for a finite index type `ι` when `d ≤ Fintype.card ι`; an auxiliary order is
chosen internally for the path argument. -/
theorem isIrreducible_glLieModule (d : ℕ) (h : d ≤ Fintype.card ι) :
    letI : LieRingModule (Matrix ι ι K) (⋀[K]^d (ι → K)) :=
      glLieRingModule (K := K) (n := ι) d
    LieModule.IsIrreducible K (Matrix ι ι K) (⋀[K]^d (ι → K)) := by
  classical
  let order : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι)
    (Fintype.equivFin ι).injective
  exact @isIrreducible_glLieModule_ordered K _ ι _ order d h

end IrreducibilityUnordered



end exteriorPower
