/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# The upper-triangular Hecke sum is `Γ₀(N)`-equivariant when `p ∣ N`

`UpperTri/Sum.lean` defines `heckeSlashUpperTri k p f = ∑_{b < p} f ∣[k] !![1, b; 0, p]`, and
`UpperTri/Periodic.lean` shows it preserves invariance under the single matrix `T`. That is far
short of an operator: to act on `M_k(Γ₁(N))` the sum has to preserve invariance under the whole
group. This file proves that it does, **provided `p` divides the level** — the case in which the
factorisation below closes on the `p` upper-triangular representatives.

## The permutation

Write `γ = !![a, b; c, d] ∈ Γ₀(N)`, so `N ∣ c` and hence `p ∣ c`. Then

`!![1, j; 0, p] · γ = !![a + jc, b + jd; pc, pd]`,

and one asks for a factorisation `γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)`. Matching entries forces
`γ' = !![a + jc, b'; pc, d - cj']` and `p b' = b + jd - (a + jc) j'`, so `j'` must solve
`a j' ≡ b + jd (mod p)`. Because `p ∣ c`, the determinant identity `ad - bc = 1` reduces to
`ad ≡ 1 (mod p)`: `a` is invertible modulo `p`, with inverse `d`, and the unique solution in
`[0, p)` is

`j' = d b + j d² mod p`,

which is `upperTriShift p γ`. It is a bijection of `Fin p` because `d²` is again invertible
modulo `p`. Slashing therefore permutes the summands, and the sum is unchanged up to the scalar
by which `γ'` acts on `f`.

Two facts make that scalar behave. The new lower-right entry is `d - c j' ≡ d (mod N)`, so `γ'`
has the *same* `Gamma0Map` value as `γ`; and if `γ ∈ Γ₁(N)` then `γ' ∈ Γ₁(N)`. So the hypothesis
on `f` is only ever used at matrices congruent to `γ` in the relevant sense, which is what lets
the nebentypus version below carry a fixed character.

⚠ `p ∣ N` is essential to the equivariance proved here, not a convenience. When `p` is prime and
`p ∤ N`, the classical double coset has one further left coset, represented by
`!![p, 0; 0, 1]` up to a `Γ₀(N)` twist, and the sum over the upper-triangular representatives
alone is *not* invariant.

## Main definitions

* `HeckeRing.GL2.upperTriShift`: the offset map `j ↦ d b + j d² mod p`.

## Main results

* `HeckeRing.GL2.upperTriShift_bijective`: it is a bijection of `Fin p`.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul`: the factorisation
  `!![1, j; 0, p] · γ = γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)` of the same `Gamma0Map` value.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0`: the equivariance, stated with an
  arbitrary scalar so that both corollaries below are instances of it.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1`: the sum of a `Γ₁(N)`-invariant
  function is `Γ₁(N)`-invariant.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_nebentypus`: the sum of a function with
  nebentypus `χ` has nebentypus `χ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- **The offset map**, `j ↦ d b + j d² mod p`, where `γ = !![a, b; c, d]`. -/
def upperTriShift (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) : Fin p :=
  ⟨((γ 1 1 * γ 0 1 + (j : ℕ) * (γ 1 1 * γ 1 1) : ℤ) : ZMod p).val, ZMod.val_lt _⟩

/-- The defining congruence of `upperTriShift`, in `ZMod p`. -/
@[simp] lemma upperTriShift_natCast (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) :
    ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 1 1 * γ 0 1 + (j : ℕ) * (γ 1 1 * γ 1 1) : ℤ) : ZMod p) :=
  ZMod.natCast_rightInverse _

/-- **The offset map is a bijection.** For `γ ∈ Γ₀(p)`, `d` is the inverse of `a` modulo `p`,
so the map gives the unique solution in `[0, p)` of `a j' ≡ b + j d (mod p)`.
Two offsets with the same shift differ by an element killed by the unit `d²`. -/
lemma upperTriShift_bijective [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) :
    Function.Bijective (upperTriShift p γ) := by
  refine Finite.injective_iff_bijective.mp fun j j' hjj ↦ ?_
  have had := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp
  have h := congrArg (fun m : Fin p ↦ ((m : ℕ) : ZMod p)) hjj
  simp only [upperTriShift_natCast] at h
  push_cast at h
  have hud : IsUnit ((γ 1 1 : ℤ) : ZMod p) :=
    IsUnit.of_mul_eq_one _ (by simpa [mul_comm] using had)
  have hcancel : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) :=
    (hud.mul hud).mul_left_inj.mp (by linear_combination h)
  exact Fin.val_injective (by
    simpa [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt j'.isLt] using
      congrArg ZMod.val hcancel)

/-- The matrix identity behind the coset factorisation, with the four entries of the second
factor given by hypothesis. Stated separately so that the computation runs on atoms: the
entries of `γ` and `γ'` never have to be unfolded inside it. -/
private lemma upperTriRep_mul_mapGL_eq {p : ℕ} (j j' : Fin p) (γ γ' : SL(2, ℤ))
    (h00 : γ' 0 0 = γ 0 0 + (j : ℕ) * γ 1 0)
    (h01 : (p : ℤ) * γ' 0 1
      = γ 0 1 + (j : ℕ) * γ 1 1 - (γ 0 0 + (j : ℕ) * γ 1 0) * (j' : ℕ))
    (h10 : γ' 1 0 = (p : ℤ) * γ 1 0)
    (h11 : γ' 1 1 = γ 1 1 - γ 1 0 * (j' : ℕ)) :
    upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p j' := by
  have c00 := congrArg (Int.cast : ℤ → ℚ) h00
  have c01 := congrArg (Int.cast : ℤ → ℚ) h01
  have c10 := congrArg (Int.cast : ℤ → ℚ) h10
  have c11 := congrArg (Int.cast : ℤ → ℚ) h11
  push_cast at c00 c01 c10 c11
  refine Units.ext (Matrix.ext fun r t ↦ ?_)
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, coe_upperTriRep, coe_upperTriRep, mapGL_coe_matrix, mapGL_coe_matrix]
  fin_cases r <;> fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, algebraMap_int_eq, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply, one_mul, mul_one, mul_zero,
      add_zero, zero_mul, zero_add] <;>
    [linear_combination -c00; linear_combination -c01 - ((j' : ℕ) : ℚ) * c00;
      linear_combination -c10; linear_combination -((j' : ℕ) : ℚ) * c10 - (p : ℚ) * c11]

/-- **The coset factorisation.** For `p ∣ N` and `γ ∈ Γ₀(N)`, the product
`!![1, j; 0, p] · γ` factors as `γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)` and `j'` the shifted
offset. The new lower-right entry is congruent to the old one modulo `N`, so `γ'` has the same
`Gamma0Map` value as `γ`: this is what makes the equivariance below carry a fixed character. -/
theorem exists_mem_Gamma0_upperTriRep_mul [NeZero p] (hpN : p ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (j : Fin p) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧ ((γ' 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  have hcN : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  have hγp : γ ∈ Gamma0 p := Gamma0_le_Gamma0_of_dvd hpN hγ
  have had := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp
  -- the entry `b'` is an integer: the congruence `a j' ≡ b + j d (mod p)` is exactly `p ∣ …`
  have hdvd : (p : ℤ) ∣ γ 0 1 + (j : ℕ) * γ 1 1
      - (γ 0 0 + (j : ℕ) * γ 1 0) * ((upperTriShift p γ j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [upperTriShift_natCast, Gamma0_mem.mp hγp]
    push_cast
    linear_combination (-((γ 0 1 : ℤ) : ZMod p)
      - ((j : ℕ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p)) * had
  obtain ⟨b', hb'⟩ := hdvd
  have hdet' : (!![γ 0 0 + (j : ℕ) * γ 1 0, b';
      (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 1 0 : ℤ) * hb'
  refine ⟨⟨_, hdet'⟩, Gamma0_mem.mpr ?_, ?_,
    upperTriRep_mul_mapGL_eq _ _ _ _ rfl hb'.symm rfl rfl⟩
  -- Unfold the two relevant projections of the explicitly displayed `SL(2, ℤ)` witness.
  · change (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · change (((γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ) : ℤ)) : ZMod N) = _
    push_cast
    rw [hcN]
    ring

/-- **The upper-triangular sum is `Γ₀(N)`-equivariant at `p ∣ N`.** The hypothesis is imposed
only at matrices of `Γ₀(N)` with the same lower-right entry modulo `N` as `γ`, which is all the
factorisation ever produces; the scalar `u` is left free so that the two corollaries below —
`Γ₁(N)`-invariance and nebentypus transport — are both instances. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) {f : ℍ → ℂ} {u : ℂ}
    (hf : ∀ δ ∈ Gamma0 N, ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) →
      f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = u • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
      = u • heckeSlashUpperTri k p f := by
  rw [heckeSlashUpperTri_def, SlashAction.sum_slash, Finset.smul_sum]
  have key : ∀ j : Fin p,
      (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ)) ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
        = u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)) := fun j ↦ by
    obtain ⟨γ', hγ', hdd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul hpN hγ j
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf γ' hγ' hdd,
      ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p _) f u]
  rw [Finset.sum_congr rfl fun j _ ↦ key j]
  exact Fintype.sum_bijective (upperTriShift p γ)
    (upperTriShift_bijective (Gamma0_le_Gamma0_of_dvd hpN hγ))
    (fun j ↦ u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)))
    (fun j ↦ u • (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ))) fun _ ↦ rfl

/-- **The upper-triangular sum preserves `Γ₁(N)`-invariance at `p ∣ N`** — the invariance that
turns it into an operator on `M_k(Γ₁(N))`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) {f : ℍ → ℂ}
    (hf : ∀ δ ∈ Gamma1 N, f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ) = heckeSlashUpperTri k p f := by
  have h11 : ((γ 1 1 : ℤ) : ZMod N) = 1 := (mem_Gamma1_iff.mp hγ).2
  have h := heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (u := 1) k hpN
    (Gamma1_in_Gamma0 N hγ) (f := f) fun δ hδ hd ↦ by
      rw [hf δ (mem_Gamma1_iff.mpr ⟨hδ, hd.trans h11⟩), one_smul]
  rwa [one_smul] at h

/-- **The upper-triangular sum preserves the nebentypus at `p ∣ N`**: if `f` transforms under
`Γ₀(N)` by the character `χ`, so does `heckeSlashUpperTri k p f`. This is the function-level
statement behind the fact that the operator preserves `M_k(N, χ)`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_nebentypus (k : ℤ) [NeZero p] (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) (γ : ↥(Gamma0 N)) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℚ (δ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) • heckeSlashUpperTri k p f := by
  apply heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 k hpN γ.2
  intro δ hδ hd
  have hmap : (Gamma0Map N).toHomUnits ⟨δ, hδ⟩ = (Gamma0Map N).toHomUnits γ := Units.ext hd
  rw [hf ⟨δ, hδ⟩, hmap]

end HeckeRing.GL2

end
