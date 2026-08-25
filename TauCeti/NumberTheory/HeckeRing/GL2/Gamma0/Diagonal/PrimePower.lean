/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Elem

/-!
# The diagonal generators of the `Γ₀(N)` Hecke ring

This file builds the two generating classes of the Hecke ring `R(Γ₀(N), Δ₀(N))` on top of the
general diagonal element `diagElemGamma0` from `Diagonal/Elem.lean`, together with the family
the Diamond–Shurman recurrence assembles.

The two generators specialise that element: `heckeTGeneratorGamma0 p` at `![1, p]` and
`heckeTScalarGamma0 p` at `![p, p]`. The iterated family `heckeTGeneratorRecGamma0 p r`
satisfies `T₀ = 1`, `T₁ = T_p` and

`T_{r+2} = T_p · T_{r+1} − (p · S_p) · T_r`,

which when `p` shares a factor with the level degenerates to `T_r = T_p^r`, the scalar term
having vanished.

Every declaration here is stated for an arbitrary natural `p`, and the names say so: they
follow `heckeTDiag`/`heckeTScalar`/`heckeT` at level one (`GL2/Basic.lean`), none of which
asks `Nat.Prime` either. The elements *are* the classical `T_p` and `T_{p^r}` of `Γ₀(N)`
exactly when `p` is prime — that is the intended reading, and the recurrence is chosen to
match it — but nothing below assumes it, so nothing below is named for it.

Neither the per-prime product formula nor the composite element assembled over a prime
factorisation is proved here; this file supplies the generators those need.

## Main definitions

* `HeckeRing.GL2.heckeTGeneratorGamma0`: the generator `Γ₀(N)·diag(1, p)·Γ₀(N)`.
* `HeckeRing.GL2.heckeTScalarGamma0`: the scalar generator `Γ₀(N)·diag(p, p)·Γ₀(N)`, or `0`.
* `HeckeRing.GL2.heckeTGeneratorRecGamma0`: the family the recurrence generates.

## Main results

* `HeckeRing.GL2.heckeTGeneratorRecGamma0_succ_succ`: the recurrence, as a rewriting rule.
* `HeckeRing.GL2.heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime`: when `p` shares a
  factor with the level, the recurrence degenerates to a power of the generator.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
* Diamond–Shurman, *A first course in modular forms*, §5.3 — the prime-power recurrence
  `T_{p^{r+1}} = T_p T_{p^r} − p^{k−1}⟨p⟩ T_{p^{r−1}}` this file's `heckeTGeneratorRecGamma0`
  transcribes to the ring.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`, declarations `heckeRingDp`,
  `heckeRingSpp`, `heckeRingSpp_of_not_coprime`, `heckeRingDppow`, `heckeRingDppow_zero`,
  `heckeRingDppow_one`, `heckeRingDppow_succ_succ` and
  `heckeRingDppow_eq_pow_of_not_coprime`. Three hypotheses of the source are dropped here: the
  generator no longer asks `0 < p`, and neither the scalar generator nor the iterated family
  asks `Nat.Prime p` — none is needed to define the elements or to prove the
  recurrence, and carrying them would force every consumer to supply a primality proof for a
  statement that does not use it. The names follow this namespace's `heckeT*` family rather
  than the source's `heckeRing*`, and drop the source's `p`/`prime` vocabulary along with the
  hypothesis it stood for.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The diagonal generator of the `Γ₀(N)` Hecke ring: for `0 < p` the class of
`Γ₀(N)·diag(1, p)·Γ₀(N)`, including when `p` shares a factor with the level, and `0` at
`p = 0`. At a prime `p` this is the classical `T_p`.

No coprimality is asked of `p`: the head entry of `![1, p]` is `1`, which is coprime to every
level, so only positivity can send this to the junk branch, and it does exactly at `p = 0`
(`heckeTGeneratorGamma0_zero`). No consumer needs `0 < p` as a hypothesis, so it is not
imposed on the definition. -/
noncomputable def heckeTGeneratorGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![1, p]

/-- The scalar generator of the `Γ₀(N)` Hecke ring: the class of `Γ₀(N)·diag(p, p)·Γ₀(N)` when
`0 < p` and `p` is coprime to the level, and `0` otherwise. Both halves of the guard bite:
`heckeTScalarGamma0 1 0` is `0` even though `0` is coprime to the level `1`.

Unlike `heckeTGeneratorGamma0` the coprimality here has content, because the head entry of
`![p, p]` is `p`. For `0 < p` sharing a factor with `N` the vanishing is a membership fact —
`diag(p, p) ∉ Δ₀(N)` — and mirrors `⟨p⟩ = 0`. At `p = 0` it is instead a junk-value
convention: `natDiagGL 2 ![0, 0]` is the identity and so *does* lie in `Δ₀(N)`, but the
positivity guard sends the element to `0` at every level, coprime or not. -/
noncomputable def heckeTScalarGamma0 (p : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  diagElemGamma0 N ![p, p]

/-- The diagonal generator as a `single`. The guard has two halves: coprimality is discharged
outright by `Nat.coprime_one_left`, since the head entry of `![1, p]` is `1`, and the supplied
`0 < p` discharges positivity — so past that hypothesis this is the class of the double coset.
Named `_eq_single` rather than `_def` because it states the two-level unfolding, not the
definition; `heckeTGeneratorGamma0_def` below is the actual defining equation. -/
lemma heckeTGeneratorGamma0_eq_single {p : ℕ} (hp : 0 < p) :
    heckeTGeneratorGamma0 N p =
      HeckeCosetModule.single ℤ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) 1 :=
  diagElemGamma0_of_pos_of_coprime N (by intro i; fin_cases i <;> simp [hp])
    (Nat.coprime_one_left N)

/-- **The defining equation of the diagonal generator**: it *is* `diagElemGamma0` at `![1, p]`.
Both generator bodies are sealed, so without this the `diagElemGamma0_*` API is unreachable
for them. -/
lemma heckeTGeneratorGamma0_def (p : ℕ) :
    heckeTGeneratorGamma0 N p = diagElemGamma0 N ![1, p] := (rfl)

/-- **The defining equation of the scalar generator**, the companion of
`heckeTGeneratorGamma0_def`. -/
lemma heckeTScalarGamma0_def (p : ℕ) :
    heckeTScalarGamma0 N p = diagElemGamma0 N ![p, p] := (rfl)

/-- The scalar generator in the coprime branch, where it is nonzero. -/
lemma heckeTScalarGamma0_of_coprime {p : ℕ} (hp : 0 < p) (hpN : Nat.Coprime p N) :
    heckeTScalarGamma0 N p =
      HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p] fun _ ↦ hpN) 1 :=
  diagElemGamma0_of_pos_of_coprime N (by intro i; fin_cases i <;> simpa using hp) hpN

/-- The scalar generator vanishes when `p` shares a factor with the level. This is the case
that lets the recurrence below be stated without splitting on whether `p` divides `N`. -/
@[simp]
theorem heckeTScalarGamma0_of_not_coprime {p : ℕ} (hpN : ¬ Nat.Coprime p N) :
    heckeTScalarGamma0 N p = 0 :=
  diagElemGamma0_of_not_coprime N hpN

/-- At `p = 1` the scalar generator is the identity: `diag(1, 1)` is the identity matrix. -/
@[simp]
theorem heckeTScalarGamma0_one : heckeTScalarGamma0 N 1 = 1 :=
  diagElemGamma0_one_one N

/-- At `p = 0` the generator vanishes: `![1, 0]` is not everywhere positive. -/
@[simp]
theorem heckeTGeneratorGamma0_zero : heckeTGeneratorGamma0 N 0 = 0 :=
  diagElemGamma0_of_not_pos N fun h ↦ absurd (h 1) (by simp)

/-- At `p = 0` the scalar generator vanishes too, for the same reason and at every level. The
two generators agreeing here is what the shared positivity guard buys: before it, this one
vanished only because `0` is not coprime to `N > 1`, and so had no unconditional normal
form. -/
@[simp]
theorem heckeTScalarGamma0_zero : heckeTScalarGamma0 N 0 = 0 :=
  diagElemGamma0_of_not_pos N fun h ↦ absurd (h 0) (by simp)

/-- At `p = 1` the generator is the identity for the other reason: `diag(1, 1)` *is* the
identity matrix, so this is `diagElemGamma0_one` rather than the degeneracy case above. -/
@[simp]
theorem heckeTGeneratorGamma0_one : heckeTGeneratorGamma0 N 1 = 1 :=
  diagElemGamma0_one_one N

-- `[NeZero N]` enters only here: the recurrence multiplies in the Hecke ring, and the
-- `IsHeckeTriple` instance behind `*` needs it. Everything above builds `single`, `0` and `1`
-- only, so it is deliberately not carried by those declarations.
variable [NeZero N]

/-- The family generated from `heckeTGeneratorGamma0` by the Diamond–Shurman recurrence
`T₀ = 1`, `T₁ = T_p` and `T_{r+2} = T_p · T_{r+1} − (p · S_p) · T_r`.

The recurrence is chosen so that at a prime `p` the `r`-th term is the classical `T_{p^r}`,
but it is defined for every natural `p` and nothing here assumes primality. -/
noncomputable def heckeTGeneratorRecGamma0 (p : ℕ) : ℕ → 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ
  | 0 => 1
  | 1 => heckeTGeneratorGamma0 N p
  | r + 2 =>
    heckeTGeneratorGamma0 N p * heckeTGeneratorRecGamma0 p (r + 1) -
      ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTGeneratorRecGamma0 p r

-- `heckeTGeneratorRecGamma0` is given by pattern matching, so its three defining equations are
-- compiler-generated equation lemmas; `rw [heckeTGeneratorRecGamma0]` is what applies them.
-- That is a different mechanism from the `_def` lemmas above, which are `(rfl)` against a
-- non-recursive sealed body — sealing is not what rules `rfl` out here.
/-- The empty product: `T₀ = 1`. -/
@[simp]
theorem heckeTGeneratorRecGamma0_zero (p : ℕ) : heckeTGeneratorRecGamma0 N p 0 = 1 := by
  rw [heckeTGeneratorRecGamma0]

/-- The first term is the generator itself: `T₁ = T_p`. -/
@[simp]
theorem heckeTGeneratorRecGamma0_one (p : ℕ) :
    heckeTGeneratorRecGamma0 N p 1 = heckeTGeneratorGamma0 N p := by
  rw [heckeTGeneratorRecGamma0]

/-- The `r + 2` case of the recurrence, as a rewriting rule. Not a `simp` lemma: the right-hand
side mentions `heckeTGeneratorRecGamma0` at two smaller arguments, so it is a recursion to
unfold deliberately rather than a normal form to rewrite towards. -/
theorem heckeTGeneratorRecGamma0_succ_succ (p r : ℕ) :
    heckeTGeneratorRecGamma0 N p (r + 2) = heckeTGeneratorGamma0 N p *
      heckeTGeneratorRecGamma0 N p (r + 1) -
        ((p : ℤ) • heckeTScalarGamma0 N p) * heckeTGeneratorRecGamma0 N p r := by
  rw [heckeTGeneratorRecGamma0]

/-- When `p` shares a factor with the level the scalar term vanishes and the recurrence
degenerates to a power of the generator: `T_r = T_p^r`.

`@[simp]` because this is the normal form once the coprimality hypothesis is in context: it
is conditional, so it fires only where `¬ Nat.Coprime p N` can be discharged, and leaves the
unconditional `heckeTGeneratorRecGamma0_zero`/`_one` normal forms alone elsewhere. -/
@[simp]
theorem heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime {p : ℕ}
    (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    heckeTGeneratorRecGamma0 N p r = heckeTGeneratorGamma0 N p ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r _ih0 ih1 =>
    simp [heckeTGeneratorRecGamma0_succ_succ, heckeTScalarGamma0_of_not_coprime N hpN, ih1,
      ← pow_succ']

end HeckeRing.GL2
