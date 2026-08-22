/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# The inertia subgroups generate the Galois group of a number field

Let `K` be a number field that is Galois over `ℚ`, with Galois group `G` acting on the ring of
integers `𝓞 K`. Each maximal ideal `P` of `𝓞 K` carries an inertia subgroup `P.inertia G`, the
elements of `G` acting trivially on `𝓞 K ⧸ P`, and its cardinality is the ramification index of
`P` over `ℤ` (`Ideal.card_inertia_eq_ramificationIdxIn`). This file proves that these subgroups
generate all of `G`:

`⨆ P : MaximalSpectrum (𝓞 K), P.asIdeal.inertia G = ⊤`.

The proof is Minkowski's theorem in disguise. If `H` contains every inertia subgroup, then over
the fixed field `F` of `H` every prime `P` of `𝓞 K` has the same inertia group as it does over
`ℚ` — because `P.inertia H` is `P.inertia G` intersected with `H`, which is all of it — so the
absolute ramification indices at the top and at the intermediate level agree, and
multiplicativity of ramification in the tower `ℤ ⊆ 𝓞 F ⊆ 𝓞 K` forces `F` to be unramified over
`ℚ` at every finite prime. Minkowski's bound on the discriminant
(`NumberField.exists_not_isUnramifiedIn`) leaves `F = ℚ`, that is `H = ⊤`.

This is the missing input flagged as a TODO of `Mathlib/RingTheory/Polynomial/Morse.lean`, whose
`Polynomial.Splits.surjective_toPermHom_of_iSup_inertia_eq_top` takes generation by inertia
subgroups as a hypothesis.

The second half of the file draws the consequence that genus theory needs. If `M` is abelian over
`ℚ` and unramified at all finite places over a quadratic subfield `F`, then the inertia subgroup
of a prime of `𝓞 M` meets `Gal(M/F)` trivially, so it injects into the two-element quotient
`Gal(M/ℚ) ⧸ Gal(M/F)` and every element of it squares to `1`. Generation by inertia then makes
the whole of `Gal(M/ℚ)` an elementary abelian `2`-group: an abelian extension of `ℚ` unramified
over a quadratic subfield is multiquadratic.

## Main results

* `NumberField.eq_top_of_forall_inertia_le`: a subgroup of `G` containing every inertia subgroup
  is `⊤`.
* `NumberField.iSup_inertia_eq_top`, `NumberField.closure_iUnion_inertia_eq_top`: the packaged
  generation statements.
* `NumberField.disjoint_inertia_of_isUnramifiedIn`: if `K` is unramified over the fixed field of
  `H` at all finite places, then every inertia subgroup meets `H` trivially.
* `NumberField.sq_eq_one_of_index_eq_two`, `NumberField.sq_eq_one_of_finrank_eq_two`: an abelian
  extension of `ℚ` unramified at all finite places over a quadratic subfield has Galois group of
  exponent dividing `2`.

## References

Generation of a Galois group by inertia subgroups is Section 4.4 of [J. P. Serre, *Topics in
Galois Theory*][serre-galois]; the genus-theoretic consequence is the standard proof that the
genus field is multiquadratic, as in D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and
F. Lemmermeyer, *Reciprocity Laws: from Euler to Eisenstein*, §2.2.
-/

public section

open scoped NumberField

namespace NumberField

section Generation

variable {K : Type*} [Field K] [NumberField K] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G K] [IsGaloisGroup G ℚ K]

variable {G} in
/-- **A subgroup containing every inertia subgroup is everything.** Let `K` be a number field
Galois over `ℚ` with Galois group `G`. If a subgroup `H` of `G` contains the inertia subgroup of
every maximal ideal of `𝓞 K`, then `H = ⊤`.

The fixed field `F` of `H` inherits no ramification: for a prime `P` of `𝓞 K` the inertia
subgroups of `P` in `H` and in `G` coincide, so the ramification indices `e(P / ℤ)` and
`e(P / 𝓞 F)` agree and the intermediate index `e(𝔮 / ℤ)` is `1`. By Minkowski's theorem a number
field unramified over `ℚ` is `ℚ`, so `F = ℚ`. -/
theorem eq_top_of_forall_inertia_le {H : Subgroup G}
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → P.inertia G ≤ H) : H = ⊤ := by
  classical
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H with hF
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  -- Every nonzero prime of `𝓞 F` is unramified over `ℤ`.
  have hq : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → q.ramificationIdx ℤ = 1 := by
    intro q hqp hq0
    have : q.IsPrime := hqp
    obtain ⟨P, hPp, hPq⟩ := (inferInstance : Nonempty (Ideal.primesOver q (𝓞 K))).some
    have : P.IsPrime := hPp
    have : P.LiesOver q := hPq
    have hPmax : P.IsMaximal := hPp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P)
    have htower : P.ramificationIdx ℤ = q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
      Ideal.ramificationIdx_tower (R := ℤ) q P
    -- The two inertia subgroups of `P`, over `ℚ` and over `F`, have the same cardinality.
    have hG : Nat.card (P.inertia G) = P.ramificationIdx ℤ := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G]
    have hH : Nat.card (P.inertia H) = P.ramificationIdx (𝓞 F) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (P.under (𝓞 F)) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P H]
    have hcard : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
      have hsub : P.inertia H = (P.inertia G).subgroupOf H := rfl
      rw [hsub]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h P hPmax)).toEquiv
    have hEq : P.ramificationIdx (𝓞 F) = P.ramificationIdx ℤ := by rw [← hH, hcard, hG]
    rw [hEq] at htower
    exact Nat.eq_of_mul_eq_mul_right (Ideal.ramificationIdx_pos (R := ℤ) (q := P))
      (by rw [one_mul, ← htower])
  -- Hence `F` is unramified over `ℚ`, so `F = ℚ` by Minkowski's theorem.
  have hrank : Module.finrank ℚ F = 1 := by
    by_contra hne
    obtain ⟨p, hp, hnu⟩ := NumberField.exists_not_isUnramifiedIn (K := F) (𝒪 := 𝓞 F) hne
    refine hnu (Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun q _ hqp => ?_)
    have : q.LiesOver (Ideal.span {(p : ℤ)}) := hqp
    refine hq q inferInstance
      (Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) ?_ q)
    simpa using hp.ne_zero
  refine Subgroup.eq_top_of_card_eq H ?_
  rw [IsGaloisGroup.card_eq_finrank H F K, IsGaloisGroup.card_eq_finrank G ℚ K,
    ← Module.finrank_mul_finrank ℚ F K, hrank, one_mul]

/-- **The inertia subgroups generate the Galois group.** For a number field `K` Galois over `ℚ`
with Galois group `G`, the supremum of the inertia subgroups of the maximal ideals of `𝓞 K`
is `⊤`. -/
theorem iSup_inertia_eq_top : ⨆ P : MaximalSpectrum (𝓞 K), P.asIdeal.inertia G = ⊤ :=
  eq_top_of_forall_inertia_le fun P hP =>
    le_iSup (fun Q : MaximalSpectrum (𝓞 K) => Q.asIdeal.inertia G) ⟨P, hP⟩

/-- The union of the inertia subgroups of the maximal ideals of `𝓞 K` generates `G`. This is the
`Subgroup.closure` form of `NumberField.iSup_inertia_eq_top`. -/
theorem closure_iUnion_inertia_eq_top :
    Subgroup.closure (⋃ P : MaximalSpectrum (𝓞 K), (P.asIdeal.inertia G : Set G)) = ⊤ := by
  rw [Subgroup.closure_iUnion]
  simpa using iSup_inertia_eq_top G

end Generation

section Unramified

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G K] [IsGaloisGroup G ℚ K]
  {F : Type*} [Field F] [NumberField F] [Algebra ℚ F] [Algebra F K] [IsScalarTower ℚ F K]

omit [IsGaloisGroup G ℚ K] [Algebra ℚ F] [IsScalarTower ℚ F K] in
/-- **An unramified subextension meets every inertia subgroup trivially.** Let `H` be a subgroup
of `G` whose fixed field is `F`. If every prime of `𝓞 F` is unramified in `𝓞 K`, then the inertia
subgroup of a prime `P` of `𝓞 K` is disjoint from `H`, since its intersection with `H` is the
inertia subgroup of `P` over `𝓞 F`, of order `e(P / 𝓞 F) = 1`. -/
theorem disjoint_inertia_of_isUnramifiedIn (H : Subgroup G) [IsGaloisGroup H F K]
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → Algebra.IsUnramifiedIn (𝓞 K) q)
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) : Disjoint (P.inertia G) H := by
  have : P.IsPrime := hP
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  rw [← Subgroup.subgroupOf_eq_bot]
  refine Subgroup.eq_bot_of_card_eq _ ?_
  have hsub : (P.inertia G).subgroupOf H = P.inertia H := rfl
  rw [hsub, Ideal.card_inertia_eq_ramificationIdxIn (G := H) (P.under (𝓞 F)) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P H]
  exact (hunr (P.under (𝓞 F)) inferInstance).ramificationIdx_eq_one inferInstance

omit [IsGaloisGroup G ℚ K] [Algebra ℚ F] [IsScalarTower ℚ F K] in
/-- **Inertia over a quadratic subfield is killed by squaring.** If the fixed field `F` of an
index-`2` subgroup `H` of `G` has every prime unramified in `𝓞 K`, then any element of an inertia
subgroup of `G` squares to `1`: its square lies in `H` because `H` has index `2`, and it lies in
the inertia subgroup, which meets `H` trivially. -/
theorem sq_eq_one_of_mem_inertia {H : Subgroup G} [IsGaloisGroup H F K] (hindex : H.index = 2)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → Algebra.IsUnramifiedIn (𝓞 K) q)
    {P : Ideal (𝓞 K)} (hP : P.IsPrime) {g : G} (hg : g ∈ P.inertia G) : g ^ 2 = 1 := by
  have hmem : g ^ 2 ∈ H := by
    rw [sq]
    exact (Subgroup.mul_mem_iff_of_index_two hindex).mpr Iff.rfl
  exact Subgroup.disjoint_def.mp (disjoint_inertia_of_isUnramifiedIn H hunr P hP)
    (pow_mem hg 2) hmem

omit [Algebra ℚ F] [IsScalarTower ℚ F K] in
open scoped IsMulCommutative in
/-- **An abelian extension of `ℚ` unramified over a quadratic subfield is multiquadratic.** Let
`K` be a number field, Galois over `ℚ` with abelian Galois group `G`, and let `H` be a subgroup of
index `2` whose fixed field `F` has every prime unramified in `𝓞 K`. Then every element of `G`
squares to `1`.

Indeed each inertia subgroup consists of elements squaring to `1`
(`NumberField.sq_eq_one_of_mem_inertia`), and in an abelian group those elements form a subgroup;
since the inertia subgroups generate `G` (`NumberField.eq_top_of_forall_inertia_le`), that
subgroup is all of `G`. -/
theorem sq_eq_one_of_index_eq_two [IsMulCommutative G] (H : Subgroup G) [IsGaloisGroup H F K]
    (hindex : H.index = 2)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → Algebra.IsUnramifiedIn (𝓞 K) q) (g : G) :
    g ^ 2 = 1 := by
  have h : (powMonoidHom 2 : G →* G).ker = ⊤ :=
    eq_top_of_forall_inertia_le fun P hP x hx => by
      simpa [MonoidHom.mem_ker] using sq_eq_one_of_mem_inertia hindex hunr hP.isPrime hx
  simpa [MonoidHom.mem_ker] using (h ▸ Subgroup.mem_top g : g ∈ (powMonoidHom 2 : G →* G).ker)

open scoped IsMulCommutative in
/-- **The degree form of `NumberField.sq_eq_one_of_index_eq_two`.** If `K` is Galois over `ℚ` with
abelian Galois group `G`, if `F` is the fixed field of `H` and is quadratic over `ℚ`, and if every
prime of `𝓞 F` is unramified in `𝓞 K`, then every element of `G` squares to `1`. The index of `H`
is the degree of its fixed field, here `2`. -/
theorem sq_eq_one_of_finrank_eq_two [IsMulCommutative G] (H : Subgroup G) [IsGaloisGroup H F K]
    (hF : Module.finrank ℚ F = 2)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → Algebra.IsUnramifiedIn (𝓞 K) q) (g : G) :
    g ^ 2 = 1 := by
  refine sq_eq_one_of_index_eq_two H ?_ hunr g
  have h : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
  rw [IsGaloisGroup.card_eq_finrank H F K, IsGaloisGroup.card_eq_finrank G ℚ K,
    ← Module.finrank_mul_finrank ℚ F K, hF] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

end Unramified

end NumberField
