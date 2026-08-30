/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.FieldTheory.Galois.IsGaloisGroup
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The inertia subgroups generate the Galois group of a number field

Let `K` be a number field that is Galois over `ℚ`, with Galois group `G` acting on the ring of
integers `𝓞 K`. Each maximal ideal `P` of `𝓞 K` carries an inertia subgroup `P.inertia G`, the
elements of `G` acting trivially on `𝓞 K ⧸ P`, and its cardinality is the ramification index of
`P` over `ℤ` (`Ideal.card_inertia_eq_ramificationIdx`, in
`TauCeti/NumberTheory/RamificationInertia/Galois.lean`). This file proves that these subgroups
generate all of `G`:

`⨆ P : MaximalSpectrum (𝓞 K), P.asIdeal.inertia G = ⊤`.

The engine is a dictionary between ramification in an intermediate field and containment of
inertia subgroups. For a subgroup `H` with fixed field `F` and a prime `P` of `𝓞 K`, the prime of
`𝓞 F` below `P` is unramified over `ℤ` exactly when `P.inertia G ≤ H`: multiplicativity of
ramification in the tower `ℤ ⊆ 𝓞 F ⊆ 𝓞 K` writes `e(P / ℤ)` as `e(𝔮 / ℤ) * e(P / 𝓞 F)`, and the
two absolute indices are the cardinalities of `P.inertia G` and of `P.inertia H`, which is
`P.inertia G ⊓ H`. Quantifying over the primes above a rational prime `p` turns this into a test
for ramification of `p` in `F`, and when the Galois group is commutative all those primes share an
inertia subgroup, so a single prime upstairs suffices.

Generation is then Minkowski's theorem. If `H` contains every inertia subgroup, the dictionary
makes its fixed field `F` unramified over `ℚ` at every finite prime, and Minkowski's bound on the
discriminant (`NumberField.exists_not_isUnramifiedIn`) leaves `F = ℚ`, that is `H = ⊤`.

This is the missing input flagged as a TODO of `Mathlib/RingTheory/Polynomial/Morse.lean`, whose
`Polynomial.Splits.surjective_toPermHom_of_iSup_inertia_eq_top` takes generation by inertia
subgroups as a hypothesis.

The second half of the file draws the consequence that genus theory needs. If `M` is abelian over
`ℚ` and unramified at all finite places over the fixed field `F` of a subgroup `H`, then the
inertia subgroup of a prime of `𝓞 M` meets `Gal(M/F)` trivially, so every element of it is killed
by the index of `H`. Generation by inertia promotes this to all of `Gal(M/ℚ)`, whose exponent
therefore divides `H.index = [F : ℚ]`. Taking `F` quadratic is the classical first step towards
the genus field being multiquadratic; the passage from exponent `2` to a compositum of quadratic
fields is Kummer theory over `ℚ` and is not formalised here.

## Main results

* `NumberField.ramificationIdx_under_eq_one_iff_inertia_le`: unramifiedness of the intermediate
  prime below `P` is containment of the inertia subgroup of `P`.
* `NumberField.notMem_ramifiedPrimes_iff_forall_inertia_le`: the same dictionary for a rational
  prime, quantified over the primes of `𝓞 K` above it.
* `NumberField.notMem_ramifiedPrimes_iff_inertia_le`: for a commutative Galois group, one prime
  upstairs suffices.
* `NumberField.eq_top_of_forall_inertia_le`: a subgroup of `G` containing every inertia subgroup
  is `⊤`.
* `NumberField.iSup_inertia_eq_top`: the packaged generation statement.
* `NumberField.disjoint_inertia_of_ramificationIdx_eq_one`: if `P` is unramified over the fixed
  field of `H`, then the inertia subgroup at `P` meets `H` trivially.
* `NumberField.pow_index_eq_one_of_isUnramifiedIn`: if `G` is abelian and `K` is unramified over
  the fixed field `F` of `H` at every prime of `𝓞 F`, then the exponent of `G` divides `H.index`,
  which is `Module.finrank ℚ F` by `IsGaloisGroup.index_eq_finrank` (in
  `TauCeti/FieldTheory/Galois/IsGaloisGroup.lean`).
* `NumberField.aut_exponent_dvd_finrank_of_isUnramifiedIn`: the resulting degree bound for the
  automorphism group of an abelian number-field extension and an arbitrary intermediate field.

## References

Generation of a Galois group by inertia subgroups is Section 4.4 of [J. P. Serre, *Topics in
Galois Theory*][serre-galois]; the genus-theoretic consequence is the standard proof that the
genus field is multiquadratic, as in D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and
F. Lemmermeyer, *Reciprocity Laws: from Euler to Eisenstein*, §2.2.
-/

public section

open scoped NumberField

namespace NumberField

/-- **A number field unramified at every finite prime is `ℚ`.** If every nonzero prime of `𝓞 F`
is unramified over `ℤ`, then `Module.finrank ℚ F = 1`. This is Minkowski's bound on the
discriminant, in the form `NumberField.exists_not_isUnramifiedIn`. -/
theorem finrank_eq_one_of_forall_ramificationIdx_eq_one {F : Type*} [Field F] [NumberField F]
    (h : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → q.ramificationIdx ℤ = 1) :
    Module.finrank ℚ F = 1 := by
  by_contra hne
  obtain ⟨p, hp, hnu⟩ := NumberField.exists_not_isUnramifiedIn (K := F) (𝒪 := 𝓞 F) hne
  refine hnu (Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun q _ hqp => ?_)
  have : q.LiesOver (Ideal.span {(p : ℤ)}) := hqp
  refine h q inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) ?_ q)
  simpa using hp.ne_zero

section Intermediate

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G K] [IsGaloisGroup G ℚ K]
  {F : Type*} [Field F] [NumberField F] [Algebra F K]

/-- **Unramifiedness in an intermediate field is containment of inertia.** Let `H` be a subgroup
of `G` with fixed field `F`, and let `P` be a prime of `𝓞 K`. The prime of `𝓞 F` below `P` is
unramified over `ℤ` exactly when the inertia subgroup of `P` is contained in `H`.

Both directions come from one computation: multiplicativity of ramification in the tower
`ℤ ⊆ 𝓞 F ⊆ 𝓞 K` writes `e(P / ℤ)` as `e(𝔮 / ℤ) * e(P / 𝓞 F)`, while
`Ideal.card_inertia_eq_ramificationIdx` reads the two absolute indices as the cardinalities of
`P.inertia G` and of `P.inertia H = P.inertia G ⊓ H`. So `e(𝔮 / ℤ) = 1` says exactly that the
intersection is everything.

`NumberField.disjoint_inertia_of_ramificationIdx_eq_one` is the complementary statement, about
`P` being unramified over `𝓞 F` rather than `𝔮` over `ℤ`. -/
theorem ramificationIdx_under_eq_one_iff_inertia_le (H : Subgroup G) [IsGaloisGroup H F K]
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) :
    (P.under (𝓞 F)).ramificationIdx ℤ = 1 ↔ P.inertia G ≤ H := by
  have : P.IsPrime := hP
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  have htower : P.ramificationIdx ℤ
      = (P.under (𝓞 F)).ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 F)) P
  have hinf : Nat.card ((P.inertia G ⊓ H : Subgroup G)) = P.ramificationIdx (𝓞 F) := by
    rw [← Ideal.card_inertia_eq_ramificationIdx (𝓞 F) H P,
      ← AddSubgroup.inertia_map_subtype (I := P.toAddSubgroup) H]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm
  rw [← Ideal.card_inertia_eq_ramificationIdx ℤ G P] at htower
  constructor
  · intro hq
    rw [hq, one_mul, ← hinf] at htower
    have hle : (P.inertia G ⊓ H : Subgroup G) ≤ P.inertia G := inf_le_left
    have htop : (P.inertia G ⊓ H).subgroupOf (P.inertia G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]; exact htower.symm)
    exact le_trans (Subgroup.subgroupOf_eq_top.mp htop) inf_le_right
  · intro hle
    rw [inf_of_le_left hle] at hinf
    rw [← hinf] at htower
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P.inertia G))
      (by rw [one_mul]; exact htower.symm)

/-- **Ramification of a rational prime in an intermediate field, read off the inertia subgroups.**
Let `H` be a subgroup of `G` with fixed field `F`. A rational prime `p` is unramified in `F`
exactly when the inertia subgroup of every prime of `𝓞 K` above `p` is contained in `H`.

Every prime of `𝓞 F` above `p` is the prime below some prime of `𝓞 K` above `p`, so this is
`NumberField.ramificationIdx_under_eq_one_iff_inertia_le` quantified over the primes upstairs. -/
theorem notMem_ramifiedPrimes_iff_forall_inertia_le (H : Subgroup G) [IsGaloisGroup H F K]
    {p : ℕ} (hp : p.Prime) :
    p ∉ ramifiedPrimes F ↔ ∀ P : Ideal (𝓞 K), P.IsPrime →
      P.LiesOver (Ideal.span {(p : ℤ)}) → P.inertia G ≤ H := by
  have hmem : p ∉ ramifiedPrimes F ↔ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
    simp only [mem_ramifiedPrimes_iff, not_and, not_not]
    exact ⟨fun h => h hp, fun h _ => h⟩
  rw [hmem, Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  constructor
  · intro h P hP hPp
    have : P.IsPrime := hP
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPp
    rw [← ramificationIdx_under_eq_one_iff_inertia_le (F := F) H P hP]
    exact h (P.under (𝓞 F)) inferInstance
  · intro hle r hr hrp
    have : r.IsPrime := hr
    have : r.LiesOver (Ideal.span {(p : ℤ)}) := hrp
    obtain ⟨P', hP'p, hP'r⟩ := (inferInstance : Nonempty (Ideal.primesOver r (𝓞 K))).some
    have : P'.IsPrime := hP'p
    have : P'.LiesOver r := hP'r
    have hP'p2 : P'.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P' r _
    have := (ramificationIdx_under_eq_one_iff_inertia_le (F := F) H P' hP'p).mpr
      (hle P' hP'p hP'p2)
    rwa [← Ideal.over_def (A := 𝓞 F) P' r] at this

/-- **Ramification of a rational prime in an intermediate field, tested at one prime upstairs.**
Let `H` be a subgroup of the abelian Galois group `G` with fixed field `F`, and let `P` be a prime
of `𝓞 K` above the rational prime `p`. Then `p` is unramified in `F` exactly when the inertia
subgroup of `P` is contained in `H`.

Only one prime `P` above `p` has to be inspected: a commutative Galois group acts transitively on
the primes above `p` and translation conjugates inertia subgroups, so they all share one inertia
subgroup (`Ideal.inertia_eq_of_liesOver`). -/
theorem notMem_ramifiedPrimes_iff_inertia_le [IsMulCommutative G] (H : Subgroup G)
    [IsGaloisGroup H F K] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) :
    p ∉ ramifiedPrimes F ↔ P.inertia G ≤ H := by
  have : P.IsPrime := hP
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPp
  rw [notMem_ramifiedPrimes_iff_forall_inertia_le (K := K) (F := F) H hp]
  refine ⟨fun h => h P hP hPp, fun h P' hP' hP'p => ?_⟩
  have : P'.IsPrime := hP'
  have : P'.LiesOver (Ideal.span {(p : ℤ)}) := hP'p
  exact (Ideal.inertia_eq_of_liesOver (Ideal.span {(p : ℤ)}) P' P G).trans_le h

end Intermediate

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
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  let _ : NumberField F := NumberField.of_intermediateField F
  -- Every nonzero prime of `𝓞 F` is unramified over `ℤ`.
  have hq : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → q.ramificationIdx ℤ = 1 := by
    intro q hqp hq0
    have : q.IsPrime := hqp
    obtain ⟨P, hPp, hPq⟩ := (inferInstance : Nonempty (Ideal.primesOver q (𝓞 K))).some
    have : P.IsPrime := hPp
    have : P.LiesOver q := hPq
    have hPmax : P.IsMaximal := hPp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P)
    have hunr := (ramificationIdx_under_eq_one_iff_inertia_le (F := F) H P hPp).mpr (h P hPmax)
    rwa [← Ideal.over_def (A := 𝓞 F) P q] at hunr
  -- Hence `F` is unramified over `ℚ`, so `F = ℚ` by Minkowski's theorem, and `H` has index `1`.
  exact Subgroup.index_eq_one.mp ((IsGaloisGroup.index_eq_finrank H ℚ F K).trans
    (finrank_eq_one_of_forall_ramificationIdx_eq_one hq))

/-- **The inertia subgroups generate the Galois group.** For a number field `K` Galois over `ℚ`
with Galois group `G`, the supremum of the inertia subgroups of the maximal ideals of `𝓞 K`
is `⊤`. -/
@[simp] theorem iSup_inertia_eq_top : ⨆ P : MaximalSpectrum (𝓞 K), P.asIdeal.inertia G = ⊤ :=
  eq_top_of_forall_inertia_le fun P hP =>
    le_iSup (fun Q : MaximalSpectrum (𝓞 K) => Q.asIdeal.inertia G) ⟨P, hP⟩

end Generation

section Unramified

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G K] [IsGaloisGroup G ℚ K]
  {F : Type*} [Field F] [NumberField F] [Algebra ℚ F] [Algebra F K] [IsScalarTower ℚ F K]

omit [IsGaloisGroup G ℚ K] [Algebra ℚ F] [IsScalarTower ℚ F K] in
/-- **The inertia subgroup at an unramified prime meets `H` trivially.** Let `H` be a subgroup of
`G` whose fixed field is `F`. If `P` is unramified over `𝓞 F`, then the inertia subgroup of `P`
is disjoint from `H`, since its intersection with `H` is the inertia subgroup of `P` over `𝓞 F`,
of order `e(P / 𝓞 F) = 1`. -/
theorem disjoint_inertia_of_ramificationIdx_eq_one (H : Subgroup G) [IsGaloisGroup H F K]
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hunr : P.ramificationIdx (𝓞 F) = 1) :
    Disjoint (P.inertia G) H := by
  have : P.IsPrime := hP
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  rw [← Subgroup.subgroupOf_eq_bot]
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [AddSubgroup.subgroupOf_inertia, Ideal.card_inertia_eq_ramificationIdx (𝓞 F) H P]
  exact hunr

omit [IsGaloisGroup G ℚ K] [Algebra ℚ F] [IsScalarTower ℚ F K] in
/-- **The index of `H` kills inertia at a prime unramified over the fixed field.** If `H` is a
normal subgroup of `G` with fixed field `F` and `P` is unramified over `𝓞 F`, then every element
of the inertia subgroup at `P` is killed by `H.index`: its `H.index`-th power lies in `H`, and it
lies in the inertia subgroup, which meets `H` trivially. -/
theorem pow_index_eq_one_of_ramificationIdx_eq_one {H : Subgroup G} [H.Normal]
    [IsGaloisGroup H F K] {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hunr : P.ramificationIdx (𝓞 F) = 1) {g : G} (hg : g ∈ P.inertia G) : g ^ H.index = 1 :=
  Subgroup.disjoint_def.mp (disjoint_inertia_of_ramificationIdx_eq_one H P hP hunr)
    (pow_mem hg _) (H.pow_index_mem g)

omit [Algebra ℚ F] [IsScalarTower ℚ F K] in
open scoped IsMulCommutative in
/-- **An abelian extension of `ℚ` unramified over a subfield has exponent dividing its degree.**
Let `K` be a number field, Galois over `ℚ` with abelian Galois group `G`, and let `H` be a
subgroup whose fixed field `F` has every prime unramified in `𝓞 K`. Then `g ^ H.index = 1` for
every `g : G`, and `H.index` is `Module.finrank ℚ F` by `IsGaloisGroup.index_eq_finrank`.

Indeed each inertia subgroup is killed by `H.index`
(`NumberField.pow_index_eq_one_of_ramificationIdx_eq_one`), and in an abelian group the elements
killed by a fixed exponent form a subgroup; since the inertia subgroups generate `G`
(`NumberField.eq_top_of_forall_inertia_le`), that subgroup is all of `G`.

For `F` quadratic this says that an abelian extension of `ℚ` unramified over a quadratic subfield
has exponent dividing `2`; by Kummer theory over `ℚ` — not formalised here — such an extension is
a compositum of quadratic fields. -/
theorem pow_index_eq_one_of_isUnramifiedIn [IsMulCommutative G] (H : Subgroup G)
    [IsGaloisGroup H F K]
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → Algebra.IsUnramifiedIn (𝓞 K) q) (g : G) :
    g ^ H.index = 1 := by
  have h : (powMonoidHom H.index : G →* G).ker = ⊤ :=
    eq_top_of_forall_inertia_le fun P hP x hx => by
      have : P.IsPrime := hP.isPrime
      simpa [MonoidHom.mem_ker] using
        pow_index_eq_one_of_ramificationIdx_eq_one (F := F) (H := H) hP.isPrime
          ((hunr (P.under (𝓞 F)) inferInstance).ramificationIdx_eq_one inferInstance) hx
  simpa [MonoidHom.mem_ker] using
    (h ▸ Subgroup.mem_top g : g ∈ (powMonoidHom H.index : G →* G).ker)

end Unramified

end NumberField

namespace NumberField

open scoped IsMulCommutative NumberField

variable {M : Type*} [Field M] [NumberField M] [IsAbelianGalois ℚ M]

/-- **An abelian extension unramified over a subfield has exponent dividing its degree.**
Let `M / ℚ` be an abelian number-field extension and let `F ⊆ M`. If every finite prime of `F`
is unramified in `M`, then `Monoid.exponent Gal(M/ℚ) ∣ [F : ℚ]`. -/
theorem aut_exponent_dvd_finrank_of_isUnramifiedIn (F : IntermediateField ℚ M)
    (hunr : ∀ q : Ideal (𝓞 F), q.IsPrime → q ≠ ⊥ → Algebra.IsUnramifiedIn (𝓞 M) q) :
    Monoid.exponent (M ≃ₐ[ℚ] M) ∣ Module.finrank ℚ F := by
  let _ : NumberField F := NumberField.of_intermediateField F
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro σ
  let H : Subgroup (M ≃ₐ[ℚ] M) := fixingSubgroup (M ≃ₐ[ℚ] M) (F : Set M)
  have hpow := NumberField.pow_index_eq_one_of_isUnramifiedIn H (fun q hq => by
    by_cases hq0 : q = ⊥
    · subst q
      exact Algebra.isUnramifiedIn_bot (R := 𝓞 F) (S := 𝓞 M)
    · exact hunr q hq hq0) σ
  rw [IsGaloisGroup.index_eq_finrank H ℚ F M] at hpow
  exact hpow

end NumberField
