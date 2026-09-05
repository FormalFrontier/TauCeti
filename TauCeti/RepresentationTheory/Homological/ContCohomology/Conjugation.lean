/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Conjugation on explicit first continuous cohomology

If `N` is a normal subgroup of a topological group `G`, conjugation by `g` on `N`, together
with the action of `g` on coefficients, is a compatible pair.  This file packages the resulting
map on the explicit quotient `H¹(N, M)`.  The map is written with the inverse conjugation
`h ↦ g⁻¹ h g`, so that its coefficient component is the left action `m ↦ g • m`.

The construction is functorial in `g`, hence gives the expected `G`-action.  When `g` belongs to
`N`, the induced map is the identity: the difference of a cocycle and its conjugate is the
principal cocycle attached to `c g`.  The file also records the degree-one and degree-two
components of the corresponding bar homotopy, including the degree-two cocycle identity that
expresses the conjugation difference as a coboundary.
-/

public section

namespace TauCeti.ContCohomology

open TauCeti.ContinuousMonoidHom

universe uG uM uK uA

section

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The conjugation compatible-pair identity on coefficients. -/
theorem inverseConjugationHom_smul (N : Subgroup G) [N.Normal] (g : G) (n : N) (m : M) :
    (DistribSMul.toAddMonoidHom M g)
        (ContinuousMonoidHom.inverseConjugationHom N g n • m) =
      n • (DistribSMul.toAddMonoidHom M g) m := by
  -- Unfold the subgroup action so the compatible-pair identity is an identity for the ambient
  -- `G`-action, where `mul_smul` applies directly.
  simp only [DistribSMul.toAddMonoidHom_apply,
    ContinuousMonoidHom.inverseConjugationHom_apply]
  change g • ((g⁻¹ * (n : G) * g) • m) = (n : G) • (g • m)
  simp [smul_smul, mul_assoc]

/-- Conjugation by `g`, with the coefficient action of `g`, on explicit `H¹`. -/
noncomputable def explicitConj1 (N : Subgroup G) [N.Normal] (g : G) : H1 N M →+ H1 N M :=
  explicitMap1 N M N M (inverseConjugationHom N g) (DistribSMul.toAddMonoidHom M g)
    ((continuous_const_smul g).congr fun _ => rfl) (inverseConjugationHom_smul N g)

/-- The conjugation/coefficient action on explicit first cohomology, defined by
`explicitConj1`. -/
noncomputable instance (N : Subgroup G) [N.Normal] : SMul G (H1 N M) where
  smul g := explicitConj1 (M := M) N g

/-- The installed scalar action is the map `explicitConj1`. -/
@[simp]
theorem explicitConj1_apply_eq_smul (N : Subgroup G) [N.Normal] (g : G) (x : H1 N M) :
    explicitConj1 N g x = g • x :=
  rfl

/-- The representative formula for `explicitConj1`. -/
@[simp]
theorem explicitConj1_mk (N : Subgroup G) [N.Normal] (g : G) (c : Z1 N M) :
    explicitConj1 N g (c : H1 N M) =
      (cocyclesMap1 N M N M (inverseConjugationHom N g)
        (DistribSMul.toAddMonoidHom M g) ((continuous_const_smul g).congr fun _ => rfl)
        (inverseConjugationHom_smul N g) c : H1 N M) :=
  explicitMap1_mk N M N M _ _ _ _ c

/-- The degree-one component of the bar homotopy for inverse conjugation. -/
def inverseConjugationHomotopy1 {K : Type uK} [Group K] {A : Type uA} [AddCommGroup A]
    (g : K) (c : K → A) : A :=
  c g

/-- The degree-two component of the bar homotopy for inverse conjugation. -/
def inverseConjugationHomotopy2 {K : Type uK} [Group K] {A : Type uA} [AddCommGroup A]
    (g : K) (c : K × K → A) : K → A :=
  fun n => c (g, g⁻¹ * n * g) - c (n, g)

/-! The following identity is algebraic; the topological subgroup specialization is stated below. -/
theorem inverseConjugationCochainHomotopy1 {K : Type uK} [Group K]
    {A : Type uA} [AddCommGroup A] [DistribMulAction K A] (g : K) (c : K → A) :
    cochainsMap1 (MulAut.conj g⁻¹ : K →* K) (DistribSMul.toAddMonoidHom A g) c - c =
      d0 K A (inverseConjugationHomotopy1 g c) +
        inverseConjugationHomotopy2 g (d1 K A c) := by
  ext n
  simp only [Pi.sub_apply, Pi.add_apply, cochainsMap1_apply, d0_apply, d1_apply,
    inverseConjugationHomotopy1, inverseConjugationHomotopy2,
    DistribSMul.toAddMonoidHom_apply]
  -- The bundled additive hom and the scalar action have the same underlying function here.
  change g • c ((MulAut.conj g⁻¹ : MulAut K) n) - c n = _
  simp only [MulAut.conj_apply, inv_inv]
  have hmul : g * (g⁻¹ * n * g) = n * g := by
    simp [mul_assoc]
  rw [hmul]
  simp only [sub_eq_add_neg]
  abel_nf

/-- The degree-two component of the bar homotopy for an algebraic inverse conjugation. -/
theorem inverseConjugationCochainHomotopy2 {K : Type uK} [Group K]
    {A : Type uA} [AddCommGroup A] [DistribMulAction K A] (g : K) (c : K × K → A)
    (hc : groupCohomology.IsCocycle₂ c) :
    cochainsMap2 (MulAut.conj g⁻¹ : K →* K) (DistribSMul.toAddMonoidHom A g) c - c =
      d1 K A (inverseConjugationHomotopy2 g c) := by
  apply funext
  rintro ⟨n, k⟩
  simp only [Pi.sub_apply, cochainsMap2_apply, d1_apply, inverseConjugationHomotopy2,
    DistribSMul.toAddMonoidHom_apply]
  -- The cochain map is bundled, so expose its underlying conjugation before using `hc`.
  change g • c ((MulAut.conj g⁻¹ : MulAut K) n, (MulAut.conj g⁻¹ : MulAut K) k) - c (n, k) = _
  simp only [MulAut.conj_apply, inv_inv]
  have hmul : g * (g⁻¹ * n * g) = n * g := by
    simp [mul_assoc]
  have hmul' : g * (g⁻¹ * k * g) = k * g := by
    simp [mul_assoc]
  have hconjmul : (g⁻¹ * n * g) * (g⁻¹ * k * g) = g⁻¹ * (n * k) * g := by
    simp [mul_assoc]
  have h₁ := hc g (g⁻¹ * n * g) (g⁻¹ * k * g)
  have h₂ := hc n g (g⁻¹ * k * g)
  have h₃ := hc n k g
  simp only [hmul, hmul', hconjmul] at h₁ h₂ h₃
  have h₁' : g • c (g⁻¹ * n * g, g⁻¹ * k * g) =
      c (n * g, g⁻¹ * k * g) + c (g, g⁻¹ * n * g) - c (g, g⁻¹ * (n * k) * g) := by
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using h₁.symm
  have h₂' : n • c (g, g⁻¹ * k * g) =
      c (n * g, g⁻¹ * k * g) + c (n, g) - c (n, k * g) := by
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using h₂.symm
  have h₃' : n • c (k, g) =
      c (n * k, g) + c (n, k) - c (n, k * g) := by
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using h₃.symm
  rw [h₁']
  simp only [smul_add, smul_neg, sub_eq_add_neg]
  rw [h₂', h₃']
  simp only [sub_eq_add_neg, add_assoc]
  abel

/-- The degree-one bar-homotopy identity for inverse conjugation on continuous cocycles. -/
theorem inverseConjugationHomotopy1_spec (N : Subgroup G) [N.Normal] (g : N) (c : Z1 N M) :
    d0 N M (inverseConjugationHomotopy1 g c) =
      (cocyclesMap1 N M N M (inverseConjugationHom N (g : G))
        (DistribSMul.toAddMonoidHom M (g : G))
        ((continuous_const_smul (g : G)).congr fun _ => by
          simp only [DistribSMul.toAddMonoidHom_apply])
        (inverseConjugationHom_smul N (g : G)) c : N → M) - (c : N → M) := by
  have hc : d1 N M (c : N → M) = 0 := by
    apply funext
    intro p
    obtain ⟨n, k⟩ := p
    exact congrFun (d1_apply_eq_zero_iff.2 ((mem_Z1_iff.1 c.property).2)) (n, k)
  have hconj :
      (inverseConjugationHom N (g : G) : N →* N) =
        (MulAut.conj (g⁻¹) : MulAut N) := by
    ext n
    simp [inverseConjugationHom_apply]
  have h := inverseConjugationCochainHomotopy1 (K := N) (A := M) g (c : N → M)
  rw [← hconj] at h
  change cochainsMap1 (inverseConjugationHom N (g : G) : N →* N)
      (DistribSMul.toAddMonoidHom M (g : G)) (c : N → M) - c = _ at h
  rw [hc] at h
  have hz : inverseConjugationHomotopy2 g (0 : N × N → M) = 0 := by
    funext n
    simp [inverseConjugationHomotopy2]
  rw [hz, add_zero] at h
  ext n
  simp only [Pi.sub_apply]
  rw [cocyclesMap1_apply]
  have hp := congrFun h.symm n
  rw [Pi.sub_apply, cochainsMap1_apply] at hp
  exact hp

omit [ContinuousSMul G M] in
/-- The degree-two bar-homotopy identity for inverse conjugation on continuous cocycles. -/
theorem inverseConjugationHomotopy2_spec (N : Subgroup G) [N.Normal] (g : N) (c : Z2 N M) :
    cochainsMap2 (inverseConjugationHom N (g : G) : N →* N)
        (DistribSMul.toAddMonoidHom M (g : G)) c - c =
      d1 N M (inverseConjugationHomotopy2 g c) := by
  have hconj :
      (inverseConjugationHom N (g : G) : N →* N) =
        (MulAut.conj (g⁻¹) : MulAut N) := by
    ext n
    simp [inverseConjugationHom_apply]
  have h := inverseConjugationCochainHomotopy2 (K := N) (A := M) g (c : N × N → M)
      (mem_Z2_iff.1 c.property).2
  rw [← hconj] at h
  change cochainsMap2 (inverseConjugationHom N (g : G) : N →* N)
      (DistribSMul.toAddMonoidHom M (g : G)) (c : N × N → M) - c = _ at h
  exact h

omit [IsTopologicalGroup G] in
private theorem explicitMap1_congr_of_eq (N : Subgroup G)
    {φ ψ : N →ₜ* N} {f q : M →+ M}
    {hf : Continuous f} {hq : Continuous q}
    {hφ : ∀ (n : N) (m : M), f (φ n • m) = n • f m}
    {hψ : ∀ (n : N) (m : M), q (ψ n • m) = n • q m}
    (hφeq : φ = ψ) (hfeq : f = q) :
    explicitMap1 N M N M φ f hf hφ = explicitMap1 N M N M ψ q hq hψ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap1_mk, explicitMap1_mk]
      apply congrArg (fun z : Z1 N M => (z : H1 N M))
      ext n
      simp only [cocyclesMap1_coe, cochainsMap1_apply, MonoidHom.coe_coe]
      rw [hφeq, hfeq]

/-- Conjugation by the identity gives the identity map on explicit `H¹`. -/
@[simp]
theorem explicitConj1_one (N : Subgroup G) [N.Normal] :
    explicitConj1 (M := M) N 1 = AddMonoidHom.id _ := by
  unfold explicitConj1
  have hφ : inverseConjugationHom N 1 = ContinuousMonoidHom.id N :=
    inverseConjugationHom_one N
  have hf : DistribSMul.toAddMonoidHom.{uG, uM} M (1 : G) = AddMonoidHom.id M := by
    ext m
    simp
  have hcont : Continuous (DistribSMul.toAddMonoidHom M (1 : G)) := by
    exact (continuous_const_smul 1).congr fun _ => rfl
  have hmap := explicitMap1_congr_of_eq (M := M) N
    (φ := inverseConjugationHom N (1 : G)) (ψ := ContinuousMonoidHom.id N)
    (f := DistribSMul.toAddMonoidHom M (1 : G)) (q := AddMonoidHom.id M)
    (hf := hcont) (hq := continuous_id) (hφ := inverseConjugationHom_smul N 1)
    (hψ := fun _ _ => rfl) (hφeq := hφ) (hfeq := hf)
  exact hmap.trans (explicitMap1_id N M (fun _ _ => rfl))

/-- Successive conjugations compose in the order dictated by the left `G`-action. -/
@[simp]
theorem explicitConj1_mul (N : Subgroup G) [N.Normal] (g h : G) :
    explicitConj1 (M := M) N (g * h) =
      (explicitConj1 (M := M) N g).comp (explicitConj1 (M := M) N h) := by
  unfold explicitConj1
  have hφ : inverseConjugationHom N (g * h) =
      (inverseConjugationHom N h).comp (inverseConjugationHom N g) :=
    inverseConjugationHom_mul N g h
  have hf : DistribSMul.toAddMonoidHom M (g * h) =
      (DistribSMul.toAddMonoidHom M g).comp (DistribSMul.toAddMonoidHom M h) := by
    ext m
    simp [mul_smul]
  have hcomp := comp_apply_smul
    (inverseConjugationHom N h : N →* N) (inverseConjugationHom N g : N →* N)
    (DistribSMul.toAddMonoidHom M h) (DistribSMul.toAddMonoidHom M g)
    (inverseConjugationHom_smul N h) (inverseConjugationHom_smul N g)
  have hcontg : Continuous (DistribSMul.toAddMonoidHom M g) := by
    exact (continuous_const_smul g).congr fun _ => rfl
  have hconth : Continuous (DistribSMul.toAddMonoidHom M h) := by
    exact (continuous_const_smul h).congr fun _ => rfl
  have hcontgh : Continuous (DistribSMul.toAddMonoidHom M (g * h)) := by
    exact (continuous_const_smul (g * h)).congr fun _ => rfl
  have hmap := explicitMap1_congr_of_eq (M := M) N
    (φ := inverseConjugationHom N (g * h))
    (ψ := (inverseConjugationHom N h).comp (inverseConjugationHom N g))
    (f := DistribSMul.toAddMonoidHom M (g * h))
    (q := (DistribSMul.toAddMonoidHom M g).comp (DistribSMul.toAddMonoidHom M h))
    (hf := hcontgh) (hq := hcontg.comp hconth)
    (hφ := inverseConjugationHom_smul N (g * h)) (hψ := hcomp)
    (hφeq := hφ) (hfeq := hf)
  exact hmap.trans (explicitMap1_comp N M N M (inverseConjugationHom N h)
      (DistribSMul.toAddMonoidHom M h) hconth
      (inverseConjugationHom_smul N h) N M (inverseConjugationHom N g)
      (DistribSMul.toAddMonoidHom M g) hcontg
      (inverseConjugationHom_smul N g) hcomp)

/-- The conjugation/coefficient action on explicit first cohomology satisfies the group action
laws. -/
noncomputable instance (N : Subgroup G) [N.Normal] : MulAction G (H1 N M) where
  one_smul x := by
    -- The `SMul` instance is defined by the explicit map, so this is its identity law.
    change explicitConj1 (M := M) N 1 x = x
    rw [explicitConj1_one]
    rfl
  mul_smul g h x := by
    -- Likewise, the action law is the composition law for the compatible pairs.
    change explicitConj1 (M := M) N (g * h) x =
      explicitConj1 (M := M) N g (explicitConj1 (M := M) N h x)
    rw [explicitConj1_mul]
    rfl

/-- An element of the subgroup acts trivially on its explicit first cohomology.

This is the inner-automorphism triviality of Milne, *Arithmetic Duality Theorems*,
Proposition 0.15. -/
theorem explicitConj1_eq_id_of_mem (N : Subgroup G) [N.Normal] (g : N) :
    explicitConj1 (M := M) N (g : G) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitConj1_mk, AddMonoidHom.id_apply, H1pi_eq_iff]
      refine mem_B1_iff.2 ⟨(c : N → M) g, ?_⟩
      intro n
      simpa [d0_apply, inverseConjugationHomotopy1] using
        congrFun (inverseConjugationHomotopy1_spec N g c) n

end

end TauCeti.ContCohomology
