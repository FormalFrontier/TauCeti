/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Contractions of cochain complexes and their normalization

A *contraction* of a cochain complex `K` onto a cochain complex `L` consists of an inclusion
`i : L ⟶ K`, a projection `p : K ⟶ L` with `p i = 1`, and a degree `-1` cochain `h` on `K` with

`1 - i p = d h + h d`.

Homological perturbation theory, and in particular the tree formula for transferred `A∞`
operations, needs a contraction which additionally satisfies the three *side conditions*

`h i = 0`,   `p h = 0`,   `h h = 0`.

Such data is a *special* contraction, classically a strong deformation retract.  Demanding the
side conditions of every caller would be a bad interface: they are not what a contraction is
naturally produced with.  This file therefore takes the weaker datum as the input and proves that
it can always be normalized.  `TauCeti.Contraction.normalize` turns an arbitrary contraction into
a special one with the *same* `i` and `p`, changing only the homotopy.

The normalization is the classical two-step argument.  Write `Ψ = 1 - i p` for the complementary
idempotent.  The first step replaces `h` by `h₁ = Ψ h Ψ`: this kills `h i` and `p h` because
`Ψ i = 0` and `p Ψ = 0`, and it is still a contracting homotopy because `Ψ` is idempotent and is
a chain map.  The second step replaces `h₁` by `h₂ = h₁ d h₁`.  The two annihilation conditions
survive, and the new homotopy squares to zero: the degree `-2` cochain `h₁ h₁` is a cocycle,
hence commutes with `d`, so `h₂ h₂` contains the factor `d (h₁ h₁) d = d d (h₁ h₁) = 0`.  That
`h₂` is still a contracting homotopy is visible from the equivalent form
`h₂ = h₁ - d (h₁ h₁)`, whose correction term is `δ`-closed.

Cochains and their differential are Mathlib's `CochainComplex.HomComplex` API.  In degree `-1`
that differential is `δ (-1) 0 h = h d + d h`, with no sign, so it is exactly the operator the
contracting equation constrains.

## Main definitions

* `TauCeti.Contraction`: the weak input, a contraction of `K` onto `L`.
* `TauCeti.Contraction.idem` and `TauCeti.Contraction.idemCompl`: the idempotent `i p` cut out by
  a contraction, and its complement `1 - i p`.
* `TauCeti.SpecialContraction`: a contraction satisfying the three side conditions.
* `TauCeti.Contraction.homotopy₁` and `TauCeti.Contraction.homotopy₂`: the two normalization steps.
* `TauCeti.Contraction.normalize`: the special contraction produced from a contraction.
* `TauCeti.Contraction.homotopyEquiv`: the homotopy equivalence between `L` and `K` underlying a
  contraction.

## Main results

* `TauCeti.Contraction.δ_homotopy₂`: the twice-normalized cochain is still a contracting homotopy.
* `TauCeti.Contraction.incl_comp_homotopy₂`, `TauCeti.Contraction.homotopy₂_comp_proj`, and
  `TauCeti.Contraction.homotopy₂_comp_homotopy₂`: the three side conditions.
* `TauCeti.Contraction.normalize_incl` and `TauCeti.Contraction.normalize_proj`: normalization
  changes only the homotopy.
* `TauCeti.SpecialContraction.normalize_homotopy_eq`: normalization is a retraction, so it leaves
  an already special contraction unchanged.
* `TauCeti.Contraction.quasiIso_incl` and `TauCeti.Contraction.quasiIso_proj`: both structure maps
  of a contraction are quasi-isomorphisms.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 3, second bullet: "Package a strong
deformation retract of cochain complexes `(H,0) ⇄ (A,d)` by maps `i,p` of degree zero and `h` of
degree `-1`, with `p i = 1`, `1-i p = d h + h d`, and the side conditions `h i=0`, `p h=0`,
`h²=0` after the standard normalization.  Give a weaker contraction input and prove normalization
rather than requiring arbitrary callers to supply side conditions."  No formalization is vendored:
the cochain calculus is Mathlib's.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

@[expose] public section

open CategoryTheory Category Preadditive CochainComplex CochainComplex.HomComplex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

section CochainAux

variable {F G : CochainComplex C ℤ}

/-- The differential of the Hom complex, written through composition with the differential
cochains of the source and of the target: `δ z = z d + (-1)^(n+1) d z`. -/
theorem δ_eq_comp_diff_add_diff_comp (n m : ℤ) (hnm : n + 1 = m) (z : Cochain F G n) :
    δ n m z = z.comp (Cochain.diff G) (by lia) +
      m.negOnePow • (Cochain.diff F).comp z (by lia) := by
  ext p q hpq
  rw [δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl, Cochain.add_v,
    Cochain.comp_v z (Cochain.diff G) (by lia) p (q - 1) q (by lia) (by lia),
    Cochain.units_smul_v,
    Cochain.comp_v (Cochain.diff F) z (by lia) p (p + 1) q (by lia) (by lia),
    Cochain.diff_v, Cochain.diff_v]

/-- A morphism of cochain complexes commutes with the differential cochains. -/
theorem ofHom_comp_diff (φ : F ⟶ G) :
    (Cochain.ofHom φ).comp (Cochain.diff G) (zero_add 1) =
      (Cochain.diff F).comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.diff_v, Cochain.diff_v,
    Cochain.ofHom_v, Cochain.ofHom_v, φ.comm]

variable (F) in
/-- The differential cochain squares to zero. -/
@[simp]
theorem diff_comp_diff :
    (Cochain.diff F).comp (Cochain.diff F) (show (1 : ℤ) + 1 = 2 by lia) = 0 := by
  ext p q hpq
  rw [Cochain.comp_v (Cochain.diff F) (Cochain.diff F) (show (1 : ℤ) + 1 = 2 by lia)
      p (p + 1) q (by lia) (by lia),
    Cochain.diff_v, Cochain.diff_v, Cochain.zero_v, HomologicalComplex.d_comp_d]

end CochainAux

/-- A **contraction** of a cochain complex `K` onto a cochain complex `L`: an inclusion `incl`,
a projection `proj` retracting it, and a degree `-1` cochain contracting the identity of `K` onto
the resulting idempotent.  No side conditions are imposed; `TauCeti.Contraction.normalize`
supplies them. -/
structure Contraction (K L : CochainComplex C ℤ) where
  /-- the inclusion of the retract -/
  incl : L ⟶ K
  /-- the projection onto the retract -/
  proj : K ⟶ L
  /-- the contracting homotopy, a cochain of degree `-1` -/
  homotopy : Cochain K K (-1)
  /-- the projection retracts the inclusion -/
  incl_comp_proj : incl ≫ proj = 𝟙 L
  /-- `h d + d h` is the complementary idempotent `1 - i p` -/
  δ_homotopy : δ (-1) 0 homotopy = Cochain.ofHom (𝟙 K - proj ≫ incl)

/-- A **special contraction**, classically a strong deformation retract: a contraction whose
homotopy satisfies the three side conditions `h i = 0`, `p h = 0` and `h h = 0`. -/
structure SpecialContraction (K L : CochainComplex C ℤ) extends Contraction K L where
  /-- the homotopy annihilates the inclusion -/
  incl_comp_homotopy :
    (Cochain.ofHom incl).comp homotopy (show (0 : ℤ) + (-1) = -1 by lia) = 0
  /-- the projection annihilates the homotopy -/
  homotopy_comp_proj :
    homotopy.comp (Cochain.ofHom proj) (show (-1 : ℤ) + 0 = -1 by lia) = 0
  /-- the homotopy squares to zero -/
  homotopy_comp_homotopy : homotopy.comp homotopy (show (-1 : ℤ) + (-1) = -2 by lia) = 0

namespace Contraction

variable {K L : CochainComplex C ℤ} (c : Contraction K L)

/-- The idempotent endomorphism `i p` of `K` cut out by a contraction. -/
def idem : K ⟶ K := c.proj ≫ c.incl

/-- The complementary idempotent `1 - i p` of a contraction; it is the endomorphism which the
contracting homotopy trivializes. -/
def idemCompl : K ⟶ K := 𝟙 K - c.idem

theorem idem_eq : c.idem = c.proj ≫ c.incl := rfl

theorem idemCompl_eq : c.idemCompl = 𝟙 K - c.proj ≫ c.incl := rfl

/-- The contracting homotopy trivializes the complementary idempotent. -/
theorem δ_homotopy' : δ (-1) 0 c.homotopy = Cochain.ofHom c.idemCompl := c.δ_homotopy

@[simp] theorem incl_comp_idem : c.incl ≫ c.idem = c.incl := by
  rw [idem_eq c, ← assoc, c.incl_comp_proj, id_comp]

@[simp] theorem idem_comp_proj : c.idem ≫ c.proj = c.proj := by
  rw [idem_eq c, assoc, c.incl_comp_proj, comp_id]

@[simp] theorem idem_comp_idem : c.idem ≫ c.idem = c.idem := by
  rw [idem_eq c, assoc, ← assoc c.incl, c.incl_comp_proj, id_comp]

@[simp] theorem incl_comp_idemCompl : c.incl ≫ c.idemCompl = 0 := by
  rw [idemCompl_eq c, comp_sub, comp_id, ← assoc, c.incl_comp_proj, id_comp, sub_self]

@[simp] theorem idemCompl_comp_proj : c.idemCompl ≫ c.proj = 0 := by
  rw [idemCompl_eq c, sub_comp, id_comp, assoc, c.incl_comp_proj, comp_id, sub_self]

@[simp] theorem idemCompl_comp_idemCompl : c.idemCompl ≫ c.idemCompl = c.idemCompl := by
  rw [idemCompl_eq c, sub_comp, id_comp, comp_sub, comp_id, ← idem_eq c, c.idem_comp_idem,
    sub_self, sub_zero]

section Step1

/-- The first normalization step, `h₁ = Ψ h Ψ` with `Ψ = 1 - i p`.  It is still a contracting
homotopy, and it satisfies the two annihilation conditions `h₁ i = 0` and `p h₁ = 0`. -/
def homotopy₁ : Cochain K K (-1) :=
  (Cochain.ofHom c.idemCompl).comp
    (c.homotopy.comp (Cochain.ofHom c.idemCompl) (show (-1 : ℤ) + 0 = -1 by lia))
    (show (0 : ℤ) + (-1) = -1 by lia)

@[simp] theorem idemCompl_comp_homotopy₁ :
    (Cochain.ofHom c.idemCompl).comp c.homotopy₁ (show (0 : ℤ) + (-1) = -1 by lia) =
      c.homotopy₁ := by
  rw [homotopy₁, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    c.idemCompl_comp_idemCompl]

@[simp] theorem homotopy₁_comp_idemCompl :
    c.homotopy₁.comp (Cochain.ofHom c.idemCompl) (show (-1 : ℤ) + 0 = -1 by lia) =
      c.homotopy₁ := by
  rw [homotopy₁, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, c.idemCompl_comp_idemCompl]

@[simp] theorem incl_comp_homotopy₁ :
    (Cochain.ofHom c.incl).comp c.homotopy₁ (show (0 : ℤ) + (-1) = -1 by lia) = 0 := by
  rw [homotopy₁, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    c.incl_comp_idemCompl, Cochain.ofHom_zero, Cochain.zero_comp]

@[simp] theorem homotopy₁_comp_proj :
    c.homotopy₁.comp (Cochain.ofHom c.proj) (show (-1 : ℤ) + 0 = -1 by lia) = 0 := by
  rw [homotopy₁, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, c.idemCompl_comp_proj,
    Cochain.ofHom_zero, Cochain.comp_zero, Cochain.comp_zero]

/-- The first normalization step preserves the contracting homotopy property. -/
@[simp] theorem δ_homotopy₁ : δ (-1) 0 c.homotopy₁ = Cochain.ofHom c.idemCompl := by
  have hψ : δ 0 1 (Cochain.ofHom c.idemCompl) = 0 := δ_ofHom _
  rw [homotopy₁, δ_zero_cochain_comp _ _ 0 (by lia), hψ, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp_zero_cochain _ _ 0 (by lia), hψ, Cochain.comp_zero, zero_add, c.δ_homotopy',
    ← Cochain.ofHom_comp, c.idemCompl_comp_idemCompl, ← Cochain.ofHom_comp,
    c.idemCompl_comp_idemCompl]

/-- Composing the once-normalized homotopy with the differential on the right. -/
theorem homotopy₁_comp_diff :
    c.homotopy₁.comp (Cochain.diff K) (show (-1 : ℤ) + 1 = 0 by lia) =
      Cochain.ofHom c.idemCompl -
        (Cochain.diff K).comp c.homotopy₁ (show (1 : ℤ) + (-1) = 0 by lia) := by
  have h := c.δ_homotopy₁
  rw [δ_eq_comp_diff_add_diff_comp (-1) 0 (by lia)] at h
  simp only [Int.negOnePow_zero, one_smul] at h
  rw [← h]
  abel

end Step1

section Step2

/-- The square of the once-normalized homotopy, a cochain of degree `-2`.  It is a cocycle, hence
commutes with the differential, and this is what makes the second normalization step square to
zero. -/
def homotopySq : Cochain K K (-2) :=
  c.homotopy₁.comp c.homotopy₁ (show (-1 : ℤ) + (-1) = -2 by lia)

/-- The square of the once-normalized homotopy is a cocycle. -/
@[simp] theorem δ_homotopySq : δ (-2) (-1) c.homotopySq = 0 := by
  rw [homotopySq, δ_comp c.homotopy₁ c.homotopy₁ (show (-1 : ℤ) + (-1) = -2 by lia)
      0 0 (-1) (by lia) (by lia) (by lia),
    c.δ_homotopy₁, c.homotopy₁_comp_idemCompl, c.idemCompl_comp_homotopy₁]
  simp

/-- The square of the once-normalized homotopy commutes with the differential. -/
theorem homotopySq_comp_diff :
    c.homotopySq.comp (Cochain.diff K) (show (-2 : ℤ) + 1 = -1 by lia) =
      (Cochain.diff K).comp c.homotopySq (show (1 : ℤ) + (-2) = -1 by lia) := by
  have h := c.δ_homotopySq
  rw [δ_eq_comp_diff_add_diff_comp (-2) (-1) (by lia)] at h
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul] at h
  rwa [← sub_eq_add_neg, sub_eq_zero] at h

/-- The second normalization step, the classical product `h₂ = h₁ d h₁`. -/
def homotopy₂ : Cochain K K (-1) :=
  c.homotopy₁.comp ((Cochain.diff K).comp c.homotopy₁ (show (1 : ℤ) + (-1) = 0 by lia))
    (show (-1 : ℤ) + 0 = -1 by lia)

/-- The second normalization step, written so that the correction to `h₁` is visibly a
`δ`-cocycle multiplied by the differential. -/
theorem homotopy₂_eq_sub :
    c.homotopy₂ =
      c.homotopy₁ -
        (Cochain.diff K).comp c.homotopySq (show (1 : ℤ) + (-2) = -1 by lia) := by
  rw [homotopy₂,
    ← Cochain.comp_assoc c.homotopy₁ (Cochain.diff K) c.homotopy₁
      (show (-1 : ℤ) + 1 = 0 by lia) (show (1 : ℤ) + (-1) = 0 by lia) (by lia),
    c.homotopy₁_comp_diff, Cochain.sub_comp, c.idemCompl_comp_homotopy₁,
    Cochain.comp_assoc (Cochain.diff K) c.homotopy₁ c.homotopy₁
      (show (1 : ℤ) + (-1) = 0 by lia) (show (-1 : ℤ) + (-1) = -2 by lia) (by lia),
    homotopySq]

/-- The second normalization step preserves the contracting homotopy property: the correction is
the differential composed with a cocycle, so it is annihilated by `δ`. -/
@[simp] theorem δ_homotopy₂ : δ (-1) 0 c.homotopy₂ = Cochain.ofHom c.idemCompl := by
  have hd : δ 1 2 (Cochain.diff K) = 0 := by simpa using (Cocycle.diff K).δ_eq_zero 2
  rw [homotopy₂_eq_sub, δ_sub,
    δ_comp (Cochain.diff K) c.homotopySq (show (1 : ℤ) + (-2) = -1 by lia)
      2 (-1) 0 (by lia) (by lia) (by lia),
    c.δ_homotopySq, hd, Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero, sub_zero,
    c.δ_homotopy₁]

@[simp] theorem incl_comp_homotopy₂ :
    (Cochain.ofHom c.incl).comp c.homotopy₂ (show (0 : ℤ) + (-1) = -1 by lia) = 0 := by
  rw [homotopy₂, ← Cochain.comp_assoc_of_first_is_zero_cochain, c.incl_comp_homotopy₁,
    Cochain.zero_comp]

@[simp] theorem homotopy₂_comp_proj :
    c.homotopy₂.comp (Cochain.ofHom c.proj) (show (-1 : ℤ) + 0 = -1 by lia) = 0 := by
  rw [homotopy₂, Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, c.homotopy₁_comp_proj, Cochain.comp_zero,
    Cochain.comp_zero]

/-- The second normalization step squares to zero. -/
@[simp] theorem homotopy₂_comp_homotopy₂ :
    c.homotopy₂.comp c.homotopy₂ (show (-1 : ℤ) + (-1) = -2 by lia) = 0 := by
  have key : (Cochain.diff K).comp
      (c.homotopySq.comp (Cochain.diff K) (show (-2 : ℤ) + 1 = -1 by lia))
      (show (1 : ℤ) + (-1) = 0 by lia) = 0 := by
    rw [c.homotopySq_comp_diff,
      ← Cochain.comp_assoc (Cochain.diff K) (Cochain.diff K) c.homotopySq
        (show (1 : ℤ) + 1 = 2 by lia) (show (1 : ℤ) + (-2) = -1 by lia) (by lia),
      diff_comp_diff, Cochain.zero_comp]
  have step : c.homotopy₁.comp c.homotopy₂ (show (-1 : ℤ) + (-1) = -2 by lia) =
      (c.homotopySq.comp (Cochain.diff K) (show (-2 : ℤ) + 1 = -1 by lia)).comp c.homotopy₁
        (show (-1 : ℤ) + (-1) = -2 by lia) := by
    rw [homotopy₂,
      ← Cochain.comp_assoc c.homotopy₁ c.homotopy₁
        ((Cochain.diff K).comp c.homotopy₁ (show (1 : ℤ) + (-1) = 0 by lia))
        (show (-1 : ℤ) + (-1) = -2 by lia) (show (-1 : ℤ) + 0 = -1 by lia) (by lia),
      ← homotopySq,
      ← Cochain.comp_assoc c.homotopySq (Cochain.diff K) c.homotopy₁
        (show (-2 : ℤ) + 1 = -1 by lia) (show (1 : ℤ) + (-1) = 0 by lia) (by lia)]
  nth_rewrite 1 [homotopy₂]
  rw [Cochain.comp_assoc c.homotopy₁
      ((Cochain.diff K).comp c.homotopy₁ (show (1 : ℤ) + (-1) = 0 by lia)) c.homotopy₂
      (show (-1 : ℤ) + 0 = -1 by lia) (show (0 : ℤ) + (-1) = -1 by lia) (by lia),
    Cochain.comp_assoc (Cochain.diff K) c.homotopy₁ c.homotopy₂
      (show (1 : ℤ) + (-1) = 0 by lia) (show (-1 : ℤ) + (-1) = -2 by lia) (by lia),
    step,
    ← Cochain.comp_assoc (Cochain.diff K)
      (c.homotopySq.comp (Cochain.diff K) (show (-2 : ℤ) + 1 = -1 by lia)) c.homotopy₁
      (show (1 : ℤ) + (-1) = 0 by lia) (show (-1 : ℤ) + (-1) = -2 by lia) (by lia),
    key, Cochain.zero_comp, Cochain.comp_zero]

end Step2

/-- **Normalization of a contraction.**  Every contraction of cochain complexes can be replaced,
without changing its inclusion or its projection, by one satisfying the three side conditions
`h i = 0`, `p h = 0` and `h h = 0`. -/
def normalize : SpecialContraction K L where
  incl := c.incl
  proj := c.proj
  homotopy := c.homotopy₂
  incl_comp_proj := c.incl_comp_proj
  δ_homotopy := c.δ_homotopy₂
  incl_comp_homotopy := c.incl_comp_homotopy₂
  homotopy_comp_proj := c.homotopy₂_comp_proj
  homotopy_comp_homotopy := c.homotopy₂_comp_homotopy₂

@[simp] theorem normalize_incl : c.normalize.incl = c.incl := rfl

@[simp] theorem normalize_proj : c.normalize.proj = c.proj := rfl

@[simp] theorem normalize_homotopy : c.normalize.homotopy = c.homotopy₂ := rfl

section HomotopyEquivalence

/-- The homotopy from the idempotent `i p` to the identity of `K` given by a contraction. -/
noncomputable def homotopyIdemId : Homotopy c.idem (𝟙 K) :=
  (Cochain.equivHomotopy _ _).symm ⟨-c.homotopy, by
    rw [δ_neg, c.δ_homotopy', idemCompl_eq, Cochain.ofHom_sub, idem_eq]
    abel⟩

/-- A contraction exhibits `L` as homotopy equivalent to `K`. -/
noncomputable def homotopyEquiv : HomotopyEquiv L K where
  hom := c.incl
  inv := c.proj
  homotopyHomInvId := Homotopy.ofEq c.incl_comp_proj
  homotopyInvHomId := c.homotopyIdemId

@[simp] theorem homotopyEquiv_hom : c.homotopyEquiv.hom = c.incl := rfl

@[simp] theorem homotopyEquiv_inv : c.homotopyEquiv.inv = c.proj := rfl

variable [∀ n, K.HasHomology n] [∀ n, L.HasHomology n]

/-- The inclusion of a contraction is a quasi-isomorphism. -/
theorem quasiIso_incl : QuasiIso c.incl := c.homotopyEquiv.quasiIso_hom

/-- The projection of a contraction is a quasi-isomorphism. -/
theorem quasiIso_proj : QuasiIso c.proj := c.homotopyEquiv.quasiIso_inv

end HomotopyEquivalence

end Contraction

namespace SpecialContraction

variable {K L : CochainComplex C ℤ} (s : SpecialContraction K L)

/-- In a special contraction the complementary idempotent acts as the identity on the homotopy
from the left, because `h i = 0`. -/
@[simp] theorem idemCompl_comp_homotopy :
    (Cochain.ofHom s.toContraction.idemCompl).comp s.homotopy
      (show (0 : ℤ) + (-1) = -1 by lia) = s.homotopy := by
  rw [Contraction.idemCompl_eq, Cochain.ofHom_sub, Cochain.sub_comp, Cochain.id_comp,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, s.incl_comp_homotopy,
    Cochain.comp_zero, sub_zero]

/-- In a special contraction the complementary idempotent acts as the identity on the homotopy
from the right, because `p h = 0`. -/
@[simp] theorem homotopy_comp_idemCompl :
    s.homotopy.comp (Cochain.ofHom s.toContraction.idemCompl)
      (show (-1 : ℤ) + 0 = -1 by lia) = s.homotopy := by
  rw [Contraction.idemCompl_eq, Cochain.ofHom_sub, Cochain.comp_sub, Cochain.comp_id,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain, s.homotopy_comp_proj,
    Cochain.zero_comp, sub_zero]

/-- The first normalization step does nothing to a special contraction. -/
@[simp] theorem homotopy₁_eq : s.toContraction.homotopy₁ = s.homotopy := by
  rw [Contraction.homotopy₁, s.homotopy_comp_idemCompl, s.idemCompl_comp_homotopy]

@[simp] theorem homotopySq_eq_zero : s.toContraction.homotopySq = 0 := by
  rw [Contraction.homotopySq, s.homotopy₁_eq, s.homotopy_comp_homotopy]

/-- The second normalization step does nothing to a special contraction either. -/
@[simp] theorem homotopy₂_eq : s.toContraction.homotopy₂ = s.homotopy := by
  rw [Contraction.homotopy₂_eq_sub, s.homotopy₁_eq, s.homotopySq_eq_zero, Cochain.comp_zero,
    sub_zero]

/-- Normalization is a retraction: it leaves an already special contraction unchanged.  In
particular normalizing twice is the same as normalizing once. -/
theorem normalize_homotopy_eq : s.toContraction.normalize.homotopy = s.homotopy :=
  s.homotopy₂_eq

/-- Every cochain complex is a special contraction of itself, with zero homotopy.  This pins the
orientation of the contracting equation: it has `1 - i p` on the right, so the identity
contraction has vanishing homotopy. -/
def refl (K : CochainComplex C ℤ) : SpecialContraction K K where
  incl := 𝟙 K
  proj := 𝟙 K
  homotopy := 0
  incl_comp_proj := by simp
  δ_homotopy := by simp
  incl_comp_homotopy := by simp
  homotopy_comp_proj := by simp
  homotopy_comp_homotopy := by simp

@[simp] theorem refl_incl (K : CochainComplex C ℤ) : (refl K).incl = 𝟙 K := rfl

@[simp] theorem refl_proj (K : CochainComplex C ℤ) : (refl K).proj = 𝟙 K := rfl

@[simp] theorem refl_homotopy (K : CochainComplex C ℤ) : (refl K).homotopy = 0 := rfl

end SpecialContraction

end TauCeti
