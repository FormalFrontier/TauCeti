/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Analytic continuation along a concatenation of paths

`Continuation/Basic.lean` carries a holomorphic germ along a single path and proves that the
result is determined by the initial germ. This file supplies the other half of the basic calculus
of analytic continuation: continuing along `γ` and then along `δ` is continuing along the
concatenated path `γ.trans δ`, and conversely a continuation along a concatenation restricts to
one along each factor.

## The gluing engine

Both directions run on general facts about `TauCeti.IsAnalyticContinuationAlong`, stated for an
arbitrary parameter space in `Continuation/Basic.lean` and consumed here:

* only the values of the path on the parameter set matter
  (`TauCeti.IsAnalyticContinuationAlong.congr_path`);
* one family of germs that continues over each of two **closed** parameter sets continues over
  their union (`TauCeti.IsAnalyticContinuationAlong.union`) — closedness being what makes the
  gluing true rather than a convenience, since the locality condition over a parameter set is
  vacuous outside its closure.

The restriction direction needs no gluing at all: reading `γ` as the first half of `γ.trans δ` is
a reparametrisation, and `TauCeti.IsAnalyticContinuationAlong.reparam` already transports a
continuation along any reparametrisation.

## The concatenated family

The family of germs carried along `γ.trans δ` is written down explicitly, as
`TauCeti.transFamily`: on the first half of the parameter interval it is the family carried along
`γ`, read at twice the parameter, and on the second half the one carried along `δ`. Assembling two
families indexed by the unit interval into one is pure reparametrisation, so `TauCeti.transFamily`
carries values in an arbitrary sort and is specialised to germs only where continuations are
concatenated. The two halves are compared at the junction, where `TauCeti.transFamily` takes the
value coming from `γ`; the hypothesis of `TauCeti.IsAnalyticContinuationAlong.trans` is exactly
that the germ `γ` delivers there agrees with the germ `δ` starts from.

## Moving the base point

The pay-off is that continuability inside a domain does not depend on the base point:
`TauCeti.continuesInside_of_isAnalyticContinuationAlong` says that if a germ continues inside `U`
from `z₀` — the hypothesis the monodromy theorem for a simply connected domain runs on
(`Conformal/GlobalBranch.lean`) — and is continued along a path inside `U` to a germ at `z₁`, then
that germ continues inside `U` from `z₁`. Concatenation supplies the paths issuing from `z₁`, and
restriction plus uniqueness of continuation along a fixed path identify the germ reached halfway.

Transport is in fact an equivalence, `TauCeti.continuesInside_iff_of_isAnalyticContinuationAlong`:
the reversed path `p.symm` carries the germ back, the family read backwards being a continuation
along it by `TauCeti.IsAnalyticContinuationAlong.reparam`. So no endpoint of the path is
distinguished — continuability inside `U` is a property of the domain and of the branch being
carried, and any point the branch reaches may serve as its base point.

## Main results

* `TauCeti.transFamily` — the family of germs carried along a concatenation.
* `TauCeti.IsAnalyticContinuationAlong.trans` — **continuations concatenate**: two continuations
  whose germs match at the junction assemble into a continuation along `γ.trans δ`.
* `TauCeti.continuesAlong_trans` — the germ-level form: a germ that continues along `γ` to a germ
  that continues along `δ` continues along `γ.trans δ`.
* `TauCeti.IsAnalyticContinuationAlong.left_of_trans`, `.right_of_trans` — **continuations
  restrict**: a continuation along `γ.trans δ` reads as a continuation along `γ` and one
  along `δ`.
* `TauCeti.ContinuesAlong.left_of_trans` — the germ-level form of the first of those: a germ
  that continues along `γ.trans δ` continues along `γ`.
* `TauCeti.continuesInside_of_isAnalyticContinuationAlong` — **continuability inside a domain
  travels with the germ**: continuing inside `U` along a path of `U` again continues inside `U`.
* `TauCeti.continuesInside_iff_of_isAnalyticContinuationAlong` — the equivalence: the two germs at
  the ends of such a path continue inside `U` together, or neither does.

## Generality

Germs of maps `ℂ → E` into a complex Banach space, as in `Continuation/Basic.lean`, where the
choice is discussed; the conformal-mapping consumers instantiate `E = ℂ`. `TauCeti.transFamily` is
pure reparametrisation and is stated for values in an arbitrary sort, and the two restriction
lemmas need no completeness, being reparametrisations as well.

## Coordination with upstream Mathlib

This is basic API for layer **L4** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), analytic continuation and the reflection
principle. Mathlib has no analytic continuation along a path, and L4 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. So
nothing here is a shim under the roadmap's shim-deletion clause, which covers L0–L3 only. The
`Path.trans` concatenation and its `Path.extend` calculus are consumed from Mathlib rather than
rebuilt.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval

/-! ### The family carried along a concatenation -/

section TransFamily

variable {Y : Sort*}

/-- The family carried along a concatenation `γ.trans δ` of paths, assembled from the family `F`
carried along `γ` and the family `G` carried along `δ`: on the first half of the parameter interval
it is `F`, read at twice the parameter, and on the second half it is `G`, read at twice the
parameter minus one. The junction time `1 / 2` is assigned the value coming from `F`, matching the
convention of `Path.trans`.

Assembling the two halves is pure reparametrisation of the unit interval, so the values are
allowed to lie in an arbitrary sort; the case of interest is `Y = ℂ → E`, where `F` and `G` are
families of germs (`TauCeti.IsAnalyticContinuationAlong.trans`). -/
noncomputable def transFamily (F G : I → Y) (u : I) : Y :=
  if (u : ℝ) ≤ 2⁻¹ then F (projIcc 0 1 zero_le_one (2 * u))
  else G (projIcc 0 1 zero_le_one (2 * u - 1))

/-- On the first half of the parameter interval the concatenated family is the first family. -/
@[simp]
theorem transFamily_of_le_half (F G : I → Y) {u : I} (hu : (u : ℝ) ≤ 2⁻¹) :
    transFamily F G u = F (projIcc 0 1 zero_le_one (2 * u)) :=
  ite_eq_left hu

/-- Strictly past the junction the concatenated family is the second family. -/
@[simp]
theorem transFamily_of_half_lt (F G : I → Y) {u : I} (hu : 2⁻¹ < (u : ℝ)) :
    transFamily F G u = G (projIcc 0 1 zero_le_one (2 * u - 1)) :=
  ite_eq_right (not_le.mpr hu)

/-- At parameter time `0` the concatenated family is the initial value of the first family:
a concatenation starts where its first factor starts.

Not itself a `simp` lemma: `simp` already reaches this normal form through
`TauCeti.transFamily_of_le_half`, whose bound it discharges at `0`. -/
theorem transFamily_zero (F G : I → Y) : transFamily F G 0 = F 0 := by
  rw [transFamily_of_le_half F G (by norm_num)]
  congr 1
  ext
  norm_num [coe_projIcc]

/-- At parameter time `1` the concatenated family is the terminal value of the second family:
a concatenation ends where its second factor ends. -/
@[simp]
theorem transFamily_one (F G : I → Y) : transFamily F G 1 = G 1 := by
  rw [transFamily_of_half_lt F G (by norm_num)]
  congr 1
  ext
  norm_num [coe_projIcc]

end TransFamily

/-! ### Concatenating continuations -/

section Trans

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a b c : ℂ} {f₀ : ℂ → E} {F G : I → ℂ → E}

/-- **A concatenation restricted to a half is a reparametrisation of that half.** Wherever the
extended concatenation agrees with `r.extend ∘ ψ` and `ψ` lands in `[0, 1]`, the concatenation
itself agrees with `r` read at `projIcc ∘ ψ`.

Both halves of `TauCeti.IsAnalyticContinuationAlong.trans` are this statement: the first for
`r = p`, `ψ u = 2u` on `{u ≤ 2⁻¹}`, the second for `r = q`, `ψ u = 2u - 1` on `{2⁻¹ ≤ u}`. The
`Path.extend_trans_of_le_half` / `Path.extend_trans_of_half_le` step is what each supplies as
`hext`. -/
private theorem eqOn_trans_comp_projIcc {X : Type*} [TopologicalSpace X] {x y z x' y' : X}
    {r : Path x' y'} {p : Path x y} {q : Path y z}
    {ψ : I → ℝ} {s : Set I} (hmem : ∀ u ∈ s, ψ u ∈ Icc (0 : ℝ) 1)
    (hext : ∀ u ∈ s, (p.trans q).extend u = r.extend (ψ u)) :
    EqOn (⇑(p.trans q)) ((⇑r) ∘ fun u : I => projIcc (0 : ℝ) 1 zero_le_one (ψ u)) s := by
  intro u hu
  calc (p.trans q) u
      = (p.trans q).extend (u : ℝ) := ((p.trans q).extend_extends' u).symm
    _ = r.extend (ψ u) := hext u hu
    _ = r.extend ((projIcc (0 : ℝ) 1 zero_le_one (ψ u) : I) : ℝ) := by
          rw [projIcc_of_mem _ (hmem u hu)]
    _ = r (projIcc (0 : ℝ) 1 zero_le_one (ψ u)) := r.extend_extends' _

/-- The first half of `p.trans q` is `p` reparametrised by doubling, so `transFamily F G`
continues along `p.trans q` on `{u | u ≤ 2⁻¹}`. -/
private theorem isAnalyticContinuationAlong_transFamily_Iic [CompleteSpace E] {p : Path a b}
    {q : Path b c} (hF : IsAnalyticContinuationAlong F (⇑p) univ) :
    IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q)) {u : I | (u : ℝ) ≤ 2⁻¹} := by
  have hφ₁ : Continuous fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u) :=
    continuous_projIcc.comp (by fun_prop)
  have h₁ := hF.reparam (φ := fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u))
    (s' := {u : I | (u : ℝ) ≤ 2⁻¹}) hφ₁.continuousOn (mapsTo_univ _ _)
  have hpath₁ : EqOn (⇑(p.trans q))
      ((⇑p) ∘ fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u))
      {u : I | (u : ℝ) ≤ 2⁻¹} :=
    eqOn_trans_comp_projIcc
      (fun u hu => have hu' : (u : ℝ) ≤ 2⁻¹ := hu
        ⟨by linarith [u.2.1], by linarith⟩)
      (fun u hu => have hu' : (u : ℝ) ≤ 2⁻¹ := hu
        Path.extend_trans_of_le_half p q (by rw [one_div]; exact hu'))
  exact (h₁.congr_path hpath₁).congr fun u hu => by
    rw [transFamily_of_le_half F G hu]
    exact .rfl

/-- The second half of `p.trans q` is `q` reparametrised by doubling and shifting, so
`transFamily F G` continues along `p.trans q` on `{u | 2⁻¹ ≤ u}`. At the midpoint the two halves
are reconciled by the matching hypothesis `hFG`. -/
private theorem isAnalyticContinuationAlong_transFamily_Ici [CompleteSpace E] {p : Path a b}
    {q : Path b c} (hG : IsAnalyticContinuationAlong G (⇑q) univ) (hFG : F 1 =ᶠ[𝓝 b] G 0) :
    IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q)) {u : I | 2⁻¹ ≤ (u : ℝ)} := by
  have hφ₂ : Continuous fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1) :=
    continuous_projIcc.comp (by fun_prop)
  have h₂ := hG.reparam (φ := fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1))
    (s' := {u : I | 2⁻¹ ≤ (u : ℝ)}) hφ₂.continuousOn (mapsTo_univ _ _)
  have hpath₂ : EqOn (⇑(p.trans q))
      ((⇑q) ∘ fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1))
      {u : I | 2⁻¹ ≤ (u : ℝ)} :=
    eqOn_trans_comp_projIcc
      (fun u hu => have hu' : 2⁻¹ ≤ (u : ℝ) := hu
        ⟨by linarith, by linarith [u.2.2]⟩)
      (fun u hu => have hu' : 2⁻¹ ≤ (u : ℝ) := hu
        Path.extend_trans_of_half_le p q (by rw [one_div]; exact hu'))
  refine (h₂.congr_path hpath₂).congr fun u hu => ?_
  have hu' : 2⁻¹ ≤ (u : ℝ) := hu
  rcases eq_or_lt_of_le hu' with heq | hlt
  · have e₁ : projIcc (0 : ℝ) 1 zero_le_one (2 * u) = 1 := by norm_num [← heq]
    have e₀ : projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1) = 0 := by norm_num [← heq]
    have hpt : (p.trans q) u = b := by rw [hpath₂ hu]; simp [e₀]
    rw [transFamily_of_le_half F G heq.ge, e₁, hpt]
    simpa [e₀] using hFG
  · rw [transFamily_of_half_lt F G hlt]
    exact .rfl

/-- **Continuations concatenate.** If `F` continues a germ along `p`, `G` continues a germ along
`q`, and the germ `F` delivers at the end of `p` is the germ `G` starts from, then
`TauCeti.transFamily F G` is a continuation along the concatenated path `p.trans q`.

Its germ at parameter time `0` is that of `F 0` and its germ at time `1` is that of `G 1`
(`TauCeti.transFamily_zero`, `TauCeti.transFamily_one`), so continuing along `p` and then along
`q` carries the initial germ of `F` to the terminal germ of `G`. -/
theorem IsAnalyticContinuationAlong.trans [CompleteSpace E] {p : Path a b} {q : Path b c}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ)
    (hG : IsAnalyticContinuationAlong G (⇑q) univ) (hFG : F 1 =ᶠ[𝓝 b] G 0) :
    IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q)) univ := by
  -- The halves are the `Iic`/`Ici` pair at the midpoint: `I` carries the order induced from `ℝ`,
  -- so the set-builder literals in the two halves are definitionally those intervals.
  rw [← Iic_union_Ici (a := (⟨2⁻¹, by norm_num⟩ : I))]
  exact (isAnalyticContinuationAlong_transFamily_Iic hF).union
    (isAnalyticContinuationAlong_transFamily_Ici hG hFG)
    (isClosed_Iic (a := (⟨2⁻¹, by norm_num⟩ : I))) (isClosed_Ici (a := (⟨2⁻¹, by norm_num⟩ : I)))

/-- **Continuability is transitive along a concatenation.** If `F` continues the germ of `f₀`
along `p`, and the germ `F 1` it delivers at the end of `p` continues along `q`, then `f₀`
continues along `p.trans q`. -/
theorem continuesAlong_trans [CompleteSpace E] {p : Path a b} {q : Path b c}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) (hF0 : F 0 =ᶠ[𝓝 a] f₀)
    (hq : ContinuesAlong (F 1) (⇑q)) : ContinuesAlong f₀ (⇑(p.trans q)) := by
  obtain ⟨G, hG, hG0⟩ := continuesAlong_iff_exists.mp hq
  rw [q.source] at hG0
  refine continuesAlong_iff_exists.mpr ⟨transFamily F G, hF.trans hG hG0.symm, ?_⟩
  rw [transFamily_zero, (p.trans q).source]
  exact hF0

/-! ### Restricting a continuation to the factors of a concatenation -/

/-- **A continuation along a concatenation restricts to its first factor.** Reading a continuation
along `p.trans q` on the first half of the parameter interval — that is, precomposing with the
halving map `t ↦ t / 2` — gives a continuation along `p`.

This is the converse of `TauCeti.IsAnalyticContinuationAlong.trans`, and needs no gluing: the
first half of `p.trans q` is `p` reparametrised, so
`TauCeti.IsAnalyticContinuationAlong.reparam` transports the continuation. -/
theorem IsAnalyticContinuationAlong.left_of_trans {H : I → ℂ → E} {p : Path a b}
    {q : Path b c} (h : IsAnalyticContinuationAlong H (⇑(p.trans q)) univ) :
    IsAnalyticContinuationAlong (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2)))
      (⇑p) univ := by
  have hψ : Continuous fun t : I => projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2) :=
    continuous_projIcc.comp (by fun_prop)
  refine (h.reparam (φ := fun t : I => projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2))
    (s' := univ) hψ.continuousOn (mapsTo_univ _ _)).congr_path fun t _ => ?_
  have ht : (t : ℝ) / 2 ≤ 1 / 2 := by linarith [t.2.2]
  have hmem : (t : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [t.2.1], by linarith⟩
  calc (p : I → ℂ) t
      = p.extend (t : ℝ) := (p.extend_extends' t).symm
    _ = p.extend (2 * ((t : ℝ) / 2)) := by ring_nf
    _ = (p.trans q).extend ((t : ℝ) / 2) := (Path.extend_trans_of_le_half p q ht).symm
    _ = (p.trans q).extend ((projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2) : I) : ℝ) := by
          rw [projIcc_of_mem _ hmem]
    _ = (p.trans q) (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2)) := (p.trans q).extend_extends' _

/-- **A continuation along a concatenation restricts to its second factor.** Reading a continuation
along `p.trans q` on the second half of the parameter interval — that is, precomposing with
`t ↦ (t + 1) / 2` — gives a continuation along `q`. -/
theorem IsAnalyticContinuationAlong.right_of_trans {H : I → ℂ → E} {p : Path a b}
    {q : Path b c} (h : IsAnalyticContinuationAlong H (⇑(p.trans q)) univ) :
    IsAnalyticContinuationAlong
      (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2))) (⇑q) univ := by
  have hψ : Continuous fun t : I => projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2) :=
    continuous_projIcc.comp (by fun_prop)
  refine (h.reparam (φ := fun t : I => projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2))
    (s' := univ) hψ.continuousOn (mapsTo_univ _ _)).congr_path fun t _ => ?_
  have ht : 1 / 2 ≤ ((t : ℝ) + 1) / 2 := by linarith [t.2.1]
  have hmem : ((t : ℝ) + 1) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [t.2.2]⟩
  calc (q : I → ℂ) t
      = q.extend (t : ℝ) := (q.extend_extends' t).symm
    _ = q.extend (2 * (((t : ℝ) + 1) / 2) - 1) := by ring_nf
    _ = (p.trans q).extend (((t : ℝ) + 1) / 2) := (Path.extend_trans_of_half_le p q ht).symm
    _ = (p.trans q).extend ((projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2) : I) : ℝ) := by
          rw [projIcc_of_mem _ hmem]
    _ = (p.trans q) (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2)) :=
          (p.trans q).extend_extends' _

/-- **Continuability restricts to the first factor of a concatenation.** A germ that continues
along `p.trans q` continues along `p`: the germ-level converse of
`TauCeti.continuesAlong_trans`, obtained by restricting a witness with
`TauCeti.IsAnalyticContinuationAlong.left_of_trans`.

There is no companion for the second factor at this level: `q` issues from the endpoint of `p`,
so the germ it continues is the one reached at the junction, which
`TauCeti.ContinuesAlong` does not name. Use
`TauCeti.IsAnalyticContinuationAlong.right_of_trans` on a witness instead. -/
theorem ContinuesAlong.left_of_trans {p : Path a b} {q : Path b c}
    (h : ContinuesAlong f₀ (⇑(p.trans q))) : ContinuesAlong f₀ (⇑p) := by
  obtain ⟨H, hH, hH0⟩ := continuesAlong_iff_exists.mp h
  rw [(p.trans q).source] at hH0
  refine continuesAlong_iff_exists.mpr
    ⟨fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2)), hH.left_of_trans, ?_⟩
  have hzero : projIcc (0 : ℝ) 1 zero_le_one (((0 : I) : ℝ) / 2) = 0 := by
    ext; norm_num [coe_projIcc]
  simp only [hzero]
  rw [p.source]
  exact hH0

/-! ### Continuability inside a domain travels with the germ -/

/-- **Continuability inside a domain does not depend on the base point.** If the germ of `f₀` at
`z₀` continues inside `U`, and `F` continues it along a path `p` from `z₀` to `z₁` that stays in
`U`, then the germ `F 1` delivered at `z₁` continues inside `U` in its own right.

So `TauCeti.ContinuesInside`, the hypothesis of the monodromy theorem for a simply connected
domain, is a condition on the domain and on the branch being carried, not on the point one starts
from: a path issuing from `z₁` is continued by prefixing `p` to it, and uniqueness of continuation
along `p` identifies the germ reached halfway with `F 1`. -/
theorem continuesInside_of_isAnalyticContinuationAlong [CompleteSpace E] {U : Set ℂ} {z₀ z₁ : ℂ}
    (H : ContinuesInside f₀ U z₀) {p : Path z₀ z₁} (hpU : ∀ t, p t ∈ U)
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) (hF0 : F 0 =ᶠ[𝓝 z₀] f₀) :
    ContinuesInside (F 1) U z₁ := by
  refine ContinuesInside.of_forall fun d hd hdU hd0 => ?_
  obtain ⟨e, q, rfl⟩ : ∃ (e : ℂ) (q : Path z₁ e), (⇑q : I → ℂ) = d :=
    ⟨d 1, ⟨⟨d, hd⟩, hd0, rfl⟩, rfl⟩
  have hpq : ∀ t, (p.trans q) t ∈ U := by
    intro t
    have hmem : (p.trans q) t ∈ range (p.trans q) := mem_range_self t
    rw [Path.trans_range] at hmem
    rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact hpU s
    · rw [← hs]; exact hdU s
  obtain ⟨K, hK, hK0⟩ := continuesAlong_iff_exists.mp
    (H.continuesAlong (p.trans q).continuous hpq (p.trans q).source)
  rw [(p.trans q).source] at hK0
  -- The first factor: the germ reached at the junction is the one `F` delivers.
  have hleft := hK.left_of_trans
  have hzero : projIcc (0 : ℝ) 1 zero_le_one (((0 : I) : ℝ) / 2) = 0 := by
    ext; norm_num [coe_projIcc]
  have hstart : (fun t : I => K (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2))) 0
      =ᶠ[𝓝 (p 0)] F 0 := by
    simp only [hzero]
    rw [p.source]
    exact hK0.trans hF0.symm
  have hmid := hleft.eventuallyEq hF isPreconnected_univ (mem_univ 0) (mem_univ 1) hstart
  rw [p.target] at hmid
  -- The second factor: it starts at the junction germ, hence at `F 1`.
  have hright := hK.right_of_trans
  have hjunction : projIcc (0 : ℝ) 1 zero_le_one ((((0 : I) : ℝ) + 1) / 2)
      = projIcc (0 : ℝ) 1 zero_le_one (((1 : I) : ℝ) / 2) := by
    ext; norm_num [coe_projIcc]
  refine continuesAlong_iff_exists.mpr
    ⟨fun t : I => K (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2)), hright, ?_⟩
  rw [q.source]
  simpa only [hjunction] using hmid

/-- **Continuability inside a fixed domain is invariant under base-point transport along an
analytic continuation inside that domain.** If `F` continues a germ along a path `p` of `U` from
`z₀` to `z₁`, then the germ `F 1` delivered at `z₁` continues inside `U` exactly when the germ
`F 0` it started from does.

This strengthens `TauCeti.continuesInside_of_isAnalyticContinuationAlong`, its `←` direction, to
an equivalence, and drops the representative `f₀` from the statement; the version with a
representative is recovered from `TauCeti.continuesInside_congr`. The `→` direction transports the
base point back along the reversed path `p.symm`, along which the family read backwards, `F ∘ σ`,
is again a continuation: reversing the parameter is a reparametrisation of the parameter interval
by the central symmetry `σ`, which `TauCeti.IsAnalyticContinuationAlong.reparam` transports. So
neither endpoint of `p` is distinguished, and any point the branch reaches inside `U` may serve as
the base point of `TauCeti.ContinuesInside`, the hypothesis of the monodromy theorem for a simply
connected domain (`Conformal/GlobalBranch.lean`). -/
theorem continuesInside_iff_of_isAnalyticContinuationAlong [CompleteSpace E] {U : Set ℂ}
    {z₀ z₁ : ℂ} {p : Path z₀ z₁} (hpU : ∀ t, p t ∈ U)
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) :
    ContinuesInside (F 1) U z₁ ↔ ContinuesInside (F 0) U z₀ := by
  -- The family read backwards is a continuation along the reversed path.
  have hsymm : IsAnalyticContinuationAlong (F ∘ σ) (⇑p.symm) univ :=
    (hF.reparam continuous_symm.continuousOn (mapsTo_univ _ _)).congr_path fun t _ => by
      rw [Path.symm_apply]
  refine ⟨fun h => ?_, fun h => continuesInside_of_isAnalyticContinuationAlong h hpU hF .rfl⟩
  have hstart : (F ∘ σ) 0 =ᶠ[𝓝 z₁] F 1 := by
    simp only [Function.comp_apply, symm_zero]
    exact .rfl
  have hback := continuesInside_of_isAnalyticContinuationAlong h (p := p.symm)
    (fun t => by rw [Path.symm_apply]; exact hpU (σ t)) hsymm hstart
  rwa [Function.comp_apply, symm_one] at hback

end Trans

end TauCeti
