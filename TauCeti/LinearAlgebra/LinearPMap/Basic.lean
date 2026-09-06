/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Basic lemmas on partial linear maps

General lemmas on `LinearPMap` that Mathlib does not provide.

## Main results

* `LinearPMap.congr_fun`: the value-level part of `LinearPMap.ext_iff`, with the two domain
  memberships as explicit arguments.
* `LinearPMap.neg_smul` and `LinearPMap.smul_neg`: a negation moves through a scalar multiple.
-/

public section

namespace LinearPMap

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module S F]

/-- Equal partial linear maps take equal values: the value-level part of `LinearPMap.ext_iff`,
with the two domain memberships as explicit arguments. -/
protected theorem congr_fun {f g : E →ₛₗ.[σ] F} (h : f = g) {x : E} (hf : x ∈ f.domain)
    (hg : x ∈ g.domain) : f ⟨x, hf⟩ = g ⟨x, hg⟩ :=
  (LinearPMap.ext_iff.mp h).2 (x := x) (hf := hf) (hg := hg)

/-- Negating the scalar negates the scalar multiple of a partial linear map (`LinearPMap` is not a
module, so this is not an instance of `neg_smul`). -/
@[simp]
theorem neg_smul {M : Type*} [Ring M] [Module M F] [SMulCommClass S M F] (c : M)
    (A : E →ₛₗ.[σ] F) : (-c) • A = -(c • A) :=
  LinearPMap.ext rfl fun _ _ _ => _root_.neg_smul _ _

/-- Negating the map negates the scalar multiple of a partial linear map. -/
@[simp]
theorem smul_neg {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass S M F] (c : M)
    (A : E →ₛₗ.[σ] F) : c • (-A) = -(c • A) :=
  LinearPMap.ext rfl fun _ _ _ => _root_.smul_neg _ _

end LinearPMap

end
