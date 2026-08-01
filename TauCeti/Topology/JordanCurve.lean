/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Topology.JordanCurve.Separation

/-!
# Jordan curves

This module re-exports the Jordan-curve API: the predicate `TauCeti.IsJordanCurve` together with
its transfer lemmas (`TauCeti.Topology.JordanCurve.Basic`), and the cutting of a Jordan curve at
one or two of its points (`TauCeti.Topology.JordanCurve.Separation`). It declares nothing of its
own, and keeps the import path `TauCeti.Topology.JordanCurve` — which named the basic theory
before it moved into the directory — working.
-/
