/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Exposition extractor

Dumps every declaration in the `TauCeti` library, together with its
library-internal dependency edges, as JSONL — the input to the exposition site
generator (`scripts/exposition/generate.py`). One line per declaration:

```json
{"id": "<full name>", "n": "<display name>", "m": "<module>", "k": "<kind>",
 "p": <private?>, "r": [startLine, startCol, endLine, endCol], "s": [nameLine, nameCol],
 "d": "<docstring?>", "deps": ["<id>", ...], "ext": <distinct external deps>}
```

Dependency edges follow the kernel closure: references to compiler-generated
auxiliaries (`match_*`, equation lemmas, `.rec`, constructors, projections, ...)
are expanded transitively until a library declaration is reached, so an edge
`A -> B` means "checking `A` requires `B`". `ext` counts distinct declarations
outside the library (Mathlib/core) encountered on that boundary.

Adapted from Lean Pool's exposition extractor (Vasily Ilin,
https://github.com/Vilin97/lean-pool, Apache 2.0), which itself ports its
coercion-instance recovery from LMLExposition (Rémy Degenne,
https://github.com/LeanMachineLearning/exposition). Lean Pool's per-project
extraction driver and minimal-file command tables are dropped: Tau Ceti is one
integrated library, extracted in a single environment.

The environment is imported at the default `OLeanLevel.private`, which loads
all data as if no `module` annotations were present — so proof terms (for
dependency edges), declaration ranges, and docstrings are all visible even
though the library uses the module system.

Usage: `lake env lean --run scripts/exposition/Extract.lean <out.jsonl> [<module> ...]`
from the repository root, after `lake build`. Explicit module arguments
override the default whole-library import (useful against a partial build).
-/

open Lean Meta

namespace Exposition

/-- The library whose declarations we extract. -/
def libraryRoot : Name := `TauCeti

/-- Is `module` one of the library's own modules? -/
def isLibraryModule (module : Name) : Bool :=
  libraryRoot.isPrefixOf module

/-- Coarse declaration kind, used only as a fallback: the site generator
refines it from the source keyword (`lemma` vs `theorem`, `abbrev` vs `def`,
`instance`, `class`, ...). -/
def kindOf (env : Environment) (name : Name) (info : ConstantInfo) : Option String :=
  match info with
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => if isStructure env name then some "structure" else some "inductive"
  | _ => none

/-- Is `name` a notation/syntax parser descriptor? Parser declarations are
implementation detail of notations, not mathematical content, so they are not
exposition nodes. -/
def isParserDescr (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info =>
    info.type.isConstOf ``Lean.ParserDescr
      || info.type.isConstOf ``Lean.TrailingParserDescr
  | none => false

/-- Mirrors the doc-gen4 / import-graph blacklist for generated declarations. -/
def isGenerated (env : Environment) (name : Name) : CoreM Bool := do
  let display := privateToUserName name
  if display.isInternalDetail then return true
  if isAuxRecursor env name || isNoConfusion env name then return true
  if (← isRec name) || (← Meta.isMatcher name) then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  if isParserDescr env name then return true
  return false

/-- Should `name` appear as a node of the exposition? -/
def isExposed (env : Environment) (name : Name) (info : ConstantInfo) : CoreM Bool := do
  let some moduleIdx := env.getModuleIdxFor? name | return false
  unless isLibraryModule env.header.moduleNames[moduleIdx.toNat]! do return false
  if (kindOf env name info).isNone then return false
  if ← isGenerated env name then return false
  return (← findDeclarationRanges? name).isSome

/-- Constants a declaration mentions, including constructor signatures for
inductives/structures (field types live in the constructor's type). -/
def directUses (env : Environment) (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v =>
    let base := v.ctors.foldl (init := info.getUsedConstantsAsSet)
      (fun acc c => match env.find? c with
        | some ci => acc.insertMany ci.getUsedConstantsAsSet
        | none => acc)
    -- Structure field defaults live in generated `<S>.<field>._default`
    -- functions; seeding them lets the resolver tunnel through their bodies.
    let withDefaults :=
      if (getStructureInfo? env v.name).isSome then
        (getStructureFields env v.name).foldl (init := base) fun acc field =>
          match getDefaultFnForField? env v.name field with
          | some defaultFn => acc.insert defaultFn
          | none => acc
      else base
    withDefaults.toArray
  | _ => info.getUsedConstantsAsSet.toArray

/-- Coercion type classes whose instances Lean unfolds at use sites; the
instance must still be present for the source's `↑`/`⇑` to elaborate, yet
`getUsedConstants` alone misses it (ported from LMLExposition). -/
def coercionClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTC, ``CoeHead, ``CoeTail, ``CoeHTCT,
   ``CoeOut, ``CoeDep]

/-- If `type` is, under binders, a coercion-class application `Cls Src …`,
the head constant of `Src` (the type coerced *from*). -/
partial def coercionSourceType? (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ b _ => coercionSourceType? b
  | _ =>
    let (fn, args) := type.getAppFnArgs
    if coercionClasses.contains fn && args.size ≥ 1 then
      args[0]!.getAppFn.constName?
    else none

/-- Expand a seed set of used constants, tunnelling through generated library
auxiliaries, until exposed library declarations (edges) or non-library
constants (externals) are reached. -/
def resolveSeeds (env : Environment) (self : Name) (seeds : Array Name)
    (exposed : NameSet) : NameSet × Nat := Id.run do
  let mut edges : NameSet := {}
  let mut externals : NameSet := {}
  let mut visited : NameSet := {}
  let mut stack : Array Name := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if c == self || visited.contains c then continue
    visited := visited.insert c
    if exposed.contains c then
      edges := edges.insert c
      continue
    let inLibrary := match env.getModuleIdxFor? c with
      | some idx => isLibraryModule env.header.moduleNames[idx.toNat]!
      | none => false
    if inLibrary then
      if let some ci := env.find? c then
        stack := stack ++ directUses env ci
    else
      externals := externals.insert c
  return (edges, externals.size)

/-- Library constants whose type is a coercion-class application, keyed by the
head constant of the type coerced *from* (ported from LMLExposition's
`coercionInstancesByType`; the type shape suffices, the instance table is not
consulted). -/
def coercionInstancesByType (env : Environment) (exposed : NameSet) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for name in exposed.toArray do
    if let some info := env.find? name then
      if let some src := coercionSourceType? info.type then
        m := m.insert src ((m.getD src #[]).push name)
  return m

def declJson (env : Environment) (name : Name) (info : ConstantInfo)
    (exposed : NameSet) (coercionInsts : Std.HashMap Name (Array Name)) :
    CoreM (Option Json) := do
  let some ranges ← findDeclarationRanges? name | return none
  let some kind := kindOf env name info | return none
  let some moduleIdx := env.getModuleIdxFor? name | return none
  let module := env.header.moduleNames[moduleIdx.toNat]!
  let display := privateToUserName name
  let doc ← findDocString? env name
  -- Coercion instances are unfolded out of elaborated terms; re-attach the
  -- instances coercing *from* any referenced type (LMLExposition's
  -- `addCoercionInsts`).
  let addCoercion (edges : NameSet) : NameSet :=
    edges.toArray.foldl (init := edges) fun acc dep =>
      (coercionInsts.getD dep #[]).foldl (init := acc) fun acc2 inst =>
        if inst == name then acc2 else acc2.insert inst
  let (rawEdges, extCount) := resolveSeeds env name (directUses env info) exposed
  let edges := addCoercion rawEdges
  let r := ranges.range
  let s := ranges.selectionRange
  return some <| Json.mkObj <| [
    ("id", Json.str name.toString),
    ("n", Json.str display.toString),
    ("m", Json.str module.toString),
    ("k", Json.str kind),
    ("r", toJson [r.pos.line, r.pos.column, r.endPos.line, r.endPos.column]),
    ("s", toJson [s.pos.line, s.pos.column]),
    ("deps", Json.arr (edges.toArray.map (Json.str ∘ Name.toString))),
    ("ext", Json.num extCount)
  ] ++ (if isPrivateName name then [("p", Json.bool true)] else [])
    ++ (match doc with | some d => [("d", Json.str d)] | none => [])

/-- Pass 1: the exposed node set, in module order. -/
def exposedDecls (env : Environment) : CoreM (NameSet × Array Name) := do
  let mut exposed : NameSet := {}
  let mut names : Array Name := #[]
  for moduleIdx in [0:env.header.moduleNames.size] do
    unless isLibraryModule env.header.moduleNames[moduleIdx]! do continue
    let moduleData : ModuleData := env.header.moduleData[moduleIdx]!
    for name in moduleData.constNames do
      -- A constant can appear in several modules' `constNames` when two files
      -- declare it textually; keep the first occurrence only.
      if exposed.contains name then continue
      let some info := env.find? name | continue
      if ← isExposed env name info then
        exposed := exposed.insert name
        names := names.push name
  return (exposed, names)

def extract (outPath : System.FilePath) (exposed : NameSet) (names : Array Name) :
    CoreM Unit := do
  let env ← getEnv
  let coercionInsts := coercionInstancesByType env exposed
  IO.FS.createDirAll (outPath.parent.getD ".")
  let handle ← IO.FS.Handle.mk outPath .write
  for name in names do
    let some info := env.find? name | continue
    if let some json ← declJson env name info exposed coercionInsts then
      handle.putStrLn json.compress
  handle.flush
  IO.println s!"exposition: wrote {names.size} declarations to {outPath}"

/-- The module name for a `.lean` source path, e.g. `TauCeti/Foo/Bar.lean ↦
TauCeti.Foo.Bar` (as in `scripts/Axioms.lean`). -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively, sorted for a deterministic
import (and hence dump) order. -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc.qsort (·.toString < ·.toString)

end Exposition

unsafe def main (args : List String) : IO UInt32 := do
  let outPath := args[0]?.getD "exposition-dump.jsonl"
  -- Further arguments override the imported modules; the default is the whole
  -- library, enumerated from the source tree because the root module is
  -- intentionally empty and imports nothing.
  let modules ← do
    if args.length > 1 then
      pure (args.drop 1 |>.map (·.toName)).toArray
    else
      Exposition.collectLeanModules (Exposition.libraryRoot.toString : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  -- Extension states must be loaded (and initializers executed) so that
  -- extension-backed queries (matcher info, structure info, ...) see their data.
  Lean.enableInitializersExecution
  let imports := modules.map fun module => ({ module } : Lean.Import)
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  let coreContext : Lean.Core.Context := {
    fileName := "<exposition-extract>",
    fileMap := default,
    maxHeartbeats := 0
  }
  let run : Lean.CoreM Unit := do
    let (exposed, names) ← Exposition.exposedDecls env
    Exposition.extract outPath exposed names
  let (result, _) ← run.toIO coreContext { env }
  let _ := result
  return 0
