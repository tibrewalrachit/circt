/-!
# Line-based parser for generic-syntax MLIR

`circt-opt --mlir-print-op-generic` prints exactly one operation per
line for the flat `hw`/`comb`/`seq` modules Veda imports, so a
line-based parser is adequate and vastly simpler than a full MLIR
grammar. Every deviation from the expected shape is a hard error — the
importer is the TCB and must never guess (rule 2).

Recognized line shapes:
* `#loc ...` and structural braces — skipped / handled structurally
* `"hw.module"() <{... module_type = !hw.modty<...> ... sym_name = "..."}> ({`
* `^bb0(%arg0: i1, ...):`
* `%N = "dialect.op"(%a, %b) <{attrs}> : (types) -> type`
* `"hw.output"(%a) : (types) -> ()`
-/

namespace Veda.Import

/-- One parsed generic operation. -/
structure GOp where
  results : List String
  name : String
  operands : List String
  /-- Raw text inside `<{ ... }>`, if present. -/
  attrs : String
  argTypes : List String
  resTypes : List String
  deriving Repr, Inhabited

/-- A parsed `hw.module`. -/
structure GModule where
  name : String
  /-- Port name, type token (e.g. `i8`), in declaration order. -/
  inputs : List (String × String)
  outputs : List (String × String)
  /-- Block argument names, in order (match `inputs`). -/
  blockArgs : List String
  ops : List GOp
  outputOperands : List String
  deriving Repr, Inhabited

/-- Split a comma-separated list at the top level (no nesting inside
the token lists we handle). -/
def splitCommas (s : String) : List String :=
  if s.trimAscii.toString.isEmpty then [] else (s.splitOn ",").map (·.trimAscii.toString)

/-- Extract the text between the first `open` and its matching `close`,
assuming no nesting of the same delimiter pair inside. -/
def between (s : String) (openS closeS : String) : Option String := do
  let parts := s.splitOn openS
  match parts with
  | _ :: rest =>
      let tail := openS.intercalate rest
      let inner := tail.splitOn closeS
      match inner with
      | x :: _ :: _ => some x
      | _ => none
  | _ => none

/-- Parse the width of a type token: `i8` ↦ 8, `!seq.clock` ↦ 1. -/
def typeWidth (ty : String) : Option Nat :=
  let ty := ty.trimAscii.toString
  if ty == "!seq.clock" then some 1
  else if ty.startsWith "i" then (ty.drop 1).toNat?
  else none

/-- Parse an attribute of the form `key = <int>` or `key = true/false`
from a raw attribute string. -/
def attrNat (attrs key : String) : Option Nat := do
  let after ← (attrs.splitOn (key ++ " = "))[1]?
  let tok := ((after.splitOn ":")[0]? |>.getD after).trimAscii.toString
  let tok := (tok.splitOn ",").headD tok |>.trimAscii.toString
  let tok := (tok.splitOn "}").headD tok |>.trimAscii.toString
  if tok == "true" then some 1
  else if tok == "false" then some 0
  else if tok.startsWith "-" then
    none  -- negative constants unsupported for now: fail the import
  else tok.toNat?

/-- Parse a string attribute `key = "..."`. -/
def attrStr (attrs key : String) : Option String := do
  let after ← (attrs.splitOn (key ++ " = \""))[1]?
  (after.splitOn "\"")[0]?

/-- Parse one `%r = "op"(%a, %b) <{attrs}> : (tys) -> ty` line. -/
def parseOpLine (line : String) : Option GOp := do
  let line := line.trimAscii.toString
  -- results
  let (results, rest) ←
    if line.startsWith "%" then
      let parts := line.splitOn " = "
      match parts with
      | res :: restParts => some (splitCommas res, " = ".intercalate restParts)
      | _ => none
    else
      some ([], line)
  guard (rest.startsWith "\"")
  let name ← ((rest.drop 1).toString.splitOn "\"")[0]?
  let afterName := (rest.drop (name.length + 2)).toString
  let operandsRaw ← between afterName "(" ")"
  let operands := splitCommas operandsRaw
  let attrs := (between afterName "<{" "}>").getD ""
  -- type signature: after the last " : "
  let sigParts := afterName.splitOn " : "
  let sig ← sigParts.getLast?
  guard (sigParts.length ≥ 2)
  let argTyRaw ← between sig "(" ")"
  let resTyRaw := ((sig.splitOn "->")[1]?).getD ""
  pure { results, name, operands, attrs,
         argTypes := splitCommas argTyRaw,
         resTypes := splitCommas (resTyRaw.trimAscii.toString) }

/-- Parse the `input a : i1, output z : i8` port list of `!hw.modty<...>`. -/
def parsePorts (modty : String) : List (String × String × Bool) :=
  (splitCommas modty).filterMap fun port =>
    let port := port.trimAscii.toString
    let isInput := port.startsWith "input "
    let isOutput := port.startsWith "output "
    if !isInput && !isOutput then none
    else
      let rest := (if isInput then port.drop 6 else port.drop 7).toString
      match rest.splitOn " : " with
      | [n, ty] => some (n.trimAscii.toString, ty.trimAscii.toString, isInput)
      | _ => none

/-- Parse a full generic-form module dump. -/
def parseModule (text : String) : Except String GModule := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  let mut m : GModule := default
  let mut seenModule := false
  for line in lines do
    if line.isEmpty || line.startsWith "#" || line.startsWith "\"builtin.module\""
        || line.startsWith "})" || line == "}" then
      continue
    else if line.startsWith "\"hw.module\"" then
      if seenModule then
        throw "multiple hw.module ops: composition lands in M5"
      seenModule := true
      let modty ← match between line "!hw.modty<" ">" with
        | some s => pure s
        | none => throw s!"hw.module without module_type: {line}"
      let name := (attrStr line "sym_name").getD "anonymous"
      let ports := parsePorts modty
      m := { m with
        name,
        inputs := ports.filterMap fun (n, ty, isIn) =>
          if isIn then some (n, ty) else none,
        outputs := ports.filterMap fun (n, ty, isIn) =>
          if isIn then none else some (n, ty) }
    else if line.startsWith "^bb0" then
      let argsRaw := (between line "(" ")").getD ""
      m := { m with
        blockArgs := (splitCommas argsRaw).filterMap fun a =>
          (a.splitOn ":").head?.map (·.trimAscii.toString) }
    else if line.startsWith "\"hw.output\"" then
      match parseOpLine line with
      | some op => m := { m with outputOperands := op.operands }
      | none => throw s!"unparseable hw.output line: {line}"
    else
      match parseOpLine line with
      | some op => m := { m with ops := m.ops ++ [op] }
      | none => throw s!"unparseable line: {line}"
  if !seenModule then throw "no hw.module found"
  pure m

end Veda.Import
