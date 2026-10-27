module

public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils

@[expose] public section

/-!
# Public steps stay with their algorithm

**The attribute.** `@[step_of X]` marks a public `step_…` declaration as a step of `X`.

**The scope check.** A step may be used only in its file and that file's satellite theorem files
(#227): wherever the source names it, or a constant under it (`step_foo.eq_1`). Unfolding a
public definition that calls a step is no use of it.

**The naming check.** `aux_…` is `private`, `step_…` carries `@[step_of …]`.
`set_option linter.stepOf false` turns both checks off.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open Lean Elab Command

namespace CORALean.StepOf


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The last component of a declaration's name as written, `private` mangling removed. -/
private meta def aux_lastName (n : Name) : String :=
  match (privateToUserName? n).getD n with
  | .str _ s => s
  | _ => ""

/-- Whether `op` occurs in `stem` as a whole CamelCase word run, followed by the end of `stem`, `_`
or an uppercase letter (`matches` of `scripts/conventions/satellites.py`). -/
private meta def aux_matches (stem op : String) : Bool := Id.run do
  if op.isEmpty then return false
  let s := stem.toList
  let o := op.toList
  for i in [0:s.length - o.length + 1] do
    if (s.drop i).take o.length == o then
      match s[i + o.length]? with
      | none => return true
      | some c => if c == '_' || c.isUpper then return true
  return false

/-- The operations of a directory, out of `ops`, that the theorem file `stem` is a satellite of
(`operations_of`): the matching stems, less any contained in a longer matching stem. -/
private meta def aux_operationsOf (stem : String) (ops : Array String) : Array String :=
  let hit := ops.filter (aux_matches stem ·)
  hit.filter fun x => !hit.any fun y => x != y && (y.splitOn x).length > 1

/-- The `Operations/` stems beside the `Theorems/` directory of the file being elaborated, read from
disk as `satellites.py` does, or from the imported modules when the directory cannot be read. -/
private meta def aux_operationStems (dir : Name) : CommandElabM (Array String) := do
  let file : System.FilePath := (← getFileName)
  let fromDisk ← match file.parent.bind (·.parent) with
    | some d => try
        let es ← (d / "Operations").readDir
        pure (some (es.filterMap fun e =>
          if e.fileName.endsWith ".lean" then some (e.fileName.dropEnd 5).toString else none))
      catch _ => pure none
    | none => pure none
  let stems := fromDisk.getD <| (← getEnv).header.moduleNames.filterMap fun
    | .str p s => if p == dir ++ `Operations then some s else none
    | _ => none
  return stems.filter (· != "Basic")

/-- The verdicts of `aux_mayUse` so far, one per pair of modules. -/
private meta initialize aux_verdicts : IO.Ref (Std.HashMap (Name × Name) Bool) ← IO.mkRef {}

/-- Whether the module `user` may use a step declared in the module `home`: it is `home`, or
`user` is `<D>.Theorems.<S>`, `home` is `<D>.Operations.<X>`, and `S` is a satellite of `X`. -/
private meta def aux_mayUse (user home : Name) : CommandElabM Bool := do
  if user == home then return true
  if let some v := (← aux_verdicts.get)[(user, home)]? then return v
  -- `satellites_of`: the same directory, neither file a `Basic.lean`, the longest stems winning
  let v ← match user, home with
    | .str (.str d₁ "Theorems") s, .str (.str d₂ "Operations") x =>
      if d₁ != d₂ || s == "Basic" || x == "Basic" || !aux_matches s x then pure false
      else pure ((aux_operationsOf s (← aux_operationStems d₁)).contains x)
    | _, _ => pure false
  aux_verdicts.modify (·.insert (user, home) v)
  return v


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `@[step_of X]`: this public `step_…` declaration is a step of the algorithm `X`. -/
syntax (name := step_of) "step_of " ident : attr

/-- The steps and their algorithms; only a `step_…` declaration takes the attribute. -/
meta initialize stepOfAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `step_of
    descr := "a step of one algorithm, usable only in its file and that file's satellites"
    getParam := fun decl stx => do
      unless (aux_lastName decl).startsWith "step_" do
        throwError "`@[step_of]` is for a declaration named `step_…`, not `{decl}` (#269)"
      match stx with
      | `(attr| step_of $x:ident) => return x.getId
      | _ => throwUnsupportedSyntax }

/-- The step that `c` is or belongs to (`step_foo.eq_1`), with its algorithm. -/
meta def stepOf? (env : Environment) : Name → Option (Name × Name)
  | .anonymous => none
  | c@(.str p _) | c@(.num p _) =>
    match stepOfAttr.getParam? env c with
    | some x => some (c, x)
    | none => stepOf? env p

meta section

/-- Turns the scope and naming checks of `stepOfLinter` on or off. -/
register_option linter.stepOf : Bool := {
  defValue := true
  descr := "check that a `@[step_of X]` declaration is used only in X's file and its satellites, \
    that `aux_` declarations are private and that `step_` ones carry `@[step_of]`"
}

end

/-- The naming check of a declaration `c` this command declares, at its name `stx`. -/
meta def checkName (env : Environment) (stx : Syntax) (c : Name) : CommandElabM Unit := do
  let last := aux_lastName c
  if last.startsWith "aux_" && !isPrivateName c then
    logErrorAt stx m!"`{c}` is named `aux_…`, so it is `private`; a public step is named \
      `step_…` and carries `@[step_of …]` (#269)"
  if last.startsWith "step_" && isPrivateName c then
    logErrorAt stx m!"`{c}` is named `step_…`, so it is public; a `private` helper is named \
      `aux_…` (#269)"
  else if last.startsWith "step_" && (stepOfAttr.getParam? env c).isNone then
    logErrorAt stx m!"`{c}` is named `step_…` but carries no `@[step_of X]` naming its \
      algorithm (#269)"

/-- The scope and naming checks of the module docstring, over the constants a command names. -/
meta def stepOfLinter : Linter where
  run _ := do
    unless Linter.getLinterValue linter.stepOf (← Linter.getLinterOptions) do return
    let env ← getEnv
    let mut seen : Std.HashSet (String.Pos.Raw × Name) := {}
    for tree in (← getInfoTrees) do
      -- every constant the source names, with whether it is being declared here
      let uses := tree.foldInfo (init := #[]) fun _ info acc =>
        match info with
        | .ofTermInfo ti => match ti.expr with
          | .const c _ => acc.push (ti.stx, c, ti.isBinder)
          | _ => acc
        | _ => acc
      for (stx, c, isBinder) in uses do
        if isBinder then
          if (env.getModuleIdxFor? c).isNone then checkName env stx c
        else if let some (step, alg) := stepOf? env c then
          let key := (stx.getPos?.getD 0, step)
          if seen.contains key then continue
          seen := seen.insert key
          -- a step of this file is always in scope
          let some idx := env.getModuleIdxFor? step | continue
          let home := env.header.moduleNames[idx.toNat]!
          unless ← aux_mayUse env.mainModule home do
            logErrorAt stx m!"`{step}` is a step of `{alg}`; only its file `{home}` and that \
              file's satellite theorem files may use it (#227)"

meta initialize addLinter stepOfLinter

end CORALean.StepOf


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
