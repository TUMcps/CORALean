import CORALean.Examples.Bench.GitInfo

/-!
# `ping`'s version, independent of the caller's current directory

`Bench.gitCommit` runs `git rev-parse HEAD` in the process's own current
directory, which is correct for `bench`: it is always run from the repo root.
The oracle is not -- `CORA.cpp` spawns it from *its own* repository -- so
`ping` cannot reuse `gitCommit` without reporting CORA.cpp's commit instead of
CORALean's, which is the bug this file fixes.

`coraleanCommit` instead resolves a directory that is CORALean's own: the
linked executable's own location (`IO.appPath`'s parent, `<repo>/.lake/build/
bin/oracle`) under the linked backend, or the current directory under the
interpreter (where `IO.appPath` is the `lean` binary, not this repository).
Either candidate is accepted only once its `git rev-parse --show-toplevel`
resolves to a directory whose `lakefile.toml` declares `name = "CORALean"`,
so an unrelated repository -- CORA.cpp's, or any other tree the oracle
happens to be run from -- is never reported as this one; `"unknown"` when
neither candidate passes that check.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean.Bench (runOrUnknown)

/-- Runs `cmd args…`, trimmed, or `none` if the process cannot be spawned or exits with anything
but `0` -- `runOrUnknown` with the failure visible, needed here to tell "no output" apart from
"the command failed", which `"unknown"` alone cannot. -/
def runOk (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args }
    if out.exitCode = 0 then pure (some out.stdout.trimAscii.toString) else pure none
  catch _ => pure none

/-- Whether `dir/lakefile.toml` declares `name = "CORALean"` -- the check that keeps a directory
inside some *other* repository from ever being accepted as this one. `false`, never an
exception, when the file is missing or unreadable. -/
def isCoraleanLakefile (dir : String) : IO Bool := do
  try
    let text ← IO.FS.readFile (dir ++ "/lakefile.toml")
    pure (((text.splitOn "\n").map (·.trimAscii.toString)).contains "name = \"CORALean\"")
  catch _ => pure false

/-- `dir`'s repository toplevel, accepted only if it is CORALean's own: `git -C dir rev-parse
--show-toplevel`, checked against `isCoraleanLakefile`. `none` if `dir` is not inside a git
repository, or is inside one that is not this one. -/
def coraleanToplevel (dir : String) : IO (Option String) := do
  match ← runOk "git" #["-C", dir, "rev-parse", "--show-toplevel"] with
  | none => pure none
  | some top => do if ← isCoraleanLakefile top then pure (some top) else pure none

/-- The directory to resolve CORALean's own git info from, independent of the caller's cwd: the
executable's own directory (`IO.appPath`'s parent) first, the cwd otherwise (the interpreter,
per the module docstring). `none` if neither passes `coraleanToplevel`'s check. -/
def coraleanDir : IO (Option String) := do
  let exeDir := (← IO.appPath).parent.map (·.toString) |>.getD "."
  match ← coraleanToplevel exeDir with
  | some top => pure (some top)
  | none => coraleanToplevel "."

/-- `ping`'s `"version"`/`"dirty"` fields: CORALean's own short commit and whether its working
tree has uncommitted changes, both read from `coraleanDir`'s toplevel. -/
structure CoraleanVersion where
  version : String
  dirty : Bool


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORALean's own short commit and dirty flag, resolved via `coraleanDir` so the answer never
depends on the caller's current directory: `"unknown"`/`false` if no CORALean checkout can be
found from either candidate directory. -/
def coraleanCommit : IO CoraleanVersion := do
  match ← coraleanDir with
  | none => pure ⟨"unknown", false⟩
  | some dir => do
    let rev ← runOrUnknown "git" #["-C", dir, "rev-parse", "--short", "HEAD"]
    let statusOpt ← runOk "git" #["-C", dir, "status", "--porcelain"]
    let dirty := match statusOpt with
      | some s => !s.isEmpty
      | none => false
    pure ⟨rev, dirty⟩

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
