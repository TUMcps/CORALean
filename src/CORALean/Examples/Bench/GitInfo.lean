/-!
# What went into a run, read from the environment

`meta.commit`, `.leanVersion` and `.machine` in the output JSON come from here:
each is a subprocess call that may not be available (no `git` on the artifact
evaluator's image, a `/proc/cpuinfo` that is not Linux's), so every one of
these falls back to `"unknown"` rather than failing the run over a field that
exists only for the paper's appendix.

## Inputs
* none

## Output
* commit, Lean version and machine of the run
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

/-- Runs `cmd args…`, trimmed, or `"unknown"` if the process cannot be spawned
or exits with anything but `0`. Never throws -- the one property every field
below relies on. -/
def runOrUnknown (cmd : String) (args : Array String) : IO String := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args }
    if out.exitCode = 0 then pure out.stdout.trimAscii.toString else pure "unknown"
  catch _ => pure "unknown"

def gitCommit : IO String := runOrUnknown "git" #["rev-parse", "HEAD"]

def leanVersion : IO String := runOrUnknown "lean" #["--version"]

def unameInfo : IO String := runOrUnknown "uname" #["-a"]

/-- The first `model name` line of `/proc/cpuinfo`, Linux only; `"unknown"`
everywhere else, since there is no portable way to ask. -/
def cpuModel : IO String := do
  try
    let text ← IO.FS.readFile "/proc/cpuinfo"
    match (text.splitOn "\n").find? (·.startsWith "model name") with
    | some line => pure (((line.splitOn ":")[1]?.getD "unknown").trimAscii.toString)
    | none => pure "unknown"
  catch _ => pure "unknown"

/-- `nproc`'s count, or `0` if it cannot be asked. -/
def coreCount : IO Nat := do
  let s ← runOrUnknown "nproc" #[]
  pure (s.toNat?.getD 0)

/-- Everything `meta.machine` in the output JSON reports: what `uname -a`,
`/proc/cpuinfo` and `nproc` say about the machine a run happened on, each
falling back to `"unknown"`/`0` alone rather than losing the rest. -/
structure MachineInfo where
  uname : String
  cpu : String
  cores : Nat


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Collects the four calls above into one `MachineInfo`. -/
def machineInfo : IO MachineInfo := do
  pure ⟨← unameInfo, ← cpuModel, ← coreCount⟩

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
