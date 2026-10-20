import CORALean.Examples.Oracle.Dispatch

/-!
# The oracle's request loop, for any set of dtypes

`run dtypes` is `lake exe oracle`'s whole `main`, apart from which dtypes it serves: one JSON
line in, one line out (`Dispatch.respond`), until stdin ends. `Oracle.lean` serves `sounds`;
another executable serves its own `DtypeSet`, for example the unsound one under `Bench/`.

## Inputs
* `dtypes` – dtypes served

## Output
* the requests are served until end of input
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

/-- `line`, its trailing `\n` and, on Windows, `\r`, dropped -- `stdin.getLine`'s own shape,
mirrored from `IO.FS.Stream.lines`. -/
def stripNewline (line : String) : String :=
  if line.isEmpty then line
  else if line.back == '\n' then
    let line := line.dropEnd 1 |>.copy
    if !line.isEmpty && line.back == '\r' then line.dropEnd 1 |>.copy else line
  else line

/-- One line in, one line out, until `stdin.getLine` returns empty -- EOF, `Stream.getLine`'s
own convention, at which point `main` returns and the process exits `0`. -/
partial def loop (dtypes : DtypeSet) (version : CoraleanVersion)
    (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then pure () else
    stdout.putStrLn (respond dtypes version (stripNewline line)).compress
    stdout.flush
    loop dtypes version stdin stdout


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Serves `dtypes` on stdin and stdout until stdin ends. -/
def run (dtypes : DtypeSet) : IO Unit := do
  let version ← coraleanCommit
  loop dtypes version (← IO.getStdin) (← IO.getStdout)

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
