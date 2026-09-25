import CORALean.Examples.Bench.Registry

/-!
# `lake exe bench`, and `lake env lean --run` at this file

The experiment harness's entry point, following `Examples/Demo.lean`'s shape:
a `[[lean_lib]]` for `lake build` to elaborate this against every commit, and a
`[[lean_exe]]` a human runs. See `experiments/README.md` for the one-command
contract this satisfies and `CORALean.Bench.Cli.CliArgs` for every flag.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  MAIN DEFINITION  ====================================== --

def main (argv : List String) : IO Unit :=
  match CORALean.Bench.parseArgs argv with
  | .error e => do
    IO.eprintln s!"bench: {e}"
    IO.Process.exit 1
  | .ok args => CORALean.Bench.dispatch args


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
