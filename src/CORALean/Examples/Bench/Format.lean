/-!
# IEEE-shaped precision labels

The paper authors name a precision the way IEEE 754 does -- `binary64`,
`binary32`, `binary16`, `binary8` (E4M3), `binary4` (E2M1) -- rather than a
raw bit count, so `--format` is the primary way `bench` picks a `Dyadic`
precision and `formatToPrec`/`precToFormat` are the one place the mapping is
written down. `binary64` is `Dyadic 53`, chosen to agree with native `Float`'s
53-bit significand; `--prec` still takes a raw count directly, for a precision
none of these five name.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

/-- Every label `--format` accepts, and the `Dyadic` significand width it
denotes. -/
def formatToPrec (fmt : String) : Except String Nat :=
  match fmt with
  | "binary64" => pure 53
  | "binary32" => pure 24
  | "binary16" => pure 11
  | "binary8" => pure 4
  | "binary4" => pure 2
  | _ => throw
      s!"`--format` is one of binary64|binary32|binary16|binary8|binary4, not `{fmt}`"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reverse of `formatToPrec`, for output metadata: a significand width
that does not name one of the five formats (an ad hoc `--prec`) reports
itself as `"custom<p>"` rather than guessing which label was meant. -/
def precToFormat (p : Nat) : String :=
  match p with
  | 53 => "binary64"
  | 24 => "binary32"
  | 11 => "binary16"
  | 4 => "binary8"
  | 2 => "binary4"
  | _ => s!"custom{p}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
