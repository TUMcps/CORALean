module

public import CORALean.HybridDynamics.Definitions.NonlinearResetArg

@[expose] public section

/-!
# `NonlinearReset.expansionPointCora`: CORA's `aux_expansionPoint`

`hybridDynamics/@nonlinearReset/evaluate.m`, l. 82-95: `px` is `center(x)` for a set and `x` for a
number; `pu` is `center(u)` for a set `u` and, after `elseif isnumeric(x)`, `u` for a numeric `x`.
The test is on `x`, where `isnumeric(u)` is meant, so a set `x` with a numeric `u` (also the
default `u = zeros(m, 1)`) leaves `pu` unassigned: MATLAB's `Output argument 'pu' ... not
assigned`, here `none`. Read from the source, not run.

# CORA's `nonlinearReset/evaluate` stops on a set state with a numeric input

`aux_expansionPoint` tests `isnumeric(x)` where `isnumeric(u)` is meant, so for a set `x` and a
numeric `u` (also the default `u = zeros(m, 1)`) `pu` is never assigned and MATLAB raises `Output
argument 'pu' ... not assigned`; the expansion point is `(center x, u)`. Read from `evaluate.m`
l. 91-95, not run (`references/coverage/hybridDynamics/nonlinearReset.md`, row `evaluate`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- The expansion point `(px, pu)` as the code assigns it, `none` for the unassigned `pu`. -/
def NonlinearReset.expansionPointCora {E : Type} (x u : NonlinearReset.Arg E) :
    Option (E × E) :=
  -- px: the center of a set, the value of a number
  let px : E := match x with | .set c => c | .num v => v
  match u with
  -- isa(u,'contSet')
  | .set c => some (px, c)
  | .num v => match x with
    -- elseif isnumeric(x)
    | .num _ => some (px, v)
    | .set _ => none


-- =======================================  MAIN THEOREM  ======================================= --

/-- A set `x` with center `c` and a numeric `u = v`: CORA gives no expansion point, where the
point `(c, v)` is wanted; with a numeric `x` it gives one. -/
theorem NonlinearReset.expansionPointCora_crash {E : Type} (c v w : E) :
    NonlinearReset.expansionPointCora (.set c) (.num v) = none ∧
      NonlinearReset.expansionPointCora (.num w) (.num v) = some (w, v) := by
  simp [NonlinearReset.expansionPointCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
