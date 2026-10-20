module

public import Mathlib.Logic.Basic

@[expose] public section

/-!
# `NonlinearSys.validateOptionsCora`: validating `options.timeStepInner` always stops

`validateOptions` calls `checkDynParameter` for every field the user gave that the function's
config file lists (`config_nonlinearSys_priv_reachInnerScaling.m` l. 81 lists `timeStepInner` as
`'optional'`), which calls `checkDynParameterOptions(field, ...)`. Its `switch` case
`'timeStepInner'` (l. 172-173) reads
`checks = aux_getChecksOptions_timeStepInner(charecks,sys,func,params,options);`: `charecks` is
no variable and no function (`checks` is meant), so MATLAB stops with `Unrecognized function or
variable 'charecks'` before the checks (a scalar, numeric, `rem(params.tFinal,val)`) are built.
`reachInner` of a `nonlinearSys` with `algInner = 'scale'` (`priv_reachInnerScaling`, l. 45) is the
call that validates `timeStepInner`. A MATLAB error, not a wrong value. Modelled over the names of
the fields the user sets: `none` is the error. Read from the source, not run.

# CORA's `reachInner` fails for every user-set `timeStepInner`

`options.timeStepInner = 0.05` with `tFinal = 1` is a valid value (`rem(1, 0.05) = 0`), and
`reachInner(sys, params, options)` stops in `validateOptions`.

## Inputs
* `fields` – option fields the user gave

## Hypotheses
* `h` – `timeStepInner` is among the fields

## Conclusion
* the validation fails
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `checkDynParameterOptions(field, ...)`: the case `'timeStepInner'` reads the undefined
`charecks` (`none`), every other field builds its checks. -/
def NonlinearSys.checkOptionsFieldCora (field : String) : Option Unit :=
  if field = "timeStepInner" then none else some ()

-- The model: CORA's code as printed, kept only to be refuted.
/-- The loop of `validateOptions` over the fields the user gave. -/
def NonlinearSys.validateOptionsCora : List String → Option Unit
  | [] => some ()
  | f :: fs =>
    (NonlinearSys.checkOptionsFieldCora f).bind fun _ => NonlinearSys.validateOptionsCora fs


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever else is set, `timeStepInner` among the fields makes the validation fail. -/
theorem NonlinearSys.validateOptionsCora_timeStepInner_crash (fields : List String)
    (h : "timeStepInner" ∈ fields) : -- --- CONCL ---
    NonlinearSys.validateOptionsCora fields = none := by -- --- PROOF ---
  induction fields with
  | nil => simp at h
  | cons f fs ih =>
    by_cases hf : f = "timeStepInner"
    · simp [NonlinearSys.validateOptionsCora, NonlinearSys.checkOptionsFieldCora, hf]
    · have hfs : "timeStepInner" ∈ fs := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hf
        · exact h'
      simp [NonlinearSys.validateOptionsCora, NonlinearSys.checkOptionsFieldCora, hf, ih hfs]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
