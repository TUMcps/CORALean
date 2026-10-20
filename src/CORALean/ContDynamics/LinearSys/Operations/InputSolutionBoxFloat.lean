module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumBoxFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# How far `inputSolutionFloat` reaches beyond the exact input solution

`inputReach_subset_inputSolutionFloat` bounds the float enclosure from below.
This box bounds it from above: it lies in the exact `inputSolution` at `U`'s
nominal zonotope, widened by this box (`inputSolutionFloat_subset_add_box`),
which is what an inner approximation pays for running the input solution in
floats. The Taylor sum pays `inputTaylorSumBoxFloat`; the remainder term
`[E(r)·r] U` is bounded through the zero matrix, a member of its interval, so it
pays its whole `mtimesIntervalMatBox`, and the exact remainder term holds `0`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `U` – float input zonotope

## Output
* float zonotope of how far the float input solution reaches beyond the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `inputSolutionFloat r η U` holds beyond the exact `inputSolution` at `U`'s nominal
zonotope: the Taylor sum's box, the remainder product's whole box, and the last `plusBox`. -/
def LinearSys.inputSolutionBoxFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) (U : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let S := sys.inputTaylorSumFloat r U η                            -- ⊕ᵢ [Tᵢ] U
  let Rm := MatExp.intervalInputRemainder (Interval.point sys.A) r η   -- [E(r)·r]
  let F := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [E(r)·r] U
    (S := 𝒵[𝕋]) Rm U
  (sys.inputTaylorSumBoxFloat r U η ⊞ (Zonotope.mtimesIntervalMatBox Rm U).zonotope) ⊞
    (Zonotope.plusBox S F).zonotope                                 -- S ⊞ F beyond S + F

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
