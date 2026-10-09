import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumBoxFloat

/-!
# How far `inputSolutionFloat` reaches beyond the exact input solution

`inputReach_subset_inputSolutionFloat` bounds the float enclosure from below.
This box bounds it from above: it lies in the exact `inputSolution` at `U`'s
nominal zonotope, widened by this box (`inputSolutionFloat_subset_add_box`),
which is what an inner approximation pays for running the input solution in
floats. The Taylor sum pays `inputTaylorSumBoxFloat`; the remainder term
`[E(r)·r] U` is bounded through the zero matrix, a member of its interval, so it
pays its whole `mtimesIntervalMatBox`, and the exact remainder term holds `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `inputSolutionFloat r η U` holds beyond the exact `inputSolution` at `U`'s nominal
zonotope: the Taylor sum's box, the remainder product's whole box, and the last `plusBox`. -/
def LinearSys.inputSolutionBoxFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) (U : Zonotope 𝕋 n) :
    Zonotope 𝕋 n :=
  let S := sys.inputTaylorSumFloat r U η                            -- ⊕ᵢ [Tᵢ] U
  let Rm := MatExp.intervalInputRemainder (Interval.point sys.A) r η   -- [E(r)·r]
  let F := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) Rm U    -- [E(r)·r] U
  (sys.inputTaylorSumBoxFloat r U η ⊞ (Zonotope.mtimesIntervalMatBox Rm U).zonotope) ⊞
    (Zonotope.plusBox S F).zonotope                                 -- S ⊞ F beyond S + F

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
