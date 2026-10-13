import CORALean.ContDynamics.LinearSys.Operations.AdaptiveStepFloat

/-!
# `Alg. 1` lines 4-11 in floats: the loop

[1, Alg. 1]'s `tunedRun` computed in `𝕋`: iterate `adaptiveStepFloat` while `t < t_f`,
collecting each step's report. Line 4's `while` is no Lean recursion, so the
caller bounds the iterations, and a run that has not reached `t_f` within
them is `none` rather than a partial cover.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-11: the reports of the steps from `s` to `t_f`, at most `k` of them. -/
def LinearSys.adaptiveRunFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (t₀ tf : ℚ)
    (options : LinearSys.AdaptiveOptions 𝕋) :
    ℕ → LinearSys.AdaptiveState 𝕋 n → Option (List (LinearSys.AdaptiveStepInfo 𝕋 n))
  | 0, s => if tf ≤ s.t then some [] else none                      -- out of iterations
  | k + 1, s =>
    if tf ≤ s.t then some []                                        -- 4. while t < t_f
    else match sys.adaptiveStepFloat X₀ V t₀ tf options s with
      | none => none
      | some (r, s') => (sys.adaptiveRunFloat X₀ V t₀ tf options k s').map (r :: ·)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
