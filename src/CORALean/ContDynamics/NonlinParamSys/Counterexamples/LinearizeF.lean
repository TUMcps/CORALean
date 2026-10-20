module

public import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeF

@[expose] public section

/-!
# `linearizeF` assumes the dynamics are affine in the parameters

CORA builds `parametricDynamicFile` from `f(x, u, 0)` and the unit vectors, and nothing checks
that `f` is affine in `p` (the `try` of `aux_parametric` catches symbolic failures only). For
`ẋ = p²` and the parameter box `[1, 2]` the zonotope `zf` of the constant term is `[1, 2]`, while
`f(x*, u*, 2) = 4` is not in it.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the dynamics value at the parameter lies outside the constant-term zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ẋ = p²` at `p = 2`: the value `4` is outside the zonotope of the constant term. -/
theorem NonlinParamSys.linearize_f_counterexample : -- --- CONCL ---
    let sys : NonlinParamSys 1 1 1 := ⟨fun _ _ p => fun _ => p 0 ^ 2, 1, fun x _ _ => x⟩
    let I : Interval (Vec ℝ 1) := ⟨fun _ => 1, fun _ => 2⟩
    sys.f 0 0 (fun _ => 2) ∉ (sys.linearizeF 0 0 I).construct := by -- --- PROOF ---
  intro sys I
  rintro ⟨β, hβ, h⟩
  -- the coordinate: `4 = 3/2 + β/2`, so `β = 5`
  have h0 := congrFun h 0
  simp [sys, I, NonlinParamSys.linearizeF, Interval.center, Interval.radius] at h0
  have := hβ (0 : Fin 1)
  rw [abs_le] at this
  norm_num at h0
  linarith [this.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
