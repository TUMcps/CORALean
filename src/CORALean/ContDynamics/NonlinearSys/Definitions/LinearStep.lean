module

@[expose] public section

/-!
# Which linear step a nonlinear step runs

The linearized system `δ̇ = A δ + ũ` of a nonlinear step is advanced by one linear step. CORA's
`linReach` calls its linear `oneStep`; CORALean's float version of it is `reachFloatInput`, whose
`[e^{AΔt}]` is the Taylor enclosure of an admissible order. `closedForm` is
`LinearSys.oneStepClosedFormFloat`, CORA's `oneStep` as the closed form it computes: the same sets
for a moderate `AΔt`, and for a stiff `A` a `[e^{AΔt}]` by scaling and squaring, as wide as
rounding and not as wide as `e^{|A|Δt}`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The linear step of a nonlinear step: one step of `LinearSys.reachFloatInput`, or
`LinearSys.oneStepClosedFormFloat`. -/
inductive NonlinearSys.LinearStep where
  | reachFloatInput
  | closedForm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
