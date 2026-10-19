module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloatReachSucc
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemTimePointStepInputFloatError

@[expose] public section

/-!
# The float sampled run keeps the origin in its error box

By induction on the step count: the float step keeps it
(`zero_mem_timePointStepInputFloat_error`), and `reduce` keeps the error box it
is given. What every step's upper bounds ask of their operand, and what makes
the run nonempty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float sampled run keeps `0` in its error box, given `R₀` and `U` do, at `Δt ≥ 0` and
an admissible order. -/
theorem LinearSys.zero_mem_discretizeEnclosureFloat_reach_error (sys : LinearSys 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 ≤ toReal Δt) {η : ℕ} (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec 𝕋 n)} (hR₀ : (0 : Vec ℝ n) ∈ R₀.I_error.construct)
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (k : ℕ) : -- --- CONCL ---
    (0 : Vec ℝ n) ∈ ((sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
      ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).I_error.construct := by -- --- PROOF ---
  induction k with
  | zero => exact hR₀
  | succ k ih =>
    rw [sys.discretizeEnclosureFloat_reach_succ]
    have hW := sys.zero_mem_timePointStepInputFloat_error hΔt hη ih hU
    -- `reduce` keeps the error box it is given
    unfold Zonotope.reduce Zonotope.reduceGirard
    split_ifs with hlt
    · exact hW
    · exact hW

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
