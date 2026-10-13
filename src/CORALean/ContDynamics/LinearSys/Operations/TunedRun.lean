module

public import CORALean.ContDynamics.LinearSys.Operations.TunedInit
public import CORALean.ContDynamics.LinearSys.Operations.TunedStep

@[expose] public section

/-!
# `Alg. 1` lines 4-11: the loop

`tunedRun`: [1, Alg. 1] lines 4-11, iterate the tuned step while `t < t_f`. Line 4's `while
t < t_f` is no Lean recursion, so the caller supplies the iteration count and a run that has
reached `t_f` stands still.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-11: iterate the tuned step while `t < t_f`. -/
noncomputable def LinearSys.tunedRun (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel : ℕ) :
    ℕ → Option (LinearSys.TunedState n)
  | 0 => some (LinearSys.tunedInit tf μ)                           -- 1.-3. initialize
  | k + 1 =>
    match sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k with
    | none => none
    | some s =>
      if s.t < tf                                                  -- 4. while t < t_f
      then sys.tunedStep le X₀ U εHmax εPmax εSmax tf μ ηmax fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
