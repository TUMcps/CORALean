module

public import CORALean.ContDynamics.LinParamSys.LinParamSys

@[expose] public section

/-!
# The input set in state coordinates

The set `V = B*U + c` of CORA's `priv_inputSolution` [1], with `B` the system's matrix set —
CORA's `intervalMatrix` or `matZonotope` times a set — `U` in input coordinates and `c` the
offset as a point. It is the `U'` the canonical form of a run is driven from
(`Trajectory.canonical`); soundness is `Trajectory.mem_inputSet`.

## References

* [1] `contDynamics/@linParamSys/private/priv_inputSolution.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
  [Mtimes 𝕄 S] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B U ⊕ c`, the matrix set times the input set, plus the offset. -/
def LinParamSys.inputSet (sys : LinParamSys 𝕄 n) (U : S sys.m) : S n :=
  Mtimes.mtimes (S := S) sys.B U ⊞ OfPoint.ofPoint sys.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
