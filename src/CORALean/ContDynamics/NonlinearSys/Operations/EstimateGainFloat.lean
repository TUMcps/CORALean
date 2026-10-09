import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGainSearchFloat
import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat

/-!
# `estimateGain`: the gain at the finite horizon, in floats

`estimateGain` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
soundness statement reads it, so every rounding is upward and no theorem is owed. What a run
guarantees holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 16: the gain `φ⁽¹⁾` eq. (56) fixes, at the `λ'` the step
size search settled on. -/
def estimateGainFloat (ζδ lam rabs1 rabsOpt : 𝕋) (scalings fuel : ℕ) : 𝕋 :=
  let target := divUp (mulUp lam rabsOpt) rabs1                  -- 56. the right-hand side
  let lhs := fun φ1 => (List.range scalings).foldl               -- 56. the left-hand side
    (fun p j => mulUp p (interpGainFloat ζδ φ1 j)) one
  estimateGainSearchFloat lhs target zero one fuel               -- 56. solve for φ⁽¹⁾ in [0,1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
